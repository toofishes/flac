/* libFLAC - Free Lossless Audio Codec library
 * Copyright (C) 2000,2001,2002  Josh Coalson
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Library General Public
 * License as published by the Free Software Foundation; either
 * version 2 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Library General Public License for more details.
 *
 * You should have received a copy of the GNU Library General Public
 * License along with this library; if not, write to the
 * Free Software Foundation, Inc., 59 Temple Place - Suite 330,
 * Boston, MA  02111-1307, USA.
 */

#include <stdlib.h> /* for malloc() */
#include <string.h> /* for memcpy(), memset() */
#include "private/bitbuffer.h"
#include "private/bitmath.h"
#include "private/crc.h"
#include "FLAC/assert.h"

/*
 * Along the way you will see two versions of some functions, selected
 * by a FLAC__NO_MANUAL_INLINING macro.  One is the simplified, more
 * readable, and slow version, and the other is the same function
 * where crucial parts have been manually inlined and are much faster.
 *
 */

/*
 * This should be at least twice as large as the largest number of blurbs
 * required to represent any 'number' (in any encoding) you are going to
 * read.  With FLAC this is on the order of maybe a few hundred bits.
 * If the buffer is smaller than that, the decoder won't be able to read
 * in a whole number that is in a variable length encoding (e.g. Rice).
 *
 * The number we are actually using here is based on what would be the
 * approximate maximum size of a verbatim frame at the default block size,
 * for CD audio (4096 sample * 4 bytes per sample), plus some wiggle room.
 * 32kbytes sounds reasonable.  For kicks we subtract out 64 bytes for any
 * alignment or malloc overhead.
 *
 * Increase this number to decrease the number of read callbacks, at the
 * expense of using more memory.  Or decrease for the reverse effect,
 * keeping in mind the limit from the first paragraph.
 */
static const unsigned FLAC__BITBUFFER_DEFAULT_CAPACITY = ((65536 - 64) * 8) / FLAC__BITS_PER_BLURB; /* blurbs */

#if FLAC__BITS_PER_BLURB == 8
#define FLAC__BITS_PER_BLURB_LOG2 3
#define FLAC__BYTES_PER_BLURB 1
#define FLAC__BLURB_ALL_ONES ((FLAC__byte)0xff)
#define FLAC__BLURB_TOP_BIT_ONE ((FLAC__byte)0x80)
#define BLURB_BIT_TO_MASK(b) (((FLAC__blurb)'\x80') >> (b))
#define CRC16_UPDATE_BLURB(bb, blurb, crc) FLAC__CRC16_UPDATE((blurb), (crc));
#elif FLAC__BITS_PER_BLURB == 32
#define FLAC__BITS_PER_BLURB_LOG2 5
#define FLAC__BYTES_PER_BLURB 4
#define FLAC__BLURB_ALL_ONES ((FLAC__uint32)0xffffffff)
#define FLAC__BLURB_TOP_BIT_ONE ((FLAC__uint32)0x80000000)
#define BLURB_BIT_TO_MASK(b) (((FLAC__blurb)0x80000000) >> (b))
#define CRC16_UPDATE_BLURB(bb, blurb, crc) crc16_update_blurb((bb), (blurb));
#else
/* ERROR, only sizes of 8 and 32 are supported */
#endif

#define FLAC__BLURBS_TO_BITS(blurbs) ((blurbs) << FLAC__BITS_PER_BLURB_LOG2)

#ifdef min
#undef min
#endif
#define min(x,y) ((x)<(y)?(x):(y))
#ifdef max
#undef max
#endif
#define max(x,y) ((x)>(y)?(x):(y))

#ifndef FLaC__INLINE
#define FLaC__INLINE
#endif

struct FLAC__BitBuffer {
	FLAC__blurb *buffer;
	unsigned capacity; /* in blurbs */
	unsigned blurbs, bits;
	unsigned total_bits; /* must always == FLAC__BITS_PER_BLURB*blurbs+bits */
	unsigned consumed_blurbs, consumed_bits;
	unsigned total_consumed_bits; /* must always == FLAC__BITS_PER_BLURB*consumed_blurbs+consumed_bits */
	FLAC__uint16 read_crc16;
#if FLAC__BITS_PER_BLURB == 32
	unsigned crc16_align;
#endif
	FLAC__blurb save_head, save_tail;
};

static void crc16_update_blurb(FLAC__BitBuffer *bb, FLAC__blurb blurb)
{
#if FLAC__BITS_PER_BLURB == 32
	if(bb->crc16_align == 0) {
		FLAC__CRC16_UPDATE(blurb >> 24, bb->read_crc16);
		FLAC__CRC16_UPDATE((blurb >> 16) & 0xff, bb->read_crc16);
		FLAC__CRC16_UPDATE((blurb >> 8) & 0xff, bb->read_crc16);
		FLAC__CRC16_UPDATE(blurb & 0xff, bb->read_crc16);
	}
	else if(bb->crc16_align == 8) {
		FLAC__CRC16_UPDATE((blurb >> 16) & 0xff, bb->read_crc16);
		FLAC__CRC16_UPDATE((blurb >> 8) & 0xff, bb->read_crc16);
		FLAC__CRC16_UPDATE(blurb & 0xff, bb->read_crc16);
	}
	else if(bb->crc16_align == 16) {
		FLAC__CRC16_UPDATE((blurb >> 8) & 0xff, bb->read_crc16);
		FLAC__CRC16_UPDATE(blurb & 0xff, bb->read_crc16);
	}
	else if(bb->crc16_align == 24) {
		FLAC__CRC16_UPDATE(blurb & 0xff, bb->read_crc16);
	}
	bb->crc16_align = 0;
#else
	(void)bb; (void)blurb;
	FLAC__ASSERT(false);
#endif
}

/*
 * WATCHOUT: The current implentation is not friendly to shrinking, i.e. it
 * does not shift left what is consumed, it just chops off the end, whether
 * there is unconsumed data there or not.  This is OK because currently we
 * never shrink the buffer, but if this ever changes, we'll have to do some
 * fixups here.
 */
static FLAC__bool bitbuffer_resize_(FLAC__BitBuffer *bb, unsigned new_capacity)
{
	FLAC__blurb *new_buffer;

	FLAC__ASSERT(bb != 0);
	FLAC__ASSERT(bb->buffer != 0);

	if(bb->capacity == new_capacity)
		return true;

	new_buffer = (FLAC__blurb*)malloc(sizeof(FLAC__blurb) * new_capacity);
	if(new_buffer == 0)
		return false;
	memset(new_buffer, 0, sizeof(FLAC__blurb) * new_capacity);
	memcpy(new_buffer, bb->buffer, sizeof(FLAC__blurb)*min(bb->blurbs+(bb->bits?1:0), new_capacity));
	if(new_capacity < bb->blurbs+(bb->bits?1:0)) {
		bb->blurbs = new_capacity;
		bb->bits = 0;
		bb->total_bits = FLAC__BLURBS_TO_BITS(new_capacity);
	}
	if(new_capacity < bb->consumed_blurbs+(bb->consumed_bits?1:0)) {
		bb->consumed_blurbs = new_capacity;
		bb->consumed_bits = 0;
		bb->total_consumed_bits = FLAC__BLURBS_TO_BITS(new_capacity);
	}
	free(bb->buffer); // we've already asserted above that (bb->buffer != 0)
	bb->buffer = new_buffer;
	bb->capacity = new_capacity;
	return true;
}

static FLAC__bool bitbuffer_grow_(FLAC__BitBuffer *bb, unsigned min_blurbs_to_add)
{
	unsigned new_capacity;

	FLAC__ASSERT(min_blurbs_to_add > 0);

	new_capacity = max(bb->capacity * 2, bb->capacity + min_blurbs_to_add);
	return bitbuffer_resize_(bb, new_capacity);
}

static FLAC__bool bitbuffer_ensure_size_(FLAC__BitBuffer *bb, unsigned bits_to_add)
{
	FLAC__ASSERT(bb != 0);
	FLAC__ASSERT(bb->buffer != 0);

	if(FLAC__BLURBS_TO_BITS(bb->capacity) < bb->total_bits + bits_to_add)
		return bitbuffer_grow_(bb, (bits_to_add >> FLAC__BITS_PER_BLURB_LOG2) + 2);
	else
		return true;
}

static FLAC__bool bitbuffer_read_from_client_(FLAC__BitBuffer *bb, FLAC__bool (*read_callback)(FLAC__byte buffer[], unsigned *bytes, void *client_data), void *client_data)
{
	unsigned bytes;
	FLAC__byte *target;

	/* first shift the unconsumed buffer data toward the front as much as possible */
	if(bb->total_consumed_bits >= FLAC__BITS_PER_BLURB) {
		unsigned l = 0, r = bb->consumed_blurbs, r_end = bb->blurbs + (bb->bits? 1:0);
		for( ; r < r_end; l++, r++)
			bb->buffer[l] = bb->buffer[r];
		for( ; l < r_end; l++)
			bb->buffer[l] = 0;
		bb->blurbs -= bb->consumed_blurbs;
		bb->total_bits -= FLAC__BLURBS_TO_BITS(bb->consumed_blurbs);
		bb->consumed_blurbs = 0;
		bb->total_consumed_bits = bb->consumed_bits;
	}

	/* grow if we need to */
	if(bb->capacity <= 1) {
		if(!bitbuffer_resize_(bb, 16))
			return false;
	}

	/* set the target for reading, taking into account blurb alignment */
#if FLAC__BITS_PER_BLURB == 8
	/* blurb == byte, so no gyrations necessary: */
	target = bb->buffer + bb->blurbs;
	bytes = bb->capacity - bb->blurbs;
#elif FLAC__BITS_PER_BLURB == 32
	/* @@@ WATCHOUT: code currently only works for big-endian: */
	FLAC__ASSERT((bb->bits & 7) == 0);
	target = (FLAC__byte*)(bb->buffer + bb->blurbs) + (bb->bits >> 3);
	bytes = ((bb->capacity - bb->blurbs) << 2) - (bb->bits >> 3); /* i.e. (bb->capacity - bb->blurbs) * FLAC__BYTES_PER_BLURB - (bb->bits / 8) */
#else
	FLAC__ASSERT(false); /* ERROR, only sizes of 8 and 32 are supported */
#endif

	/* finally, read in some data */
	if(!read_callback(target, &bytes, client_data))
		return false;

	/* now we have to handle partial blurb cases: */
#if FLAC__BITS_PER_BLURB == 8
	/* blurb == byte, so no gyrations necessary: */
	bb->blurbs += bytes;
	bb->total_bits += FLAC__BLURBS_TO_BITS(bytes);
#elif FLAC__BITS_PER_BLURB == 32
	/* @@@ WATCHOUT: code currently only works for big-endian: */
	{
		const unsigned aligned_bytes = (bb->bits >> 3) + bytes;
		bb->blurbs += (aligned_bytes >> 2); /* i.e. aligned_bytes / FLAC__BYTES_PER_BLURB */
		bb->bits = (aligned_bytes & 3u) << 3; /* i.e. (aligned_bytes % FLAC__BYTES_PER_BLURB) * 8 */
		bb->total_bits += (bytes << 3);
	}
#else
	FLAC__ASSERT(false); /* ERROR, only sizes of 8 and 32 are supported */
#endif
	return true;
}

/***********************************************************************
 *
 * Class constructor/destructor
 *
 ***********************************************************************/

FLAC__BitBuffer *FLAC__bitbuffer_new()
{
	return (FLAC__BitBuffer*)malloc(sizeof(FLAC__BitBuffer));
}

void FLAC__bitbuffer_delete(FLAC__BitBuffer *bb)
{
	FLAC__ASSERT(bb != 0);

	FLAC__bitbuffer_free(bb);
	free(bb);
}

/***********************************************************************
 *
 * Public class methods
 *
 ***********************************************************************/

FLAC__bool FLAC__bitbuffer_init(FLAC__BitBuffer *bb)
{
	FLAC__ASSERT(bb != 0);

	bb->buffer = 0;
	bb->capacity = 0;
	bb->blurbs = bb->bits = bb->total_bits = 0;
	bb->consumed_blurbs = bb->consumed_bits = bb->total_consumed_bits = 0;

	return FLAC__bitbuffer_clear(bb);
}

FLAC__bool FLAC__bitbuffer_init_from(FLAC__BitBuffer *bb, const FLAC__byte buffer[], unsigned bytes)
{
	FLAC__ASSERT(bb != 0);
	FLAC__ASSERT(bytes > 0);

	if(!FLAC__bitbuffer_init(bb))
		return false;

	if(!bitbuffer_ensure_size_(bb, bytes << 3))
		return false;

	FLAC__ASSERT(buffer != 0);
	/* @@@ WATCHOUT: code currently only works for 8-bits-per-blurb inclusive-or big-endian: */
	memcpy((FLAC__byte*)bb->buffer, buffer, sizeof(FLAC__byte)*bytes);
	bb->blurbs = bytes / FLAC__BYTES_PER_BLURB;
	bb->bits = (bytes % FLAC__BYTES_PER_BLURB) << 3;
	bb->total_bits = bytes << 3;
	return true;
}

FLAC__bool FLAC__bitbuffer_concatenate_aligned(FLAC__BitBuffer *dest, const FLAC__BitBuffer *src)
{
	unsigned bits_to_add = src->total_bits - src->total_consumed_bits;

	FLAC__ASSERT(dest != 0);
	FLAC__ASSERT(src != 0);

	if(bits_to_add == 0)
		return true;
	if(dest->bits != src->consumed_bits)
		return false;
	if(!bitbuffer_ensure_size_(dest, bits_to_add))
		return false;
	if(dest->bits == 0) {
		memcpy(dest->buffer+dest->blurbs, src->buffer+src->consumed_blurbs, sizeof(FLAC__blurb)*(src->blurbs-src->consumed_blurbs + ((src->bits)? 1:0)));
	}
	else if(dest->bits + bits_to_add > FLAC__BITS_PER_BLURB) {
		dest->buffer[dest->blurbs] <<= (FLAC__BITS_PER_BLURB - dest->bits);
		dest->buffer[dest->blurbs] |= (src->buffer[src->consumed_blurbs] & ((1u << (FLAC__BITS_PER_BLURB-dest->bits)) - 1));
		memcpy(dest->buffer+dest->blurbs+1, src->buffer+src->consumed_blurbs+1, sizeof(FLAC__blurb)*(src->blurbs-src->consumed_blurbs-1 + ((src->bits)? 1:0)));
	}
	else {
		dest->buffer[dest->blurbs] <<= bits_to_add;
		dest->buffer[dest->blurbs] |= (src->buffer[src->consumed_blurbs] & ((1u << bits_to_add) - 1));
	}
	dest->bits = src->bits;
	dest->total_bits += bits_to_add;
	dest->blurbs = dest->total_bits / FLAC__BITS_PER_BLURB;

	return true;
}

void FLAC__bitbuffer_free(FLAC__BitBuffer *bb)
{
	FLAC__ASSERT(bb != 0);

	if(bb->buffer != 0)
		free(bb->buffer);
	bb->buffer = 0;
	bb->capacity = 0;
	bb->blurbs = bb->bits = bb->total_bits = 0;
	bb->consumed_blurbs = bb->consumed_bits = bb->total_consumed_bits = 0;
}

FLAC__bool FLAC__bitbuffer_clear(FLAC__BitBuffer *bb)
{
	if(bb->buffer == 0) {
		bb->capacity = FLAC__BITBUFFER_DEFAULT_CAPACITY;
		bb->buffer = (FLAC__blurb*)malloc(sizeof(FLAC__blurb) * bb->capacity);
		if(bb->buffer == 0)
			return false;
		memset(bb->buffer, 0, bb->capacity);
	}
	else {
		memset(bb->buffer, 0, bb->blurbs + (bb->bits?1:0));
	}
	bb->blurbs = bb->bits = bb->total_bits = 0;
	bb->consumed_blurbs = bb->consumed_bits = bb->total_consumed_bits = 0;
	return true;
}

FLAC__bool FLAC__bitbuffer_clone(FLAC__BitBuffer *dest, const FLAC__BitBuffer *src)
{
	FLAC__ASSERT(dest != 0);
	FLAC__ASSERT(dest->buffer != 0);
	FLAC__ASSERT(src != 0);
	FLAC__ASSERT(src->buffer != 0);

	if(dest->capacity < src->capacity)
		if(!bitbuffer_resize_(dest, src->capacity))
			return false;
	memcpy(dest->buffer, src->buffer, sizeof(FLAC__blurb)*min(src->capacity, src->blurbs+1));
	dest->blurbs = src->blurbs;
	dest->bits = src->bits;
	dest->total_bits = src->total_bits;
	dest->consumed_blurbs = src->consumed_blurbs;
	dest->consumed_bits = src->consumed_bits;
	dest->total_consumed_bits = src->total_consumed_bits;
	dest->read_crc16 = src->read_crc16;
	return true;
}

void FLAC__bitbuffer_reset_read_crc16(FLAC__BitBuffer *bb, FLAC__uint16 seed)
{
	FLAC__ASSERT(bb != 0);
	FLAC__ASSERT(bb->buffer != 0);
	FLAC__ASSERT((bb->consumed_bits & 7) == 0);

	bb->read_crc16 = seed;
#if FLAC__BITS_PER_BLURB == 8
	/* no need to do anything */
#elif FLAC__BITS_PER_BLURB == 32
	bb->crc16_align = bb->consumed_bits;
#else
	FLAC__ASSERT(false); /* ERROR, only sizes of 8 and 32 are supported */
#endif
}

FLAC__uint16 FLAC__bitbuffer_get_read_crc16(FLAC__BitBuffer *bb)
{
	FLAC__ASSERT(bb != 0);
	FLAC__ASSERT(bb->buffer != 0);
	FLAC__ASSERT((bb->bits & 7) == 0);
	FLAC__ASSERT((bb->consumed_bits & 7) == 0);

#if FLAC__BITS_PER_BLURB == 8
	/* no need to do anything */
#elif FLAC__BITS_PER_BLURB == 32
	/*@@@ BUG: even though this probably can't happen with FLAC, need to fix the case where we are called here for the very first blurb and crc16_align is > 0 */
	if(bb->bits == 0 || bb->consumed_blurbs < bb->blurbs) {
		if(bb->consumed_bits == 8) {
			const FLAC__blurb blurb = bb->buffer[bb->consumed_blurbs];
			FLAC__CRC16_UPDATE(blurb >> 24, bb->read_crc16);
		}
		else if(bb->consumed_bits == 16) {
			const FLAC__blurb blurb = bb->buffer[bb->consumed_blurbs];
			FLAC__CRC16_UPDATE(blurb >> 24, bb->read_crc16);
			FLAC__CRC16_UPDATE((blurb >> 16) & 0xff, bb->read_crc16);
		}
		else if(bb->consumed_bits == 24) {
			const FLAC__blurb blurb = bb->buffer[bb->consumed_blurbs];
			FLAC__CRC16_UPDATE(blurb >> 24, bb->read_crc16);
			FLAC__CRC16_UPDATE((blurb >> 16) & 0xff, bb->read_crc16);
			FLAC__CRC16_UPDATE((blurb >> 8) & 0xff, bb->read_crc16);
		}
	}
	else {
		if(bb->consumed_bits == 8) {
			const FLAC__blurb blurb = bb->buffer[bb->consumed_blurbs];
			FLAC__CRC16_UPDATE(blurb >> (bb->bits-8), bb->read_crc16);
		}
		else if(bb->consumed_bits == 16) {
			const FLAC__blurb blurb = bb->buffer[bb->consumed_blurbs];
			FLAC__CRC16_UPDATE(blurb >> (bb->bits-8), bb->read_crc16);
			FLAC__CRC16_UPDATE((blurb >> (bb->bits-16)) & 0xff, bb->read_crc16);
		}
		else if(bb->consumed_bits == 24) {
			const FLAC__blurb blurb = bb->buffer[bb->consumed_blurbs];
			FLAC__CRC16_UPDATE(blurb >> (bb->bits-8), bb->read_crc16);
			FLAC__CRC16_UPDATE((blurb >> (bb->bits-16)) & 0xff, bb->read_crc16);
			FLAC__CRC16_UPDATE((blurb >> (bb->bits-24)) & 0xff, bb->read_crc16);
		}
	}
	bb->crc16_align = bb->consumed_bits;
#else
	FLAC__ASSERT(false); /* ERROR, only sizes of 8 and 32 are supported */
#endif
	return bb->read_crc16;
}

FLAC__uint16 FLAC__bitbuffer_get_write_crc16(const FLAC__BitBuffer *bb)
{
	FLAC__ASSERT((bb->bits & 7) == 0); /* assert that we're byte-aligned */

#if FLAC__BITS_PER_BLURB == 8
	return FLAC__crc16(bb->buffer, bb->blurbs);
#elif FLAC__BITS_PER_BLURB == 32
	/* @@@ WATCHOUT: code currently only works for big-endian: */
	return FLAC__crc16((FLAC__byte*)(bb->buffer), (bb->blurbs * FLAC__BYTES_PER_BLURB) + (bb->bits >> 3));
#else
	FLAC__ASSERT(false); /* ERROR, only sizes of 8 and 32 are supported */
#endif
}

FLAC__byte FLAC__bitbuffer_get_write_crc8(const FLAC__BitBuffer *bb)
{
	FLAC__ASSERT(bb->blurbs == 0);
	FLAC__ASSERT(bb->buffer[0] == 0xff); /* MAGIC NUMBER for the first byte of the sync code */
	FLAC__ASSERT((bb->bits & 7) == 0); /* assert that we're byte-aligned */
#if FLAC__BITS_PER_BLURB == 8
	return FLAC__crc8(bb->buffer, bb->blurbs);
#elif FLAC__BITS_PER_BLURB == 32
	/* @@@ WATCHOUT: code currently only works for big-endian: */
	return FLAC__crc8((FLAC__byte*)(bb->buffer), (bb->blurbs * FLAC__BYTES_PER_BLURB) + (bb->bits >> 3));
#else
	FLAC__ASSERT(false); /* ERROR, only sizes of 8 and 32 are supported */
#endif
}

FLAC__bool FLAC__bitbuffer_is_byte_aligned(const FLAC__BitBuffer *bb)
{
	return ((bb->bits & 7) == 0);
}

FLAC__bool FLAC__bitbuffer_is_consumed_byte_aligned(const FLAC__BitBuffer *bb)
{
	return ((bb->consumed_bits & 7) == 0);
}

unsigned FLAC__bitbuffer_bits_left_for_byte_alignment(const FLAC__BitBuffer *bb)
{
	return 8 - (bb->consumed_bits & 7);
}

unsigned FLAC__bitbuffer_get_input_bytes_unconsumed(const FLAC__BitBuffer *bb)
{
	FLAC__ASSERT((bb->consumed_bits & 7) == 0 && (bb->bits & 7) == 0);
	return (bb->total_bits - bb->total_consumed_bits) >> 3;
}

void FLAC__bitbuffer_get_buffer(FLAC__BitBuffer *bb, const FLAC__byte **buffer, unsigned *bytes)
{
	FLAC__ASSERT((bb->consumed_bits & 7) == 0 && (bb->bits & 7) == 0);
#if FLAC__BITS_PER_BLURB == 8
	*buffer = bb->buffer + bb->consumed_blurbs;
	*bytes = bb->blurbs - bb->consumed_blurbs;
#elif FLAC__BITS_PER_BLURB == 32
	/* @@@ WATCHOUT: code currently only works for big-endian: */
	*buffer = (FLAC__byte*)(bb->buffer + bb->consumed_blurbs) + (bb->consumed_bits >> 3);
	*bytes = (bb->total_bits - bb->total_consumed_bits) >> 3;
#else
	FLAC__ASSERT(false); /* ERROR, only sizes of 8 and 32 are supported */
#endif
}

void FLAC__bitbuffer_release_buffer(FLAC__BitBuffer *bb)
{
#if FLAC__BITS_PER_BLURB == 8
	(void)bb;
#elif FLAC__BITS_PER_BLURB == 32
	/* @@@ WATCHOUT: code currently only works for big-endian: */
	(void)bb;
#else
	FLAC__ASSERT(false); /* ERROR, only sizes of 8 and 32 are supported */
#endif
}

FLAC__bool FLAC__bitbuffer_write_zeroes(FLAC__BitBuffer *bb, unsigned bits)
{
	unsigned n;

	FLAC__ASSERT(bb != 0);
	FLAC__ASSERT(bb->buffer != 0);

	if(bits == 0)
		return true;
	if(!bitbuffer_ensure_size_(bb, bits))
		return false;
	bb->total_bits += bits;
	while(bits > 0) {
		n = min(FLAC__BITS_PER_BLURB - bb->bits, bits);
		bb->buffer[bb->blurbs] <<= n;
		bits -= n;
		bb->bits += n;
		if(bb->bits == FLAC__BITS_PER_BLURB) {
			bb->blurbs++;
			bb->bits = 0;
		}
	}
	return true;
}

FLaC__INLINE FLAC__bool FLAC__bitbuffer_write_raw_uint32(FLAC__BitBuffer *bb, FLAC__uint32 val, unsigned bits)
{
	unsigned n, k;

	FLAC__ASSERT(bb != 0);
	FLAC__ASSERT(bb->buffer != 0);

	FLAC__ASSERT(bits <= 32);
	if(bits == 0)
		return true;
	/* inline the size check so we don't incure a function call unnecessarily */
	if(FLAC__BLURBS_TO_BITS(bb->capacity) < bb->total_bits + bits) {
		if(!bitbuffer_ensure_size_(bb, bits))
			return false;
	}
	if(bits < 32) /* @@@ gcc seems to require this because the following line causes incorrect results when bits==32; investigate */
		val &= (~(0xffffffff << bits)); /* zero-out unused bits */
	bb->total_bits += bits;
	while(bits > 0) {
		n = FLAC__BITS_PER_BLURB - bb->bits;
		if(n == FLAC__BITS_PER_BLURB) { /* i.e. bb->bits == 0 */
			if(bits < FLAC__BITS_PER_BLURB) {
				bb->buffer[bb->blurbs] = (FLAC__blurb)val;
				bb->bits = bits;
				break;
			}
			else if(bits == FLAC__BITS_PER_BLURB) {
				bb->buffer[bb->blurbs++] = (FLAC__blurb)val;
				break;
			}
			else {
				k = bits - FLAC__BITS_PER_BLURB;
				bb->buffer[bb->blurbs++] = (FLAC__blurb)(val >> k);
				/* we know k < 32 so no need to protect against the gcc bug mentioned above */
				val &= (~(0xffffffff << k));
				bits -= FLAC__BITS_PER_BLURB;
			}
		}
		else if(bits <= n) {
			bb->buffer[bb->blurbs] <<= bits;
			bb->buffer[bb->blurbs] |= val;
			if(bits == n) {
				bb->blurbs++;
				bb->bits = 0;
			}
			else
				bb->bits += bits;
			break;
		}
		else {
			k = bits - n;
			bb->buffer[bb->blurbs] <<= n;
			bb->buffer[bb->blurbs] |= (val >> k);
			/* we know n > 0 so k < 32 so no need to protect against the gcc bug mentioned above */
			val &= (~(0xffffffff << k));
			bits -= n;
			bb->blurbs++;
			bb->bits = 0;
		}
	}

	return true;
}

FLAC__bool FLAC__bitbuffer_write_raw_int32(FLAC__BitBuffer *bb, FLAC__int32 val, unsigned bits)
{
	return FLAC__bitbuffer_write_raw_uint32(bb, (FLAC__uint32)val, bits);
}

FLAC__bool FLAC__bitbuffer_write_raw_uint64(FLAC__BitBuffer *bb, FLAC__uint64 val, unsigned bits)
{
	static const FLAC__uint64 mask[] = {
		0,
		0x0000000000000001, 0x0000000000000003, 0x0000000000000007, 0x000000000000000F,
		0x000000000000001F, 0x000000000000003F, 0x000000000000007F, 0x00000000000000FF,
		0x00000000000001FF, 0x00000000000003FF, 0x00000000000007FF, 0x0000000000000FFF,
		0x0000000000001FFF, 0x0000000000003FFF, 0x0000000000007FFF, 0x000000000000FFFF,
		0x000000000001FFFF, 0x000000000003FFFF, 0x000000000007FFFF, 0x00000000000FFFFF,
		0x00000000001FFFFF, 0x00000000003FFFFF, 0x00000000007FFFFF, 0x0000000000FFFFFF,
		0x0000000001FFFFFF, 0x0000000003FFFFFF, 0x0000000007FFFFFF, 0x000000000FFFFFFF,
		0x000000001FFFFFFF, 0x000000003FFFFFFF, 0x000000007FFFFFFF, 0x00000000FFFFFFFF,
		0x00000001FFFFFFFF, 0x00000003FFFFFFFF, 0x00000007FFFFFFFF, 0x0000000FFFFFFFFF,
		0x0000001FFFFFFFFF, 0x0000003FFFFFFFFF, 0x0000007FFFFFFFFF, 0x000000FFFFFFFFFF,
		0x000001FFFFFFFFFF, 0x000003FFFFFFFFFF, 0x000007FFFFFFFFFF, 0x00000FFFFFFFFFFF,
		0x00001FFFFFFFFFFF, 0x00003FFFFFFFFFFF, 0x00007FFFFFFFFFFF, 0x0000FFFFFFFFFFFF,
		0x0001FFFFFFFFFFFF, 0x0003FFFFFFFFFFFF, 0x0007FFFFFFFFFFFF, 0x000FFFFFFFFFFFFF,
		0x001FFFFFFFFFFFFF, 0x003FFFFFFFFFFFFF, 0x007FFFFFFFFFFFFF, 0x00FFFFFFFFFFFFFF,
		0x01FFFFFFFFFFFFFF, 0x03FFFFFFFFFFFFFF, 0x07FFFFFFFFFFFFFF, 0x0FFFFFFFFFFFFFFF,
		0x1FFFFFFFFFFFFFFF, 0x3FFFFFFFFFFFFFFF, 0x7FFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF
	};
	unsigned n, k;

	FLAC__ASSERT(bb != 0);
	FLAC__ASSERT(bb->buffer != 0);

	FLAC__ASSERT(bits <= 64);
	if(bits == 0)
		return true;
	if(!bitbuffer_ensure_size_(bb, bits))
		return false;
	val &= mask[bits];
	bb->total_bits += bits;
	while(bits > 0) {
		if(bb->bits == 0) {
			if(bits < FLAC__BITS_PER_BLURB) {
				bb->buffer[bb->blurbs] = (FLAC__blurb)val;
				bb->bits = bits;
				break;
			}
			else if(bits == FLAC__BITS_PER_BLURB) {
				bb->buffer[bb->blurbs++] = (FLAC__blurb)val;
				break;
			}
			else {
				k = bits - FLAC__BITS_PER_BLURB;
				bb->buffer[bb->blurbs++] = (FLAC__blurb)(val >> k);
				/* we know k < 64 so no need to protect against the gcc bug mentioned above */
				val &= (~(0xffffffffffffffff << k));
				bits -= FLAC__BITS_PER_BLURB;
			}
		}
		else {
			n = min(FLAC__BITS_PER_BLURB - bb->bits, bits);
			k = bits - n;
			bb->buffer[bb->blurbs] <<= n;
			bb->buffer[bb->blurbs] |= (val >> k);
			/* we know n > 0 so k < 64 so no need to protect against the gcc bug mentioned above */
			val &= (~(0xffffffffffffffff << k));
			bits -= n;
			bb->bits += n;
			if(bb->bits == FLAC__BITS_PER_BLURB) {
				bb->blurbs++;
				bb->bits = 0;
			}
		}
	}

	return true;
}

FLAC__bool FLAC__bitbuffer_write_raw_int64(FLAC__BitBuffer *bb, FLAC__int64 val, unsigned bits)
{
	return FLAC__bitbuffer_write_raw_uint64(bb, (FLAC__uint64)val, bits);
}

FLAC__bool FLAC__bitbuffer_write_unary_unsigned(FLAC__BitBuffer *bb, unsigned val)
{
	if(val < 32)
		return FLAC__bitbuffer_write_raw_uint32(bb, 1, ++val);
	else if(val < 64)
		return FLAC__bitbuffer_write_raw_uint64(bb, 1, ++val);
	else {
		if(!FLAC__bitbuffer_write_zeroes(bb, val))
			return false;
		return FLAC__bitbuffer_write_raw_uint32(bb, 1, 1);
	}
}

unsigned FLAC__bitbuffer_rice_bits(int val, unsigned parameter)
{
	unsigned msbs, uval;

	/* fold signed to unsigned */
	if(val < 0)
		/* equivalent to
		 *     (unsigned)(((--val) << 1) - 1);
		 * but without the overflow problem at MININT
		 */
		uval = (unsigned)(((-(++val)) << 1) + 1);
	else
		uval = (unsigned)(val << 1);

	msbs = uval >> parameter;

	return 1 + parameter + msbs;
}

#if 0 /* UNUSED */
unsigned FLAC__bitbuffer_golomb_bits_signed(int val, unsigned parameter)
{
	unsigned bits, msbs, uval;
	unsigned k;

	FLAC__ASSERT(parameter > 0);

	/* fold signed to unsigned */
	if(val < 0)
		/* equivalent to
		 *     (unsigned)(((--val) << 1) - 1);
		 * but without the overflow problem at MININT
		 */
		uval = (unsigned)(((-(++val)) << 1) + 1);
	else
		uval = (unsigned)(val << 1);

	k = FLAC__bitmath_ilog2(parameter);
	if(parameter == 1u<<k) {
		FLAC__ASSERT(k <= 30);

		msbs = uval >> k;
		bits = 1 + k + msbs;
	}
	else {
		unsigned q, r, d;

		d = (1 << (k+1)) - parameter;
		q = uval / parameter;
		r = uval - (q * parameter);

		bits = 1 + q + k;
		if(r >= d)
			bits++;
	}
	return bits;
}

unsigned FLAC__bitbuffer_golomb_bits_unsigned(unsigned uval, unsigned parameter)
{
	unsigned bits, msbs;
	unsigned k;

	FLAC__ASSERT(parameter > 0);

	k = FLAC__bitmath_ilog2(parameter);
	if(parameter == 1u<<k) {
		FLAC__ASSERT(k <= 30);

		msbs = uval >> k;
		bits = 1 + k + msbs;
	}
	else {
		unsigned q, r, d;

		d = (1 << (k+1)) - parameter;
		q = uval / parameter;
		r = uval - (q * parameter);

		bits = 1 + q + k;
		if(r >= d)
			bits++;
	}
	return bits;
}
#endif /* UNUSED */

#ifdef FLAC__SYMMETRIC_RICE
FLAC__bool FLAC__bitbuffer_write_symmetric_rice_signed(FLAC__BitBuffer *bb, int val, unsigned parameter)
{
	unsigned total_bits, interesting_bits, msbs;
	FLAC__uint32 pattern;

	FLAC__ASSERT(bb != 0);
	FLAC__ASSERT(bb->buffer != 0);
	FLAC__ASSERT(parameter <= 31);

	/* init pattern with the unary end bit and the sign bit */
	if(val < 0) {
		pattern = 3;
		val = -val;
	}
	else
		pattern = 2;

	msbs = val >> parameter;
	interesting_bits = 2 + parameter;
	total_bits = interesting_bits + msbs;
	pattern <<= parameter;
	pattern |= (val & ((1<<parameter)-1)); /* the binary LSBs */

	if(total_bits <= 32) {
		if(!FLAC__bitbuffer_write_raw_uint32(bb, pattern, total_bits))
			return false;
	}
	else {
		/* write the unary MSBs */
		if(!FLAC__bitbuffer_write_zeroes(bb, msbs))
			return false;
		/* write the unary end bit, the sign bit, and binary LSBs */
		if(!FLAC__bitbuffer_write_raw_uint32(bb, pattern, interesting_bits))
			return false;
	}
	return true;
}

#if 0 /* UNUSED */
FLAC__bool FLAC__bitbuffer_write_symmetric_rice_signed_guarded(FLAC__BitBuffer *bb, int val, unsigned parameter, unsigned max_bits, FLAC__bool *overflow)
{
	unsigned total_bits, interesting_bits, msbs;
	FLAC__uint32 pattern;

	FLAC__ASSERT(bb != 0);
	FLAC__ASSERT(bb->buffer != 0);
	FLAC__ASSERT(parameter <= 31);

	*overflow = false;

	/* init pattern with the unary end bit and the sign bit */
	if(val < 0) {
		pattern = 3;
		val = -val;
	}
	else
		pattern = 2;

	msbs = val >> parameter;
	interesting_bits = 2 + parameter;
	total_bits = interesting_bits + msbs;
	pattern <<= parameter;
	pattern |= (val & ((1<<parameter)-1)); /* the binary LSBs */

	if(total_bits <= 32) {
		if(!FLAC__bitbuffer_write_raw_uint32(bb, pattern, total_bits))
			return false;
	}
	else if(total_bits > max_bits) {
		*overflow = true;
		return true;
	}
	else {
		/* write the unary MSBs */
		if(!FLAC__bitbuffer_write_zeroes(bb, msbs))
			return false;
		/* write the unary end bit, the sign bit, and binary LSBs */
		if(!FLAC__bitbuffer_write_raw_uint32(bb, pattern, interesting_bits))
			return false;
	}
	return true;
}
#endif /* UNUSED */

FLAC__bool FLAC__bitbuffer_write_symmetric_rice_signed_escape(FLAC__BitBuffer *bb, int val, unsigned parameter)
{
	unsigned total_bits, val_bits;
	FLAC__uint32 pattern;

	FLAC__ASSERT(bb != 0);
	FLAC__ASSERT(bb->buffer != 0);
	FLAC__ASSERT(parameter <= 31);

	val_bits = FLAC__bitmath_silog2(val);
	total_bits = 2 + parameter + 5 + val_bits;

	if(total_bits <= 32) {
		pattern = 3;
		pattern <<= (parameter + 5);
		pattern |= val_bits;
		pattern <<= val_bits;
		pattern |= (val & ((1 << val_bits) - 1));
		if(!FLAC__bitbuffer_write_raw_uint32(bb, pattern, total_bits))
			return false;
	}
	else {
		/* write the '-0' escape code first */
		if(!FLAC__bitbuffer_write_raw_uint32(bb, 3u << parameter, 2+parameter))
			return false;
		/* write the length */
		if(!FLAC__bitbuffer_write_raw_uint32(bb, val_bits, 5))
			return false;
		/* write the value */
		if(!FLAC__bitbuffer_write_raw_int32(bb, val, val_bits))
			return false;
	}
	return true;
}
#endif /* ifdef FLAC__SYMMETRIC_RICE */

FLAC__bool FLAC__bitbuffer_write_rice_signed(FLAC__BitBuffer *bb, int val, unsigned parameter)
{
	unsigned total_bits, interesting_bits, msbs, uval;
	FLAC__uint32 pattern;

	FLAC__ASSERT(bb != 0);
	FLAC__ASSERT(bb->buffer != 0);
	FLAC__ASSERT(parameter <= 30);

	/* fold signed to unsigned */
	if(val < 0)
		/* equivalent to
		 *     (unsigned)(((--val) << 1) - 1);
		 * but without the overflow problem at MININT
		 */
		uval = (unsigned)(((-(++val)) << 1) + 1);
	else
		uval = (unsigned)(val << 1);

	msbs = uval >> parameter;
	interesting_bits = 1 + parameter;
	total_bits = interesting_bits + msbs;
	pattern = 1 << parameter; /* the unary end bit */
	pattern |= (uval & ((1<<parameter)-1)); /* the binary LSBs */

	if(total_bits <= 32) {
		if(!FLAC__bitbuffer_write_raw_uint32(bb, pattern, total_bits))
			return false;
	}
	else {
		/* write the unary MSBs */
		if(!FLAC__bitbuffer_write_zeroes(bb, msbs))
			return false;
		/* write the unary end bit and binary LSBs */
		if(!FLAC__bitbuffer_write_raw_uint32(bb, pattern, interesting_bits))
			return false;
	}
	return true;
}

#if 0 /* UNUSED */
FLAC__bool FLAC__bitbuffer_write_rice_signed_guarded(FLAC__BitBuffer *bb, int val, unsigned parameter, unsigned max_bits, FLAC__bool *overflow)
{
	unsigned total_bits, interesting_bits, msbs, uval;
	FLAC__uint32 pattern;

	FLAC__ASSERT(bb != 0);
	FLAC__ASSERT(bb->buffer != 0);
	FLAC__ASSERT(parameter <= 30);

	*overflow = false;

	/* fold signed to unsigned */
	if(val < 0)
		/* equivalent to
		 *     (unsigned)(((--val) << 1) - 1);
		 * but without the overflow problem at MININT
		 */
		uval = (unsigned)(((-(++val)) << 1) + 1);
	else
		uval = (unsigned)(val << 1);

	msbs = uval >> parameter;
	interesting_bits = 1 + parameter;
	total_bits = interesting_bits + msbs;
	pattern = 1 << parameter; /* the unary end bit */
	pattern |= (uval & ((1<<parameter)-1)); /* the binary LSBs */

	if(total_bits <= 32) {
		if(!FLAC__bitbuffer_write_raw_uint32(bb, pattern, total_bits))
			return false;
	}
	else if(total_bits > max_bits) {
		*overflow = true;
		return true;
	}
	else {
		/* write the unary MSBs */
		if(!FLAC__bitbuffer_write_zeroes(bb, msbs))
			return false;
		/* write the unary end bit and binary LSBs */
		if(!FLAC__bitbuffer_write_raw_uint32(bb, pattern, interesting_bits))
			return false;
	}
	return true;
}
#endif /* UNUSED */

#if 0 /* UNUSED */
FLAC__bool FLAC__bitbuffer_write_golomb_signed(FLAC__BitBuffer *bb, int val, unsigned parameter)
{
	unsigned total_bits, msbs, uval;
	unsigned k;

	FLAC__ASSERT(bb != 0);
	FLAC__ASSERT(bb->buffer != 0);
	FLAC__ASSERT(parameter > 0);

	/* fold signed to unsigned */
	if(val < 0)
		/* equivalent to
		 *     (unsigned)(((--val) << 1) - 1);
		 * but without the overflow problem at MININT
		 */
		uval = (unsigned)(((-(++val)) << 1) + 1);
	else
		uval = (unsigned)(val << 1);

	k = FLAC__bitmath_ilog2(parameter);
	if(parameter == 1u<<k) {
		unsigned pattern;

		FLAC__ASSERT(k <= 30);

		msbs = uval >> k;
		total_bits = 1 + k + msbs;
		pattern = 1 << k; /* the unary end bit */
		pattern |= (uval & ((1u<<k)-1)); /* the binary LSBs */

		if(total_bits <= 32) {
			if(!FLAC__bitbuffer_write_raw_uint32(bb, pattern, total_bits))
				return false;
		}
		else {
			/* write the unary MSBs */
			if(!FLAC__bitbuffer_write_zeroes(bb, msbs))
				return false;
			/* write the unary end bit and binary LSBs */
			if(!FLAC__bitbuffer_write_raw_uint32(bb, pattern, k+1))
				return false;
		}
	}
	else {
		unsigned q, r, d;

		d = (1 << (k+1)) - parameter;
		q = uval / parameter;
		r = uval - (q * parameter);
		/* write the unary MSBs */
		if(!FLAC__bitbuffer_write_zeroes(bb, q))
			return false;
		/* write the unary end bit */
		if(!FLAC__bitbuffer_write_raw_uint32(bb, 1, 1))
			return false;
		/* write the binary LSBs */
		if(r >= d) {
			if(!FLAC__bitbuffer_write_raw_uint32(bb, r+d, k+1))
				return false;
		}
		else {
			if(!FLAC__bitbuffer_write_raw_uint32(bb, r, k))
				return false;
		}
	}
	return true;
}

FLAC__bool FLAC__bitbuffer_write_golomb_unsigned(FLAC__BitBuffer *bb, unsigned uval, unsigned parameter)
{
	unsigned total_bits, msbs;
	unsigned k;

	FLAC__ASSERT(bb != 0);
	FLAC__ASSERT(bb->buffer != 0);
	FLAC__ASSERT(parameter > 0);

	k = FLAC__bitmath_ilog2(parameter);
	if(parameter == 1u<<k) {
		unsigned pattern;

		FLAC__ASSERT(k <= 30);

		msbs = uval >> k;
		total_bits = 1 + k + msbs;
		pattern = 1 << k; /* the unary end bit */
		pattern |= (uval & ((1u<<k)-1)); /* the binary LSBs */

		if(total_bits <= 32) {
			if(!FLAC__bitbuffer_write_raw_uint32(bb, pattern, total_bits))
				return false;
		}
		else {
			/* write the unary MSBs */
			if(!FLAC__bitbuffer_write_zeroes(bb, msbs))
				return false;
			/* write the unary end bit and binary LSBs */
			if(!FLAC__bitbuffer_write_raw_uint32(bb, pattern, k+1))
				return false;
		}
	}
	else {
		unsigned q, r, d;

		d = (1 << (k+1)) - parameter;
		q = uval / parameter;
		r = uval - (q * parameter);
		/* write the unary MSBs */
		if(!FLAC__bitbuffer_write_zeroes(bb, q))
			return false;
		/* write the unary end bit */
		if(!FLAC__bitbuffer_write_raw_uint32(bb, 1, 1))
			return false;
		/* write the binary LSBs */
		if(r >= d) {
			if(!FLAC__bitbuffer_write_raw_uint32(bb, r+d, k+1))
				return false;
		}
		else {
			if(!FLAC__bitbuffer_write_raw_uint32(bb, r, k))
				return false;
		}
	}
	return true;
}
#endif /* UNUSED */

FLAC__bool FLAC__bitbuffer_write_utf8_uint32(FLAC__BitBuffer *bb, FLAC__uint32 val)
{
	FLAC__bool ok = 1;

	FLAC__ASSERT(bb != 0);
	FLAC__ASSERT(bb->buffer != 0);

	FLAC__ASSERT(!(val & 0x80000000)); /* this version only handles 31 bits */

	if(val < 0x80) {
		return FLAC__bitbuffer_write_raw_uint32(bb, val, 8);
	}
	else if(val < 0x800) {
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0xC0 | (val>>6), 8);
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0x80 | (val&0x3F), 8);
	}
	else if(val < 0x10000) {
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0xE0 | (val>>12), 8);
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0x80 | ((val>>6)&0x3F), 8);
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0x80 | (val&0x3F), 8);
	}
	else if(val < 0x200000) {
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0xF0 | (val>>18), 8);
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0x80 | ((val>>12)&0x3F), 8);
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0x80 | ((val>>6)&0x3F), 8);
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0x80 | (val&0x3F), 8);
	}
	else if(val < 0x4000000) {
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0xF8 | (val>>24), 8);
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0x80 | ((val>>18)&0x3F), 8);
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0x80 | ((val>>12)&0x3F), 8);
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0x80 | ((val>>6)&0x3F), 8);
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0x80 | (val&0x3F), 8);
	}
	else {
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0xFC | (val>>30), 8);
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0x80 | ((val>>24)&0x3F), 8);
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0x80 | ((val>>18)&0x3F), 8);
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0x80 | ((val>>12)&0x3F), 8);
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0x80 | ((val>>6)&0x3F), 8);
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0x80 | (val&0x3F), 8);
	}

	return ok;
}

FLAC__bool FLAC__bitbuffer_write_utf8_uint64(FLAC__BitBuffer *bb, FLAC__uint64 val)
{
	FLAC__bool ok = 1;

	FLAC__ASSERT(bb != 0);
	FLAC__ASSERT(bb->buffer != 0);

	FLAC__ASSERT(!(val & 0xFFFFFFF000000000)); /* this version only handles 36 bits */

	if(val < 0x80) {
		return FLAC__bitbuffer_write_raw_uint32(bb, (FLAC__uint32)val, 8);
	}
	else if(val < 0x800) {
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0xC0 | (FLAC__uint32)(val>>6), 8);
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0x80 | (FLAC__uint32)(val&0x3F), 8);
	}
	else if(val < 0x10000) {
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0xE0 | (FLAC__uint32)(val>>12), 8);
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0x80 | (FLAC__uint32)((val>>6)&0x3F), 8);
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0x80 | (FLAC__uint32)(val&0x3F), 8);
	}
	else if(val < 0x200000) {
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0xF0 | (FLAC__uint32)(val>>18), 8);
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0x80 | (FLAC__uint32)((val>>12)&0x3F), 8);
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0x80 | (FLAC__uint32)((val>>6)&0x3F), 8);
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0x80 | (FLAC__uint32)(val&0x3F), 8);
	}
	else if(val < 0x4000000) {
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0xF8 | (FLAC__uint32)(val>>24), 8);
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0x80 | (FLAC__uint32)((val>>18)&0x3F), 8);
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0x80 | (FLAC__uint32)((val>>12)&0x3F), 8);
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0x80 | (FLAC__uint32)((val>>6)&0x3F), 8);
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0x80 | (FLAC__uint32)(val&0x3F), 8);
	}
	else if(val < 0x80000000) {
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0xFC | (FLAC__uint32)(val>>30), 8);
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0x80 | (FLAC__uint32)((val>>24)&0x3F), 8);
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0x80 | (FLAC__uint32)((val>>18)&0x3F), 8);
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0x80 | (FLAC__uint32)((val>>12)&0x3F), 8);
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0x80 | (FLAC__uint32)((val>>6)&0x3F), 8);
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0x80 | (FLAC__uint32)(val&0x3F), 8);
	}
	else {
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0xFE, 8);
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0x80 | (FLAC__uint32)((val>>30)&0x3F), 8);
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0x80 | (FLAC__uint32)((val>>24)&0x3F), 8);
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0x80 | (FLAC__uint32)((val>>18)&0x3F), 8);
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0x80 | (FLAC__uint32)((val>>12)&0x3F), 8);
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0x80 | (FLAC__uint32)((val>>6)&0x3F), 8);
		ok &= FLAC__bitbuffer_write_raw_uint32(bb, 0x80 | (FLAC__uint32)(val&0x3F), 8);
	}

	return ok;
}

FLAC__bool FLAC__bitbuffer_zero_pad_to_byte_boundary(FLAC__BitBuffer *bb)
{
	/* 0-pad to byte boundary */
	if(bb->bits & 7u)
		return FLAC__bitbuffer_write_zeroes(bb, 8 - (bb->bits & 7u));
	else
		return true;
}

FLAC__bool FLAC__bitbuffer_peek_bit(FLAC__BitBuffer *bb, unsigned *val, FLAC__bool (*read_callback)(FLAC__byte buffer[], unsigned *bytes, void *client_data), void *client_data)
{
	/* to avoid a drastic speed penalty we don't:
	FLAC__ASSERT(bb != 0);
	FLAC__ASSERT(bb->buffer != 0);
	FLAC__ASSERT(bb->bits == 0);
	*/

	while(1) {
		if(bb->total_consumed_bits < bb->total_bits) {
			*val = (bb->buffer[bb->consumed_blurbs] & BLURB_BIT_TO_MASK(bb->consumed_bits))? 1 : 0;
			return true;
		}
		else {
			if(!bitbuffer_read_from_client_(bb, read_callback, client_data))
				return false;
		}
	}
}

FLAC__bool FLAC__bitbuffer_read_bit(FLAC__BitBuffer *bb, unsigned *val, FLAC__bool (*read_callback)(FLAC__byte buffer[], unsigned *bytes, void *client_data), void *client_data)
{
	/* to avoid a drastic speed penalty we don't:
	FLAC__ASSERT(bb != 0);
	FLAC__ASSERT(bb->buffer != 0);
	FLAC__ASSERT(bb->bits == 0);
	*/

	while(1) {
		if(bb->total_consumed_bits < bb->total_bits) {
			*val = (bb->buffer[bb->consumed_blurbs] & BLURB_BIT_TO_MASK(bb->consumed_bits))? 1 : 0;
			bb->consumed_bits++;
			if(bb->consumed_bits == FLAC__BITS_PER_BLURB) {
				CRC16_UPDATE_BLURB(bb, bb->buffer[bb->consumed_blurbs], bb->read_crc16);
				bb->consumed_blurbs++;
				bb->consumed_bits = 0;
			}
			bb->total_consumed_bits++;
			return true;
		}
		else {
			if(!bitbuffer_read_from_client_(bb, read_callback, client_data))
				return false;
		}
	}
}

FLAC__bool FLAC__bitbuffer_read_bit_to_uint32(FLAC__BitBuffer *bb, FLAC__uint32 *val, FLAC__bool (*read_callback)(FLAC__byte buffer[], unsigned *bytes, void *client_data), void *client_data)
{
	/* to avoid a drastic speed penalty we don't:
	FLAC__ASSERT(bb != 0);
	FLAC__ASSERT(bb->buffer != 0);
	FLAC__ASSERT(bb->bits == 0);
	*/

	while(1) {
		if(bb->total_consumed_bits < bb->total_bits) {
			*val <<= 1;
			*val |= (bb->buffer[bb->consumed_blurbs] & BLURB_BIT_TO_MASK(bb->consumed_bits))? 1 : 0;
			bb->consumed_bits++;
			if(bb->consumed_bits == FLAC__BITS_PER_BLURB) {
				CRC16_UPDATE_BLURB(bb, bb->buffer[bb->consumed_blurbs], bb->read_crc16);
				bb->consumed_blurbs++;
				bb->consumed_bits = 0;
			}
			bb->total_consumed_bits++;
			return true;
		}
		else {
			if(!bitbuffer_read_from_client_(bb, read_callback, client_data))
				return false;
		}
	}
}

FLAC__bool FLAC__bitbuffer_read_bit_to_uint64(FLAC__BitBuffer *bb, FLAC__uint64 *val, FLAC__bool (*read_callback)(FLAC__byte buffer[], unsigned *bytes, void *client_data), void *client_data)
{
	/* to avoid a drastic speed penalty we don't:
	FLAC__ASSERT(bb != 0);
	FLAC__ASSERT(bb->buffer != 0);
	FLAC__ASSERT(bb->bits == 0);
	*/

	while(1) {
		if(bb->total_consumed_bits < bb->total_bits) {
			*val <<= 1;
			*val |= (bb->buffer[bb->consumed_blurbs] & BLURB_BIT_TO_MASK(bb->consumed_bits))? 1 : 0;
			bb->consumed_bits++;
			if(bb->consumed_bits == FLAC__BITS_PER_BLURB) {
				CRC16_UPDATE_BLURB(bb, bb->buffer[bb->consumed_blurbs], bb->read_crc16);
				bb->consumed_blurbs++;
				bb->consumed_bits = 0;
			}
			bb->total_consumed_bits++;
			return true;
		}
		else {
			if(!bitbuffer_read_from_client_(bb, read_callback, client_data))
				return false;
		}
	}
}

FLaC__INLINE FLAC__bool FLAC__bitbuffer_read_raw_uint32(FLAC__BitBuffer *bb, FLAC__uint32 *val, const unsigned bits, FLAC__bool (*read_callback)(FLAC__byte buffer[], unsigned *bytes, void *client_data), void *client_data)
#ifdef FLAC__NO_MANUAL_INLINING
{
	unsigned i;

	FLAC__ASSERT(bb != 0);
	FLAC__ASSERT(bb->buffer != 0);

	FLAC__ASSERT(bits <= 32);

	*val = 0;
	for(i = 0; i < bits; i++) {
		if(!FLAC__bitbuffer_read_bit_to_uint32(bb, val, read_callback, client_data))
			return false;
	}
	return true;
}
#else
{
	unsigned i, bits_ = bits;
	FLAC__uint32 v = 0;

	FLAC__ASSERT(bb != 0);
	FLAC__ASSERT(bb->buffer != 0);

	FLAC__ASSERT(bits <= 32);
	FLAC__ASSERT((bb->capacity*FLAC__BITS_PER_BLURB) * 2 >= bits);

	if(bits == 0) {
		*val = 0;
		return true;
	}

	while(bb->total_consumed_bits + bits > bb->total_bits) {
		if(!bitbuffer_read_from_client_(bb, read_callback, client_data))
			return false;
	}
#if FLAC__BITS_PER_BLURB > 8
	if(bb->bits == 0 || bb->consumed_blurbs < bb->blurbs) { //@@@ comment on why this is here
#endif
		if(bb->consumed_bits) {
			i = FLAC__BITS_PER_BLURB - bb->consumed_bits;
			if(i <= bits_) {
				v = bb->buffer[bb->consumed_blurbs] & (FLAC__BLURB_ALL_ONES >> bb->consumed_bits);
				bits_ -= i;
				CRC16_UPDATE_BLURB(bb, bb->buffer[bb->consumed_blurbs], bb->read_crc16);
				bb->consumed_blurbs++;
				bb->consumed_bits = 0;
				/* we hold off updating bb->total_consumed_bits until the end */
			}
			else {
				*val = (bb->buffer[bb->consumed_blurbs] & (FLAC__BLURB_ALL_ONES >> bb->consumed_bits)) >> (i-bits_);
				bb->consumed_bits += bits_;
				bb->total_consumed_bits += bits_;
				return true;
			}
		}
#if FLAC__BITS_PER_BLURB == 32
		/* note that we know bits_ cannot be > 32 because of previous assertions */
		if(bits_ == FLAC__BITS_PER_BLURB) {
			v = bb->buffer[bb->consumed_blurbs];
			CRC16_UPDATE_BLURB(bb, v, bb->read_crc16);
			bb->consumed_blurbs++;
			/* bb->consumed_bits is already 0 */
			bb->total_consumed_bits += bits;
			*val = v;
			return true;
		}
#else
		while(bits_ >= FLAC__BITS_PER_BLURB) {
			v <<= FLAC__BITS_PER_BLURB;
			v |= bb->buffer[bb->consumed_blurbs];
			bits_ -= FLAC__BITS_PER_BLURB;
			CRC16_UPDATE_BLURB(bb, bb->buffer[bb->consumed_blurbs], bb->read_crc16);
			bb->consumed_blurbs++;
			/* bb->consumed_bits is already 0 */
			/* we hold off updating bb->total_consumed_bits until the end */
		}
#endif
		if(bits_ > 0) {
			v <<= bits_;
			v |= (bb->buffer[bb->consumed_blurbs] >> (FLAC__BITS_PER_BLURB-bits_));
			bb->consumed_bits = bits_;
			/* we hold off updating bb->total_consumed_bits until the end */
		}
		bb->total_consumed_bits += bits;
		*val = v;
#if FLAC__BITS_PER_BLURB > 8
	}
	else {
		*val = 0;
		for(i = 0; i < bits; i++) {
			if(!FLAC__bitbuffer_read_bit_to_uint32(bb, val, read_callback, client_data))
				return false;
		}
	}
#endif
	return true;
}
#endif

FLAC__bool FLAC__bitbuffer_read_raw_int32(FLAC__BitBuffer *bb, FLAC__int32 *val, const unsigned bits, FLAC__bool (*read_callback)(FLAC__byte buffer[], unsigned *bytes, void *client_data), void *client_data)
#ifdef FLAC__NO_MANUAL_INLINING
{
	unsigned i;
	FLAC__uint32 v;

	FLAC__ASSERT(bb != 0);
	FLAC__ASSERT(bb->buffer != 0);

	FLAC__ASSERT(bits <= 32);

	if(bits == 0) {
		*val = 0;
		return true;
	}

	v = 0;
	for(i = 0; i < bits; i++) {
		if(!FLAC__bitbuffer_read_bit_to_uint32(bb, &v, read_callback, client_data))
			return false;
	}

	/* fix the sign */
	i = 32 - bits;
	if(i) {
		v <<= i;
		*val = (FLAC__int32)v;
		*val >>= i;
	}
	else
		*val = (FLAC__int32)v;

	return true;
}
#else
{
	unsigned i, bits_ = bits;
	FLAC__uint32 v = 0;

	FLAC__ASSERT(bb != 0);
	FLAC__ASSERT(bb->buffer != 0);

	FLAC__ASSERT(bits <= 32);
	FLAC__ASSERT((bb->capacity*FLAC__BITS_PER_BLURB) * 2 >= bits);

	if(bits == 0) {
		*val = 0;
		return true;
	}

	while(bb->total_consumed_bits + bits > bb->total_bits) {
		if(!bitbuffer_read_from_client_(bb, read_callback, client_data))
			return false;
	}
#if FLAC__BITS_PER_BLURB > 8
	if(bb->bits == 0 || bb->consumed_blurbs < bb->blurbs) { //@@@ comment on why this is here
#endif
		if(bb->consumed_bits) {
			i = FLAC__BITS_PER_BLURB - bb->consumed_bits;
			if(i <= bits_) {
				v = bb->buffer[bb->consumed_blurbs] & (FLAC__BLURB_ALL_ONES >> bb->consumed_bits);
				bits_ -= i;
				CRC16_UPDATE_BLURB(bb, bb->buffer[bb->consumed_blurbs], bb->read_crc16);
				bb->consumed_blurbs++;
				bb->consumed_bits = 0;
				/* we hold off updating bb->total_consumed_bits until the end */
			}
			else {
				/* bits_ must be < FLAC__BITS_PER_BLURB-1 if we get to here */
				v = (bb->buffer[bb->consumed_blurbs] & (FLAC__BLURB_ALL_ONES >> bb->consumed_bits));
				v <<= (32-i);
				*val = (FLAC__int32)v;
				*val >>= (32-bits_);
				bb->consumed_bits += bits_;
				bb->total_consumed_bits += bits_;
				return true;
			}
		}
#if FLAC__BITS_PER_BLURB == 32
		/* note that we know bits_ cannot be > 32 because of previous assertions */
		if(bits_ == FLAC__BITS_PER_BLURB) {
			v = bb->buffer[bb->consumed_blurbs];
			bits_ = 0;
			CRC16_UPDATE_BLURB(bb, v, bb->read_crc16);
			bb->consumed_blurbs++;
			/* bb->consumed_bits is already 0 */
			/* we hold off updating bb->total_consumed_bits until the end */
		}
#else
		while(bits_ >= FLAC__BITS_PER_BLURB) {
			v <<= FLAC__BITS_PER_BLURB;
			v |= bb->buffer[bb->consumed_blurbs];
			bits_ -= FLAC__BITS_PER_BLURB;
			CRC16_UPDATE_BLURB(bb, bb->buffer[bb->consumed_blurbs], bb->read_crc16);
			bb->consumed_blurbs++;
			/* bb->consumed_bits is already 0 */
			/* we hold off updating bb->total_consumed_bits until the end */
		}
#endif
		if(bits_ > 0) {
			v <<= bits_;
			v |= (bb->buffer[bb->consumed_blurbs] >> (FLAC__BITS_PER_BLURB-bits_));
			bb->consumed_bits = bits_;
			/* we hold off updating bb->total_consumed_bits until the end */
		}
		bb->total_consumed_bits += bits;
#if FLAC__BITS_PER_BLURB > 8
	}
	else {
		for(i = 0; i < bits; i++) {
			if(!FLAC__bitbuffer_read_bit_to_uint32(bb, &v, read_callback, client_data))
				return false;
		}
	}
#endif

	/* fix the sign */
	i = 32 - bits;
	if(i) {
		v <<= i;
		*val = (FLAC__int32)v;
		*val >>= i;
	}
	else
		*val = (FLAC__int32)v;

	return true;
}
#endif

FLAC__bool FLAC__bitbuffer_read_raw_uint64(FLAC__BitBuffer *bb, FLAC__uint64 *val, const unsigned bits, FLAC__bool (*read_callback)(FLAC__byte buffer[], unsigned *bytes, void *client_data), void *client_data)
#ifdef FLAC__NO_MANUAL_INLINING
{
	unsigned i;

	FLAC__ASSERT(bb != 0);
	FLAC__ASSERT(bb->buffer != 0);

	FLAC__ASSERT(bits <= 64);

	*val = 0;
	for(i = 0; i < bits; i++) {
		if(!FLAC__bitbuffer_read_bit_to_uint64(bb, val, read_callback, client_data))
			return false;
	}
	return true;
}
#else
{
	unsigned i, bits_ = bits;
	FLAC__uint64 v = 0;

	FLAC__ASSERT(bb != 0);
	FLAC__ASSERT(bb->buffer != 0);

	FLAC__ASSERT(bits <= 64);
	FLAC__ASSERT((bb->capacity*FLAC__BITS_PER_BLURB) * 2 >= bits);

	if(bits == 0) {
		*val = 0;
		return true;
	}

	while(bb->total_consumed_bits + bits > bb->total_bits) {
		if(!bitbuffer_read_from_client_(bb, read_callback, client_data))
			return false;
	}
#if FLAC__BITS_PER_BLURB > 8
	if(bb->bits == 0 || bb->consumed_blurbs < bb->blurbs) { //@@@ comment on why this is here
#endif
		if(bb->consumed_bits) {
			i = FLAC__BITS_PER_BLURB - bb->consumed_bits;
			if(i <= bits_) {
				v = bb->buffer[bb->consumed_blurbs] & (FLAC__BLURB_ALL_ONES >> bb->consumed_bits);
				bits_ -= i;
				CRC16_UPDATE_BLURB(bb, bb->buffer[bb->consumed_blurbs], bb->read_crc16);
				bb->consumed_blurbs++;
				bb->consumed_bits = 0;
				/* we hold off updating bb->total_consumed_bits until the end */
			}
			else {
				*val = (bb->buffer[bb->consumed_blurbs] & (FLAC__BLURB_ALL_ONES >> bb->consumed_bits)) >> (i-bits_);
				bb->consumed_bits += bits_;
				bb->total_consumed_bits += bits_;
				return true;
			}
		}
		while(bits_ >= FLAC__BITS_PER_BLURB) {
			v <<= FLAC__BITS_PER_BLURB;
			v |= bb->buffer[bb->consumed_blurbs];
			bits_ -= FLAC__BITS_PER_BLURB;
			CRC16_UPDATE_BLURB(bb, bb->buffer[bb->consumed_blurbs], bb->read_crc16);
			bb->consumed_blurbs++;
			/* bb->consumed_bits is already 0 */
			/* we hold off updating bb->total_consumed_bits until the end */
		}
		if(bits_ > 0) {
			v <<= bits_;
			v |= (bb->buffer[bb->consumed_blurbs] >> (FLAC__BITS_PER_BLURB-bits_));
			bb->consumed_bits = bits_;
			/* we hold off updating bb->total_consumed_bits until the end */
		}
		bb->total_consumed_bits += bits;
		*val = v;
#if FLAC__BITS_PER_BLURB > 8
	}
	else {
		*val = 0;
		for(i = 0; i < bits; i++) {
			if(!FLAC__bitbuffer_read_bit_to_uint64(bb, val, read_callback, client_data))
				return false;
		}
	}
#endif
	return true;
}
#endif

FLAC__bool FLAC__bitbuffer_read_raw_int64(FLAC__BitBuffer *bb, FLAC__int64 *val, const unsigned bits, FLAC__bool (*read_callback)(FLAC__byte buffer[], unsigned *bytes, void *client_data), void *client_data)
#ifdef FLAC__NO_MANUAL_INLINING
{
	unsigned i;
	FLAC__uint64 v;

	FLAC__ASSERT(bb != 0);
	FLAC__ASSERT(bb->buffer != 0);

	FLAC__ASSERT(bits <= 64);

	v = 0;
	for(i = 0; i < bits; i++) {
		if(!FLAC__bitbuffer_read_bit_to_uint64(bb, &v, read_callback, client_data))
			return false;
	}
	/* fix the sign */
	i = 64 - bits;
	if(i) {
		v <<= i;
		*val = (FLAC__int64)v;
		*val >>= i;
	}
	else
		*val = (FLAC__int64)v;

	return true;
}
#else
{
	unsigned i, bits_ = bits;
	FLAC__uint64 v = 0;

	FLAC__ASSERT(bb != 0);
	FLAC__ASSERT(bb->buffer != 0);

	FLAC__ASSERT(bits <= 64);
	FLAC__ASSERT((bb->capacity*FLAC__BITS_PER_BLURB) * 2 >= bits);

	if(bits == 0) {
		*val = 0;
		return true;
	}

	while(bb->total_consumed_bits + bits > bb->total_bits) {
		if(!bitbuffer_read_from_client_(bb, read_callback, client_data))
			return false;
	}
#if FLAC__BITS_PER_BLURB > 8
	if(bb->bits == 0 || bb->consumed_blurbs < bb->blurbs) { //@@@ comment on why this is here
#endif
		if(bb->consumed_bits) {
			i = FLAC__BITS_PER_BLURB - bb->consumed_bits;
			if(i <= bits_) {
				v = bb->buffer[bb->consumed_blurbs] & (FLAC__BLURB_ALL_ONES >> bb->consumed_bits);
				bits_ -= i;
				CRC16_UPDATE_BLURB(bb, bb->buffer[bb->consumed_blurbs], bb->read_crc16);
				bb->consumed_blurbs++;
				bb->consumed_bits = 0;
				/* we hold off updating bb->total_consumed_bits until the end */
			}
			else {
				/* bits_ must be < FLAC__BITS_PER_BLURB-1 if we get to here */
				v = (bb->buffer[bb->consumed_blurbs] & (FLAC__BLURB_ALL_ONES >> bb->consumed_bits));
				v <<= (64-i);
				*val = (FLAC__int64)v;
				*val >>= (64-bits_);
				bb->consumed_bits += bits_;
				bb->total_consumed_bits += bits_;
				return true;
			}
		}
		while(bits_ >= FLAC__BITS_PER_BLURB) {
			v <<= FLAC__BITS_PER_BLURB;
			v |= bb->buffer[bb->consumed_blurbs];
			bits_ -= FLAC__BITS_PER_BLURB;
			CRC16_UPDATE_BLURB(bb, bb->buffer[bb->consumed_blurbs], bb->read_crc16);
			bb->consumed_blurbs++;
			/* bb->consumed_bits is already 0 */
			/* we hold off updating bb->total_consumed_bits until the end */
		}
		if(bits_ > 0) {
			v <<= bits_;
			v |= (bb->buffer[bb->consumed_blurbs] >> (FLAC__BITS_PER_BLURB-bits_));
			bb->consumed_bits = bits_;
			/* we hold off updating bb->total_consumed_bits until the end */
		}
		bb->total_consumed_bits += bits;
#if FLAC__BITS_PER_BLURB > 8
	}
	else {
		for(i = 0; i < bits; i++) {
			if(!FLAC__bitbuffer_read_bit_to_uint64(bb, &v, read_callback, client_data))
				return false;
		}
	}
#endif

	/* fix the sign */
	i = 64 - bits;
	if(i) {
		v <<= i;
		*val = (FLAC__int64)v;
		*val >>= i;
	}
	else
		*val = (FLAC__int64)v;

	return true;
}
#endif

FLaC__INLINE FLAC__bool FLAC__bitbuffer_read_unary_unsigned(FLAC__BitBuffer *bb, unsigned *val, FLAC__bool (*read_callback)(FLAC__byte buffer[], unsigned *bytes, void *client_data), void *client_data)
#ifdef FLAC__NO_MANUAL_INLINING
{
	unsigned bit, val_ = 0;

	FLAC__ASSERT(bb != 0);
	FLAC__ASSERT(bb->buffer != 0);

	while(1) {
		if(!FLAC__bitbuffer_read_bit(bb, &bit, read_callback, client_data))
			return false;
		if(bit)
			break;
		else
			val_++;
	}
	*val = val_;
	return true;
}
#else
{
	unsigned i, val_ = 0;
	unsigned total_blurbs_ = (bb->total_bits + (FLAC__BITS_PER_BLURB-1)) / FLAC__BITS_PER_BLURB;
	FLAC__blurb b;

	FLAC__ASSERT(bb != 0);
	FLAC__ASSERT(bb->buffer != 0);

#if FLAC__BITS_PER_BLURB > 8
	if(bb->bits == 0 || bb->consumed_blurbs < bb->blurbs) { //@@@ comment on why this is here
#endif
		if(bb->consumed_bits) {
			b = bb->buffer[bb->consumed_blurbs] << bb->consumed_bits;
			if(b) {
				for(i = 0; !(b & FLAC__BLURB_TOP_BIT_ONE); i++)
					b <<= 1;
				*val = i;
				i++;
				bb->consumed_bits += i;
				bb->total_consumed_bits += i;
				if(bb->consumed_bits == FLAC__BITS_PER_BLURB) {
					CRC16_UPDATE_BLURB(bb, bb->buffer[bb->consumed_blurbs], bb->read_crc16);
					bb->consumed_blurbs++;
					bb->consumed_bits = 0;
				}
				return true;
			}
			else {
				val_ = FLAC__BITS_PER_BLURB - bb->consumed_bits;
				CRC16_UPDATE_BLURB(bb, bb->buffer[bb->consumed_blurbs], bb->read_crc16);
				bb->consumed_blurbs++;
				bb->consumed_bits = 0;
				bb->total_consumed_bits += val_;
			}
		}
		while(1) {
			if(bb->consumed_blurbs >= total_blurbs_) {
				if(!bitbuffer_read_from_client_(bb, read_callback, client_data))
					return false;
				total_blurbs_ = (bb->total_bits + (FLAC__BITS_PER_BLURB-1)) / FLAC__BITS_PER_BLURB;
			}
			b = bb->buffer[bb->consumed_blurbs];
			if(b) {
				for(i = 0; !(b & FLAC__BLURB_TOP_BIT_ONE); i++)
					b <<= 1;
				val_ += i;
				i++;
				bb->consumed_bits = i;
				*val = val_;
				if(i == FLAC__BITS_PER_BLURB) {
					CRC16_UPDATE_BLURB(bb, bb->buffer[bb->consumed_blurbs], bb->read_crc16);
					bb->consumed_blurbs++;
					bb->consumed_bits = 0;
				}
				bb->total_consumed_bits += i;
				return true;
			}
			else {
				val_ += FLAC__BITS_PER_BLURB;
				CRC16_UPDATE_BLURB(bb, 0, bb->read_crc16);
				bb->consumed_blurbs++;
				/* bb->consumed_bits is already 0 */
				bb->total_consumed_bits += FLAC__BITS_PER_BLURB;
			}
		}
#if FLAC__BITS_PER_BLURB > 8
	}
	else {
		while(1) {
			if(!FLAC__bitbuffer_read_bit(bb, &i, read_callback, client_data))
				return false;
			if(i)
				break;
			else
				val_++;
		}
		*val = val_;
		return true;
	}
#endif
}
#endif

#ifdef FLAC__SYMMETRIC_RICE
FLAC__bool FLAC__bitbuffer_read_symmetric_rice_signed(FLAC__BitBuffer *bb, int *val, unsigned parameter, FLAC__bool (*read_callback)(FLAC__byte buffer[], unsigned *bytes, void *client_data), void *client_data)
{
	FLAC__uint32 sign = 0, lsbs = 0, msbs = 0;

	FLAC__ASSERT(bb != 0);
	FLAC__ASSERT(bb->buffer != 0);
	FLAC__ASSERT(parameter <= 31);

	/* read the unary MSBs and end bit */
	if(!FLAC__bitbuffer_read_unary_unsigned(bb, &msbs, read_callback, client_data))
		return false;

	/* read the sign bit */
	if(!FLAC__bitbuffer_read_bit_to_uint32(bb, &sign, read_callback, client_data))
		return false;

	/* read the binary LSBs */
	if(!FLAC__bitbuffer_read_raw_uint32(bb, &lsbs, parameter, read_callback, client_data))
		return false;

	/* compose the value */
	*val = (msbs << parameter) | lsbs;
	if(sign)
		*val = -(*val);

	return true;
}
#endif /* ifdef FLAC__SYMMETRIC_RICE */

FLAC__bool FLAC__bitbuffer_read_rice_signed(FLAC__BitBuffer *bb, int *val, unsigned parameter, FLAC__bool (*read_callback)(FLAC__byte buffer[], unsigned *bytes, void *client_data), void *client_data)
{
	FLAC__uint32 lsbs = 0, msbs = 0;
	unsigned uval;

	FLAC__ASSERT(bb != 0);
	FLAC__ASSERT(bb->buffer != 0);
	FLAC__ASSERT(parameter <= 31);

	/* read the unary MSBs and end bit */
	if(!FLAC__bitbuffer_read_unary_unsigned(bb, &msbs, read_callback, client_data))
		return false;

	/* read the binary LSBs */
	if(!FLAC__bitbuffer_read_raw_uint32(bb, &lsbs, parameter, read_callback, client_data))
		return false;

	/* compose the value */
	uval = (msbs << parameter) | lsbs;
	if(uval & 1)
		*val = -((int)(uval >> 1)) - 1;
	else
		*val = (int)(uval >> 1);

	return true;
}

#if 0 /* UNUSED */
FLAC__bool FLAC__bitbuffer_read_golomb_signed(FLAC__BitBuffer *bb, int *val, unsigned parameter, FLAC__bool (*read_callback)(FLAC__byte buffer[], unsigned *bytes, void *client_data), void *client_data)
{
	FLAC__uint32 lsbs = 0, msbs = 0;
	unsigned bit, uval, k;

	FLAC__ASSERT(bb != 0);
	FLAC__ASSERT(bb->buffer != 0);

	k = FLAC__bitmath_ilog2(parameter);

	/* read the unary MSBs and end bit */
	if(!FLAC__bitbuffer_read_unary_unsigned(bb, &msbs, read_callback, client_data))
		return false;

	/* read the binary LSBs */
	if(!FLAC__bitbuffer_read_raw_uint32(bb, &lsbs, k, read_callback, client_data))
		return false;

	if(parameter == 1u<<k) {
		/* compose the value */
		uval = (msbs << k) | lsbs;
	}
	else {
		unsigned d = (1 << (k+1)) - parameter;
		if(lsbs >= d) {
			if(!FLAC__bitbuffer_read_bit(bb, &bit, read_callback, client_data))
				return false;
			lsbs <<= 1;
			lsbs |= bit;
			lsbs -= d;
		}
		/* compose the value */
		uval = msbs * parameter + lsbs;
	}

	/* unfold unsigned to signed */
	if(uval & 1)
		*val = -((int)(uval >> 1)) - 1;
	else
		*val = (int)(uval >> 1);

	return true;
}

FLAC__bool FLAC__bitbuffer_read_golomb_unsigned(FLAC__BitBuffer *bb, unsigned *val, unsigned parameter, FLAC__bool (*read_callback)(FLAC__byte buffer[], unsigned *bytes, void *client_data), void *client_data)
{
	FLAC__uint32 lsbs, msbs = 0;
	unsigned bit, k;

	FLAC__ASSERT(bb != 0);
	FLAC__ASSERT(bb->buffer != 0);

	k = FLAC__bitmath_ilog2(parameter);

	/* read the unary MSBs and end bit */
	if(!FLAC__bitbuffer_read_unary_unsigned(bb, &msbs, read_callback, client_data))
		return false;

	/* read the binary LSBs */
	if(!FLAC__bitbuffer_read_raw_uint32(bb, &lsbs, k, read_callback, client_data))
		return false;

	if(parameter == 1u<<k) {
		/* compose the value */
		*val = (msbs << k) | lsbs;
	}
	else {
		unsigned d = (1 << (k+1)) - parameter;
		if(lsbs >= d) {
			if(!FLAC__bitbuffer_read_bit(bb, &bit, read_callback, client_data))
				return false;
			lsbs <<= 1;
			lsbs |= bit;
			lsbs -= d;
		}
		/* compose the value */
		*val = msbs * parameter + lsbs;
	}

	return true;
}
#endif /* UNUSED */

/* on return, if *val == 0xffffffff then the utf-8 sequence was invalid, but the return value will be true */
FLAC__bool FLAC__bitbuffer_read_utf8_uint32(FLAC__BitBuffer *bb, FLAC__uint32 *val, FLAC__bool (*read_callback)(FLAC__byte buffer[], unsigned *bytes, void *client_data), void *client_data, FLAC__byte *raw, unsigned *rawlen)
{
	FLAC__uint32 v = 0;
	FLAC__uint32 x;
	unsigned i;

	if(!FLAC__bitbuffer_read_raw_uint32(bb, &x, 8, read_callback, client_data))
		return false;
	if(raw)
		raw[(*rawlen)++] = (FLAC__byte)x;
	if(!(x & 0x80)) { /* 0xxxxxxx */
		v = x;
		i = 0;
	}
	else if(x & 0xC0 && !(x & 0x20)) { /* 110xxxxx */
		v = x & 0x1F;
		i = 1;
	}
	else if(x & 0xE0 && !(x & 0x10)) { /* 1110xxxx */
		v = x & 0x0F;
		i = 2;
	}
	else if(x & 0xF0 && !(x & 0x08)) { /* 11110xxx */
		v = x & 0x07;
		i = 3;
	}
	else if(x & 0xF8 && !(x & 0x04)) { /* 111110xx */
		v = x & 0x03;
		i = 4;
	}
	else if(x & 0xFC && !(x & 0x02)) { /* 1111110x */
		v = x & 0x01;
		i = 5;
	}
	else {
		*val = 0xffffffff;
		return true;
	}
	for( ; i; i--) {
		if(!FLAC__bitbuffer_read_raw_uint32(bb, &x, 8, read_callback, client_data))
			return false;
		if(raw)
			raw[(*rawlen)++] = (FLAC__byte)x;
		if(!(x & 0x80) || (x & 0x40)) { /* 10xxxxxx */
			*val = 0xffffffff;
			return true;
		}
		v <<= 6;
		v |= (x & 0x3F);
	}
	*val = v;
	return true;
}

/* on return, if *val == 0xffffffffffffffff then the utf-8 sequence was invalid, but the return value will be true */
FLAC__bool FLAC__bitbuffer_read_utf8_uint64(FLAC__BitBuffer *bb, FLAC__uint64 *val, FLAC__bool (*read_callback)(FLAC__byte buffer[], unsigned *bytes, void *client_data), void *client_data, FLAC__byte *raw, unsigned *rawlen)
{
	FLAC__uint64 v = 0;
	FLAC__uint32 x;
	unsigned i;

	if(!FLAC__bitbuffer_read_raw_uint32(bb, &x, 8, read_callback, client_data))
		return false;
	if(raw)
		raw[(*rawlen)++] = (FLAC__byte)x;
	if(!(x & 0x80)) { /* 0xxxxxxx */
		v = x;
		i = 0;
	}
	else if(x & 0xC0 && !(x & 0x20)) { /* 110xxxxx */
		v = x & 0x1F;
		i = 1;
	}
	else if(x & 0xE0 && !(x & 0x10)) { /* 1110xxxx */
		v = x & 0x0F;
		i = 2;
	}
	else if(x & 0xF0 && !(x & 0x08)) { /* 11110xxx */
		v = x & 0x07;
		i = 3;
	}
	else if(x & 0xF8 && !(x & 0x04)) { /* 111110xx */
		v = x & 0x03;
		i = 4;
	}
	else if(x & 0xFC && !(x & 0x02)) { /* 1111110x */
		v = x & 0x01;
		i = 5;
	}
	else if(x & 0xFE && !(x & 0x01)) { /* 11111110 */
		v = 0;
		i = 6;
	}
	else {
		*val = 0xffffffffffffffff;
		return true;
	}
	for( ; i; i--) {
		if(!FLAC__bitbuffer_read_raw_uint32(bb, &x, 8, read_callback, client_data))
			return false;
		if(raw)
			raw[(*rawlen)++] = (FLAC__byte)x;
		if(!(x & 0x80) || (x & 0x40)) { /* 10xxxxxx */
			*val = 0xffffffffffffffff;
			return true;
		}
		v <<= 6;
		v |= (x & 0x3F);
	}
	*val = v;
	return true;
}

void FLAC__bitbuffer_dump(const FLAC__BitBuffer *bb, FILE *out)
{
	unsigned i, j;
	if(bb == 0) {
		fprintf(out, "bitbuffer is NULL\n");
	}
	else {
		fprintf(out, "bitbuffer: capacity=%u blurbs=%u bits=%u total_bits=%u consumed: blurbs=%u, bits=%u, total_bits=%u\n", bb->capacity, bb->blurbs, bb->bits, bb->total_bits, bb->consumed_blurbs, bb->consumed_bits, bb->total_consumed_bits);
		for(i = 0; i < bb->blurbs; i++) {
			fprintf(out, "%08X: ", i);
			for(j = 0; j < FLAC__BITS_PER_BLURB; j++)
				if(i*FLAC__BITS_PER_BLURB+j < bb->total_consumed_bits)
					fprintf(out, ".");
				else
					fprintf(out, "%01u", bb->buffer[i] & (1 << (FLAC__BITS_PER_BLURB-j-1)) ? 1:0);
			fprintf(out, "\n");
		}
		if(bb->bits > 0) {
			fprintf(out, "%08X: ", i);
			for(j = 0; j < bb->bits; j++)
				if(i*FLAC__BITS_PER_BLURB+j < bb->total_consumed_bits)
					fprintf(out, ".");
				else
					fprintf(out, "%01u", bb->buffer[i] & (1 << (bb->bits-j-1)) ? 1:0);
			fprintf(out, "\n");
		}
	}
}
