/* libFLAC - Free Lossless Audio Codec library
 * Copyright (C) 2000,2001  Josh Coalson
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

#include <stdio.h>
#include <stdlib.h> /* for malloc() */
#include <string.h> /* for memset/memcpy() */
#include "FLAC/assert.h"
#include "protected/stream_decoder.h"
#include "private/bitbuffer.h"
#include "private/cpu.h"
#include "private/crc.h"
#include "private/fixed.h"
#include "private/lpc.h"

/***********************************************************************
 *
 * Private static data
 *
 ***********************************************************************/

static byte ID3V2_TAG_[3] = { 'I', 'D', '3' };

/***********************************************************************
 *
 * Private class method prototypes
 *
 ***********************************************************************/

static bool stream_decoder_allocate_output_(FLAC__StreamDecoder *decoder, unsigned size, unsigned channels);
static bool stream_decoder_find_metadata_(FLAC__StreamDecoder *decoder);
static bool stream_decoder_read_metadata_(FLAC__StreamDecoder *decoder);
static bool stream_decoder_skip_id3v2_tag_(FLAC__StreamDecoder *decoder);
static bool stream_decoder_frame_sync_(FLAC__StreamDecoder *decoder);
static bool stream_decoder_read_frame_(FLAC__StreamDecoder *decoder, bool *got_a_frame);
static bool stream_decoder_read_frame_header_(FLAC__StreamDecoder *decoder);
static bool stream_decoder_read_subframe_(FLAC__StreamDecoder *decoder, unsigned channel, unsigned bps);
static bool stream_decoder_read_subframe_constant_(FLAC__StreamDecoder *decoder, unsigned channel, unsigned bps);
static bool stream_decoder_read_subframe_fixed_(FLAC__StreamDecoder *decoder, unsigned channel, unsigned bps, const unsigned order);
static bool stream_decoder_read_subframe_lpc_(FLAC__StreamDecoder *decoder, unsigned channel, unsigned bps, const unsigned order);
static bool stream_decoder_read_subframe_verbatim_(FLAC__StreamDecoder *decoder, unsigned channel, unsigned bps);
static bool stream_decoder_read_residual_partitioned_rice_(FLAC__StreamDecoder *decoder, unsigned predictor_order, unsigned partition_order, int32 *residual);
static bool stream_decoder_read_zero_padding_(FLAC__StreamDecoder *decoder);
static bool read_callback_(byte buffer[], unsigned *bytes, void *client_data);

/***********************************************************************
 *
 * Private class data
 *
 ***********************************************************************/

typedef struct FLAC__StreamDecoderPrivate {
	FLAC__StreamDecoderReadStatus (*read_callback)(const FLAC__StreamDecoder *decoder, byte buffer[], unsigned *bytes, void *client_data);
	FLAC__StreamDecoderWriteStatus (*write_callback)(const FLAC__StreamDecoder *decoder, const FLAC__Frame *frame, const int32 *buffer[], void *client_data);
	void (*metadata_callback)(const FLAC__StreamDecoder *decoder, const FLAC__StreamMetaData *metadata, void *client_data);
	void (*error_callback)(const FLAC__StreamDecoder *decoder, FLAC__StreamDecoderErrorStatus status, void *client_data);
	void (*local_lpc_restore_signal)(const int32 residual[], unsigned data_len, const int32 qlp_coeff[], unsigned order, int lp_quantization, int32 data[]);
	void (*local_lpc_restore_signal_16bit)(const int32 residual[], unsigned data_len, const int32 qlp_coeff[], unsigned order, int lp_quantization, int32 data[]);
	void *client_data;
	FLAC__BitBuffer input;
	int32 *output[FLAC__MAX_CHANNELS];
	int32 *residual[FLAC__MAX_CHANNELS];
	unsigned output_capacity, output_channels;
	uint32 last_frame_number;
	uint64 samples_decoded;
	bool has_stream_info, has_seek_table;
	FLAC__StreamMetaData stream_info;
	FLAC__StreamMetaData seek_table;
	FLAC__Frame frame;
	bool cached; /* true if there is a byte in lookahead */
	FLAC__CPUInfo cpuinfo;
	byte header_warmup[2]; /* contains the sync code and reserved bits */
	byte lookahead; /* temp storage when we need to look ahead one byte in the stream */
} FLAC__StreamDecoderPrivate;

/***********************************************************************
 *
 * Public static class data
 *
 ***********************************************************************/

const char *FLAC__StreamDecoderStateString[] = {
	"FLAC__STREAM_DECODER_SEARCH_FOR_METADATA",
	"FLAC__STREAM_DECODER_READ_METADATA",
	"FLAC__STREAM_DECODER_SEARCH_FOR_FRAME_SYNC",
	"FLAC__STREAM_DECODER_READ_FRAME",
	"FLAC__STREAM_DECODER_END_OF_STREAM",
	"FLAC__STREAM_DECODER_ABORTED",
	"FLAC__STREAM_DECODER_UNPARSEABLE_STREAM",
	"FLAC__STREAM_DECODER_MEMORY_ALLOCATION_ERROR",
	"FLAC__STREAM_DECODER_ALREADY_INITIALIZED",
	"FLAC__STREAM_DECODER_UNINITIALIZED"
};

const char *FLAC__StreamDecoderReadStatusString[] = {
	"FLAC__STREAM_DECODER_READ_CONTINUE",
	"FLAC__STREAM_DECODER_READ_END_OF_STREAM",
	"FLAC__STREAM_DECODER_READ_ABORT"
};

const char *FLAC__StreamDecoderWriteStatusString[] = {
	"FLAC__STREAM_DECODER_WRITE_CONTINUE",
	"FLAC__STREAM_DECODER_WRITE_ABORT"
};

const char *FLAC__StreamDecoderErrorStatusString[] = {
	"FLAC__STREAM_DECODER_ERROR_LOST_SYNC",
	"FLAC__STREAM_DECODER_ERROR_BAD_HEADER",
	"FLAC__STREAM_DECODER_ERROR_FRAME_CRC_MISMATCH"
};

/***********************************************************************
 *
 * Class constructor/destructor
 *
 ***********************************************************************/
FLAC__StreamDecoder *FLAC__stream_decoder_new()
{
	FLAC__StreamDecoder *decoder;

	FLAC__ASSERT(sizeof(int) >= 4); /* we want to die right away if this is not true */

	decoder = (FLAC__StreamDecoder*)malloc(sizeof(FLAC__StreamDecoder));
	if(decoder == 0) {
		return 0;
	}
	decoder->protected = (FLAC__StreamDecoderProtected*)malloc(sizeof(FLAC__StreamDecoderProtected));
	if(decoder->protected == 0) {
		free(decoder);
		return 0;
	}
	decoder->private = (FLAC__StreamDecoderPrivate*)malloc(sizeof(FLAC__StreamDecoderPrivate));
	if(decoder->private == 0) {
		free(decoder->protected);
		free(decoder);
		return 0;
	}

	decoder->protected->state = FLAC__STREAM_DECODER_UNINITIALIZED;

	return decoder;
}

void FLAC__stream_decoder_delete(FLAC__StreamDecoder *decoder)
{
	FLAC__ASSERT(decoder != 0);
	FLAC__ASSERT(decoder->protected != 0);
	FLAC__ASSERT(decoder->private != 0);

	free(decoder->private);
	free(decoder->protected);
	free(decoder);
}

/***********************************************************************
 *
 * Public class methods
 *
 ***********************************************************************/

FLAC__StreamDecoderState FLAC__stream_decoder_init(
	FLAC__StreamDecoder *decoder,
    FLAC__StreamDecoderReadStatus (*read_callback)(const FLAC__StreamDecoder *decoder, byte buffer[], unsigned *bytes, void *client_data),
    FLAC__StreamDecoderWriteStatus (*write_callback)(const FLAC__StreamDecoder *decoder, const FLAC__Frame *frame, const int32 *buffer[], void *client_data),
    void (*metadata_callback)(const FLAC__StreamDecoder *decoder, const FLAC__StreamMetaData *metadata, void *client_data),
    void (*error_callback)(const FLAC__StreamDecoder *decoder, FLAC__StreamDecoderErrorStatus status, void *client_data),
    void *client_data)
{
	unsigned i;

	FLAC__ASSERT(decoder != 0);
	FLAC__ASSERT(read_callback != 0);
	FLAC__ASSERT(write_callback != 0);
	FLAC__ASSERT(metadata_callback != 0);
	FLAC__ASSERT(error_callback != 0);

	if(decoder->protected->state != FLAC__STREAM_DECODER_UNINITIALIZED)
		return decoder->protected->state = FLAC__STREAM_DECODER_ALREADY_INITIALIZED;

	decoder->protected->state = FLAC__STREAM_DECODER_SEARCH_FOR_METADATA;

	decoder->private->read_callback = read_callback;
	decoder->private->write_callback = write_callback;
	decoder->private->metadata_callback = metadata_callback;
	decoder->private->error_callback = error_callback;
	decoder->private->client_data = client_data;

	FLAC__bitbuffer_init(&decoder->private->input);

	for(i = 0; i < FLAC__MAX_CHANNELS; i++) {
		decoder->private->output[i] = 0;
		decoder->private->residual[i] = 0;
	}

	decoder->private->output_capacity = 0;
	decoder->private->output_channels = 0;
	decoder->private->last_frame_number = 0;
	decoder->private->samples_decoded = 0;
	decoder->private->has_stream_info = false;
	decoder->private->has_seek_table = false;
	decoder->private->cached = false;

	/*
	 * get the CPU info and set the function pointers
	 */
	FLAC__cpu_info(&decoder->private->cpuinfo);
	/* first default to the non-asm routines */
	decoder->private->local_lpc_restore_signal = FLAC__lpc_restore_signal;
	decoder->private->local_lpc_restore_signal_16bit = FLAC__lpc_restore_signal;
	/* now override with asm where appropriate */
#ifndef FLAC__NO_ASM
	FLAC__ASSERT(decoder->private->cpuinfo.use_asm);
#ifdef FLAC__CPU_IA32
	FLAC__ASSERT(decoder->private->cpuinfo.type == FLAC__CPUINFO_TYPE_IA32);
#ifdef FLAC__HAS_NASM
	if(decoder->private->cpuinfo.data.ia32.mmx) {
		decoder->private->local_lpc_restore_signal = FLAC__lpc_restore_signal_asm_i386;
		decoder->private->local_lpc_restore_signal_16bit = FLAC__lpc_restore_signal_asm_i386_mmx;
	}
	else {
		decoder->private->local_lpc_restore_signal = FLAC__lpc_restore_signal_asm_i386;
		decoder->private->local_lpc_restore_signal_16bit = FLAC__lpc_restore_signal_asm_i386;
	}
#endif
#endif
#endif

	return decoder->protected->state;
}

void FLAC__stream_decoder_finish(FLAC__StreamDecoder *decoder)
{
	unsigned i;
	FLAC__ASSERT(decoder != 0);
	if(decoder->protected->state == FLAC__STREAM_DECODER_UNINITIALIZED)
		return;
	if(decoder->private->has_seek_table) {
		free(decoder->private->seek_table.data.seek_table.points);
		decoder->private->seek_table.data.seek_table.points = 0;
	}
	FLAC__bitbuffer_free(&decoder->private->input);
	for(i = 0; i < FLAC__MAX_CHANNELS; i++) {
		if(decoder->private->output[i] != 0) {
			free(decoder->private->output[i]);
			decoder->private->output[i] = 0;
		}
		if(decoder->private->residual[i] != 0) {
			free(decoder->private->residual[i]);
			decoder->private->residual[i] = 0;
		}
	}
	decoder->protected->state = FLAC__STREAM_DECODER_UNINITIALIZED;
}

FLAC__StreamDecoderState FLAC__stream_decoder_state(const FLAC__StreamDecoder *decoder)
{
	return decoder->protected->state;
}

unsigned FLAC__stream_decoder_channels(const FLAC__StreamDecoder *decoder)
{
	return decoder->protected->channels;
}

FLAC__ChannelAssignment FLAC__stream_decoder_channel_assignment(const FLAC__StreamDecoder *decoder)
{
	return decoder->protected->channel_assignment;
}

unsigned FLAC__stream_decoder_bits_per_sample(const FLAC__StreamDecoder *decoder)
{
	return decoder->protected->bits_per_sample;
}

unsigned FLAC__stream_decoder_sample_rate(const FLAC__StreamDecoder *decoder)
{
	return decoder->protected->sample_rate;
}

unsigned FLAC__stream_decoder_blocksize(const FLAC__StreamDecoder *decoder)
{
	return decoder->protected->blocksize;
}

bool FLAC__stream_decoder_flush(FLAC__StreamDecoder *decoder)
{
	FLAC__ASSERT(decoder != 0);

	if(!FLAC__bitbuffer_clear(&decoder->private->input)) {
		decoder->protected->state = FLAC__STREAM_DECODER_MEMORY_ALLOCATION_ERROR;
		return false;
	}

	return true;
}

bool FLAC__stream_decoder_reset(FLAC__StreamDecoder *decoder)
{
	FLAC__ASSERT(decoder != 0);

	if(!FLAC__stream_decoder_flush(decoder)) {
		decoder->protected->state = FLAC__STREAM_DECODER_MEMORY_ALLOCATION_ERROR;
		return false;
	}
	decoder->protected->state = FLAC__STREAM_DECODER_SEARCH_FOR_METADATA;

	decoder->private->samples_decoded = 0;

	return true;
}

bool FLAC__stream_decoder_process_whole_stream(FLAC__StreamDecoder *decoder)
{
	bool dummy;
	FLAC__ASSERT(decoder != 0);

	if(decoder->protected->state == FLAC__STREAM_DECODER_END_OF_STREAM)
		return true;

	FLAC__ASSERT(decoder->protected->state == FLAC__STREAM_DECODER_SEARCH_FOR_METADATA);

	if(!FLAC__stream_decoder_reset(decoder)) {
		decoder->protected->state = FLAC__STREAM_DECODER_MEMORY_ALLOCATION_ERROR;
		return false;
	}

	while(1) {
		switch(decoder->protected->state) {
			case FLAC__STREAM_DECODER_SEARCH_FOR_METADATA:
				if(!stream_decoder_find_metadata_(decoder))
					return false; /* above function sets the status for us */
				break;
			case FLAC__STREAM_DECODER_READ_METADATA:
				if(!stream_decoder_read_metadata_(decoder))
					return false; /* above function sets the status for us */
				break;
			case FLAC__STREAM_DECODER_SEARCH_FOR_FRAME_SYNC:
				if(!stream_decoder_frame_sync_(decoder))
					return true; /* above function sets the status for us */
				break;
			case FLAC__STREAM_DECODER_READ_FRAME:
				if(!stream_decoder_read_frame_(decoder, &dummy))
					return false; /* above function sets the status for us */
				break;
			case FLAC__STREAM_DECODER_END_OF_STREAM:
				return true;
			default:
				FLAC__ASSERT(0);
		}
	}
}

bool FLAC__stream_decoder_process_metadata(FLAC__StreamDecoder *decoder)
{
	FLAC__ASSERT(decoder != 0);

	if(decoder->protected->state == FLAC__STREAM_DECODER_END_OF_STREAM)
		return true;

	FLAC__ASSERT(decoder->protected->state == FLAC__STREAM_DECODER_SEARCH_FOR_METADATA);

	if(!FLAC__stream_decoder_reset(decoder)) {
		decoder->protected->state = FLAC__STREAM_DECODER_MEMORY_ALLOCATION_ERROR;
		return false;
	}

	while(1) {
		switch(decoder->protected->state) {
			case FLAC__STREAM_DECODER_SEARCH_FOR_METADATA:
				if(!stream_decoder_find_metadata_(decoder))
					return false; /* above function sets the status for us */
				break;
			case FLAC__STREAM_DECODER_READ_METADATA:
				if(!stream_decoder_read_metadata_(decoder))
					return false; /* above function sets the status for us */
				break;
			case FLAC__STREAM_DECODER_SEARCH_FOR_FRAME_SYNC:
				return true;
				break;
			case FLAC__STREAM_DECODER_END_OF_STREAM:
				return true;
			default:
				FLAC__ASSERT(0);
		}
	}
}

bool FLAC__stream_decoder_process_one_frame(FLAC__StreamDecoder *decoder)
{
	bool got_a_frame;
	FLAC__ASSERT(decoder != 0);

	if(decoder->protected->state == FLAC__STREAM_DECODER_END_OF_STREAM)
		return true;

	FLAC__ASSERT(decoder->protected->state == FLAC__STREAM_DECODER_SEARCH_FOR_FRAME_SYNC);

	while(1) {
		switch(decoder->protected->state) {
			case FLAC__STREAM_DECODER_SEARCH_FOR_FRAME_SYNC:
				if(!stream_decoder_frame_sync_(decoder))
					return true; /* above function sets the status for us */
				break;
			case FLAC__STREAM_DECODER_READ_FRAME:
				if(!stream_decoder_read_frame_(decoder, &got_a_frame))
					return false; /* above function sets the status for us */
				if(got_a_frame)
					return true; /* above function sets the status for us */
				break;
			case FLAC__STREAM_DECODER_END_OF_STREAM:
				return true;
			default:
				FLAC__ASSERT(0);
		}
	}
}

bool FLAC__stream_decoder_process_remaining_frames(FLAC__StreamDecoder *decoder)
{
	bool dummy;
	FLAC__ASSERT(decoder != 0);

	if(decoder->protected->state == FLAC__STREAM_DECODER_END_OF_STREAM)
		return true;

	FLAC__ASSERT(decoder->protected->state == FLAC__STREAM_DECODER_SEARCH_FOR_FRAME_SYNC);

	while(1) {
		switch(decoder->protected->state) {
			case FLAC__STREAM_DECODER_SEARCH_FOR_FRAME_SYNC:
				if(!stream_decoder_frame_sync_(decoder))
					return true; /* above function sets the status for us */
				break;
			case FLAC__STREAM_DECODER_READ_FRAME:
				if(!stream_decoder_read_frame_(decoder, &dummy))
					return false; /* above function sets the status for us */
				break;
			case FLAC__STREAM_DECODER_END_OF_STREAM:
				return true;
			default:
				FLAC__ASSERT(0);
		}
	}
}

/***********************************************************************
 *
 * Protected class methods
 *
 ***********************************************************************/

unsigned FLAC__stream_decoder_input_bytes_unconsumed(const FLAC__StreamDecoder *decoder)
{
	FLAC__ASSERT(decoder != 0);
	return decoder->private->input.bytes - decoder->private->input.consumed_bytes;
}

/***********************************************************************
 *
 * Private class methods
 *
 ***********************************************************************/

bool stream_decoder_allocate_output_(FLAC__StreamDecoder *decoder, unsigned size, unsigned channels)
{
	unsigned i;
	int32 *tmp;

	if(size <= decoder->private->output_capacity && channels <= decoder->private->output_channels)
		return true;

	/* @@@ should change to use realloc() */

	for(i = 0; i < FLAC__MAX_CHANNELS; i++) {
		if(decoder->private->output[i] != 0) {
			free(decoder->private->output[i]);
			decoder->private->output[i] = 0;
		}
		if(decoder->private->residual[i] != 0) {
			free(decoder->private->residual[i]);
			decoder->private->residual[i] = 0;
		}
	}

	for(i = 0; i < channels; i++) {
		tmp = (int32*)malloc(sizeof(int32)*size);
		if(tmp == 0) {
			decoder->protected->state = FLAC__STREAM_DECODER_MEMORY_ALLOCATION_ERROR;
			return false;
		}
		decoder->private->output[i] = tmp;

		tmp = (int32*)malloc(sizeof(int32)*size);
		if(tmp == 0) {
			decoder->protected->state = FLAC__STREAM_DECODER_MEMORY_ALLOCATION_ERROR;
			return false;
		}
		decoder->private->residual[i] = tmp;
	}

	decoder->private->output_capacity = size;
	decoder->private->output_channels = channels;

	return true;
}

bool stream_decoder_find_metadata_(FLAC__StreamDecoder *decoder)
{
	uint32 x;
	unsigned i, id;
	bool first = true;

	FLAC__ASSERT(decoder->private->input.consumed_bits == 0); /* make sure we're byte aligned */

	for(i = id = 0; i < 4; ) {
		if(decoder->private->cached) {
			x = (uint32)decoder->private->lookahead;
			decoder->private->cached = false;
		}
		else {
			if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &x, 8, read_callback_, decoder))
				return false; /* the read_callback_ sets the state for us */
		}
		if(x == FLAC__STREAM_SYNC_STRING[i]) {
			first = true;
			i++;
			id = 0;
			continue;
		}
		if(x == ID3V2_TAG_[id]) {
			id++;
			i = 0;
			if(id == 3) {
				if(!stream_decoder_skip_id3v2_tag_(decoder))
					return false; /* the read_callback_ sets the state for us */
			}
			continue;
		}
		if(x == 0xff) { /* MAGIC NUMBER for the first 8 frame sync bits */
			decoder->private->header_warmup[0] = (byte)x;
			if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &x, 8, read_callback_, decoder))
				return false; /* the read_callback_ sets the state for us */

			/* we have to check if we just read two 0xff's in a row; the second may actually be the beginning of the sync code */
			/* else we have to check if the second byte is the end of a sync code */
			if(x == 0xff) { /* MAGIC NUMBER for the first 8 frame sync bits */
				decoder->private->lookahead = (byte)x;
				decoder->private->cached = true;
			}
			else if(x >> 2 == 0x3e) { /* MAGIC NUMBER for the last 6 sync bits */
				decoder->private->header_warmup[1] = (byte)x;
				decoder->protected->state = FLAC__STREAM_DECODER_READ_FRAME;
				return true;
			}
		}
		i = 0;
		if(first) {
			decoder->private->error_callback(decoder, FLAC__STREAM_DECODER_ERROR_LOST_SYNC, decoder->private->client_data);
			first = false;
		}
	}

	decoder->protected->state = FLAC__STREAM_DECODER_READ_METADATA;
	return true;
}

bool stream_decoder_read_metadata_(FLAC__StreamDecoder *decoder)
{
	uint32 i, x, last_block, type, length;
	uint64 xx;

	FLAC__ASSERT(decoder->private->input.consumed_bits == 0); /* make sure we're byte aligned */

	if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &last_block, FLAC__STREAM_METADATA_IS_LAST_LEN, read_callback_, decoder))
		return false; /* the read_callback_ sets the state for us */
	if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &type, FLAC__STREAM_METADATA_TYPE_LEN, read_callback_, decoder))
		return false; /* the read_callback_ sets the state for us */
	if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &length, FLAC__STREAM_METADATA_LENGTH_LEN, read_callback_, decoder))
		return false; /* the read_callback_ sets the state for us */
	if(type == FLAC__METADATA_TYPE_STREAMINFO) {
		unsigned used_bits = 0;
		decoder->private->stream_info.type = type;
		decoder->private->stream_info.is_last = last_block;
		decoder->private->stream_info.length = length;

		if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &x, FLAC__STREAM_METADATA_STREAMINFO_MIN_BLOCK_SIZE_LEN, read_callback_, decoder))
			return false; /* the read_callback_ sets the state for us */
		decoder->private->stream_info.data.stream_info.min_blocksize = x;
		used_bits += FLAC__STREAM_METADATA_STREAMINFO_MIN_BLOCK_SIZE_LEN;

		if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &x, FLAC__STREAM_METADATA_STREAMINFO_MAX_BLOCK_SIZE_LEN, read_callback_, decoder))
			return false; /* the read_callback_ sets the state for us */
		decoder->private->stream_info.data.stream_info.max_blocksize = x;
		used_bits += FLAC__STREAM_METADATA_STREAMINFO_MAX_BLOCK_SIZE_LEN;

		if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &x, FLAC__STREAM_METADATA_STREAMINFO_MIN_FRAME_SIZE_LEN, read_callback_, decoder))
			return false; /* the read_callback_ sets the state for us */
		decoder->private->stream_info.data.stream_info.min_framesize = x;
		used_bits += FLAC__STREAM_METADATA_STREAMINFO_MIN_FRAME_SIZE_LEN;

		if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &x, FLAC__STREAM_METADATA_STREAMINFO_MAX_FRAME_SIZE_LEN, read_callback_, decoder))
			return false; /* the read_callback_ sets the state for us */
		decoder->private->stream_info.data.stream_info.max_framesize = x;
		used_bits += FLAC__STREAM_METADATA_STREAMINFO_MAX_FRAME_SIZE_LEN;

		if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &x, FLAC__STREAM_METADATA_STREAMINFO_SAMPLE_RATE_LEN, read_callback_, decoder))
			return false; /* the read_callback_ sets the state for us */
		decoder->private->stream_info.data.stream_info.sample_rate = x;
		used_bits += FLAC__STREAM_METADATA_STREAMINFO_SAMPLE_RATE_LEN;

		if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &x, FLAC__STREAM_METADATA_STREAMINFO_CHANNELS_LEN, read_callback_, decoder))
			return false; /* the read_callback_ sets the state for us */
		decoder->private->stream_info.data.stream_info.channels = x+1;
		used_bits += FLAC__STREAM_METADATA_STREAMINFO_CHANNELS_LEN;

		if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &x, FLAC__STREAM_METADATA_STREAMINFO_BITS_PER_SAMPLE_LEN, read_callback_, decoder))
			return false; /* the read_callback_ sets the state for us */
		decoder->private->stream_info.data.stream_info.bits_per_sample = x+1;
		used_bits += FLAC__STREAM_METADATA_STREAMINFO_BITS_PER_SAMPLE_LEN;

		if(!FLAC__bitbuffer_read_raw_uint64(&decoder->private->input, &decoder->private->stream_info.data.stream_info.total_samples, FLAC__STREAM_METADATA_STREAMINFO_TOTAL_SAMPLES_LEN, read_callback_, decoder))
			return false; /* the read_callback_ sets the state for us */
		used_bits += FLAC__STREAM_METADATA_STREAMINFO_TOTAL_SAMPLES_LEN;

		for(i = 0; i < 16; i++) {
			if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &x, 8, read_callback_, decoder))
				return false; /* the read_callback_ sets the state for us */
			decoder->private->stream_info.data.stream_info.md5sum[i] = (byte)x;
		}
		used_bits += i*8;

		/* skip the rest of the block */
		FLAC__ASSERT(used_bits % 8 == 0);
		length -= (used_bits / 8);
		for(i = 0; i < length; i++) {
			if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &x, 8, read_callback_, decoder))
				return false; /* the read_callback_ sets the state for us */
		}

		decoder->private->has_stream_info = true;
		decoder->private->metadata_callback(decoder, &decoder->private->stream_info, decoder->private->client_data);
	}
	else if(type == FLAC__METADATA_TYPE_SEEKTABLE) {
		unsigned real_points;

		decoder->private->seek_table.type = type;
		decoder->private->seek_table.is_last = last_block;
		decoder->private->seek_table.length = length;

		decoder->private->seek_table.data.seek_table.num_points = length / FLAC__STREAM_METADATA_SEEKPOINT_LEN;

		if(0 == (decoder->private->seek_table.data.seek_table.points = (FLAC__StreamMetaData_SeekPoint*)malloc(decoder->private->seek_table.data.seek_table.num_points * sizeof(FLAC__StreamMetaData_SeekPoint)))) {
			decoder->protected->state = FLAC__STREAM_DECODER_MEMORY_ALLOCATION_ERROR;
			return false;
		}
		for(i = real_points = 0; i < decoder->private->seek_table.data.seek_table.num_points; i++) {
			if(!FLAC__bitbuffer_read_raw_uint64(&decoder->private->input, &xx, FLAC__STREAM_METADATA_SEEKPOINT_SAMPLE_NUMBER_LEN, read_callback_, decoder))
				return false; /* the read_callback_ sets the state for us */
			decoder->private->seek_table.data.seek_table.points[real_points].sample_number = xx;

			if(!FLAC__bitbuffer_read_raw_uint64(&decoder->private->input, &xx, FLAC__STREAM_METADATA_SEEKPOINT_STREAM_OFFSET_LEN, read_callback_, decoder))
				return false; /* the read_callback_ sets the state for us */
			decoder->private->seek_table.data.seek_table.points[real_points].stream_offset = xx;

			if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &x, FLAC__STREAM_METADATA_SEEKPOINT_FRAME_SAMPLES_LEN, read_callback_, decoder))
				return false; /* the read_callback_ sets the state for us */
			decoder->private->seek_table.data.seek_table.points[real_points].frame_samples = x;

			if(decoder->private->seek_table.data.seek_table.points[real_points].sample_number != FLAC__STREAM_METADATA_SEEKPOINT_PLACEHOLDER)
				real_points++;
		}
		decoder->private->seek_table.data.seek_table.num_points = real_points;

		decoder->private->has_seek_table = true;
		decoder->private->metadata_callback(decoder, &decoder->private->seek_table, decoder->private->client_data);
	}
	else {
		/* skip other metadata blocks */
		for(i = 0; i < length; i++) {
			if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &x, 8, read_callback_, decoder))
				return false; /* the read_callback_ sets the state for us */
		}
	}

	if(last_block)
		decoder->protected->state = FLAC__STREAM_DECODER_SEARCH_FOR_FRAME_SYNC;

	return true;
}

bool stream_decoder_skip_id3v2_tag_(FLAC__StreamDecoder *decoder)
{
	uint32 x;
	unsigned i, skip;

	/* skip the version and flags bytes */
	if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &x, 24, read_callback_, decoder))
		return false; /* the read_callback_ sets the state for us */
	/* get the size (in bytes) to skip */
	skip = 0;
	for(i = 0; i < 4; i++) {
		if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &x, 8, read_callback_, decoder))
			return false; /* the read_callback_ sets the state for us */
		skip <<= 7;
		skip |= (x & 0x7f);
	}
	/* skip the rest of the tag */
	for(i = 0; i < skip; i++) {
		if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &x, 8, read_callback_, decoder))
			return false; /* the read_callback_ sets the state for us */
	}
	return true;
}

bool stream_decoder_frame_sync_(FLAC__StreamDecoder *decoder)
{
	uint32 x;
	bool first = true;

	/* If we know the total number of samples in the stream, stop if we've read that many. */
	/* This will stop us, for example, from wasting time trying to sync on an ID3V1 tag. */
	if(decoder->private->has_stream_info && decoder->private->stream_info.data.stream_info.total_samples) {
		if(decoder->private->samples_decoded >= decoder->private->stream_info.data.stream_info.total_samples) {
			decoder->protected->state = FLAC__STREAM_DECODER_END_OF_STREAM;
			return true;
		}
	}

	/* make sure we're byte aligned */
	if(decoder->private->input.consumed_bits != 0) {
		if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &x, 8-decoder->private->input.consumed_bits, read_callback_, decoder))
			return false; /* the read_callback_ sets the state for us */
	}

	while(1) {
		if(decoder->private->cached) {
			x = (uint32)decoder->private->lookahead;
			decoder->private->cached = false;
		}
		else {
			if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &x, 8, read_callback_, decoder))
				return false; /* the read_callback_ sets the state for us */
		}
		if(x == 0xff) { /* MAGIC NUMBER for the first 8 frame sync bits */
			decoder->private->header_warmup[0] = (byte)x;
			if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &x, 8, read_callback_, decoder))
				return false; /* the read_callback_ sets the state for us */

			/* we have to check if we just read two 0xff's in a row; the second may actually be the beginning of the sync code */
			/* else we have to check if the second byte is the end of a sync code */
			if(x == 0xff) { /* MAGIC NUMBER for the first 8 frame sync bits */
				decoder->private->lookahead = (byte)x;
				decoder->private->cached = true;
			}
			else if(x >> 2 == 0x3e) { /* MAGIC NUMBER for the last 6 sync bits */
				decoder->private->header_warmup[1] = (byte)x;
				decoder->protected->state = FLAC__STREAM_DECODER_READ_FRAME;
				return true;
			}
		}
		if(first) {
			decoder->private->error_callback(decoder, FLAC__STREAM_DECODER_ERROR_LOST_SYNC, decoder->private->client_data);
			first = 0;
		}
	}

	return true;
}

bool stream_decoder_read_frame_(FLAC__StreamDecoder *decoder, bool *got_a_frame)
{
	unsigned channel;
	unsigned i;
	int32 mid, side, left, right;
	uint16 frame_crc; /* the one we calculate from the input stream */
	uint32 x;

	*got_a_frame = false;

	/* init the CRC */
	frame_crc = 0;
	FLAC__CRC16_UPDATE(decoder->private->header_warmup[0], frame_crc);
	FLAC__CRC16_UPDATE(decoder->private->header_warmup[1], frame_crc);
	FLAC__bitbuffer_init_read_crc16(&decoder->private->input, frame_crc);

	if(!stream_decoder_read_frame_header_(decoder))
		return false;
	if(decoder->protected->state == FLAC__STREAM_DECODER_SEARCH_FOR_FRAME_SYNC)
		return true;
	if(!stream_decoder_allocate_output_(decoder, decoder->private->frame.header.blocksize, decoder->private->frame.header.channels))
		return false;
	for(channel = 0; channel < decoder->private->frame.header.channels; channel++) {
		/*
		 * first figure the correct bits-per-sample of the subframe
		 */
		unsigned bps = decoder->private->frame.header.bits_per_sample;
		switch(decoder->private->frame.header.channel_assignment) {
			case FLAC__CHANNEL_ASSIGNMENT_INDEPENDENT:
				/* no adjustment needed */
				break;
			case FLAC__CHANNEL_ASSIGNMENT_LEFT_SIDE:
				FLAC__ASSERT(decoder->private->frame.header.channels == 2);
				if(channel == 1)
					bps++;
				break;
			case FLAC__CHANNEL_ASSIGNMENT_RIGHT_SIDE:
				FLAC__ASSERT(decoder->private->frame.header.channels == 2);
				if(channel == 0)
					bps++;
				break;
			case FLAC__CHANNEL_ASSIGNMENT_MID_SIDE:
				FLAC__ASSERT(decoder->private->frame.header.channels == 2);
				if(channel == 1)
					bps++;
				break;
			default:
				FLAC__ASSERT(0);
		}
		/*
		 * now read it
		 */
		if(!stream_decoder_read_subframe_(decoder, channel, bps))
			return false;
		if(decoder->protected->state != FLAC__STREAM_DECODER_READ_FRAME) {
			decoder->protected->state = FLAC__STREAM_DECODER_SEARCH_FOR_FRAME_SYNC;
			return true;
		}
	}
	if(!stream_decoder_read_zero_padding_(decoder))
		return false;

	/*
	 * Read the frame CRC-16 from the footer and check
	 */
	frame_crc = decoder->private->input.read_crc16;
	if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &x, FLAC__FRAME_FOOTER_CRC_LEN, read_callback_, decoder))
		return false; /* the read_callback_ sets the state for us */
	if(frame_crc == (uint16)x) {
		/* Undo any special channel coding */
		switch(decoder->private->frame.header.channel_assignment) {
			case FLAC__CHANNEL_ASSIGNMENT_INDEPENDENT:
				/* do nothing */
				break;
			case FLAC__CHANNEL_ASSIGNMENT_LEFT_SIDE:
				FLAC__ASSERT(decoder->private->frame.header.channels == 2);
				for(i = 0; i < decoder->private->frame.header.blocksize; i++)
					decoder->private->output[1][i] = decoder->private->output[0][i] - decoder->private->output[1][i];
				break;
			case FLAC__CHANNEL_ASSIGNMENT_RIGHT_SIDE:
				FLAC__ASSERT(decoder->private->frame.header.channels == 2);
				for(i = 0; i < decoder->private->frame.header.blocksize; i++)
					decoder->private->output[0][i] += decoder->private->output[1][i];
				break;
			case FLAC__CHANNEL_ASSIGNMENT_MID_SIDE:
				FLAC__ASSERT(decoder->private->frame.header.channels == 2);
				for(i = 0; i < decoder->private->frame.header.blocksize; i++) {
					mid = decoder->private->output[0][i];
					side = decoder->private->output[1][i];
					mid <<= 1;
					if(side & 1) /* i.e. if 'side' is odd... */
						mid++;
					left = mid + side;
					right = mid - side;
					decoder->private->output[0][i] = left >> 1;
					decoder->private->output[1][i] = right >> 1;
				}
				break;
			default:
				FLAC__ASSERT(0);
				break;
		}
	}
	else {
		/* Bad frame, emit error and zero the output signal */
		decoder->private->error_callback(decoder, FLAC__STREAM_DECODER_ERROR_FRAME_CRC_MISMATCH, decoder->private->client_data);
		for(channel = 0; channel < decoder->private->frame.header.channels; channel++) {
			memset(decoder->private->output[channel], 0, sizeof(int32) * decoder->private->frame.header.blocksize);
		}
	}

	*got_a_frame = true;

	/* put the latest values into the public section of the decoder instance */
	decoder->protected->channels = decoder->private->frame.header.channels;
	decoder->protected->channel_assignment = decoder->private->frame.header.channel_assignment;
	decoder->protected->bits_per_sample = decoder->private->frame.header.bits_per_sample;
	decoder->protected->sample_rate = decoder->private->frame.header.sample_rate;
	decoder->protected->blocksize = decoder->private->frame.header.blocksize;

	decoder->private->samples_decoded = decoder->private->frame.header.number.sample_number + decoder->private->frame.header.blocksize;

	/* write it */
	/* NOTE: some versions of GCC can't figure out const-ness right and will give you an 'incompatible pointer type' warning on arg 3 here: */
	if(decoder->private->write_callback(decoder, &decoder->private->frame, decoder->private->output, decoder->private->client_data) != FLAC__STREAM_DECODER_WRITE_CONTINUE)
		return false;

	decoder->protected->state = FLAC__STREAM_DECODER_SEARCH_FOR_FRAME_SYNC;
	return true;
}

bool stream_decoder_read_frame_header_(FLAC__StreamDecoder *decoder)
{
	uint32 x;
	uint64 xx;
	unsigned i, blocksize_hint = 0, sample_rate_hint = 0;
	byte crc8, raw_header[16]; /* MAGIC NUMBER based on the maximum frame header size, including CRC */
	unsigned raw_header_len;
	bool is_unparseable = false;
	const bool is_known_variable_blocksize_stream = (decoder->private->has_stream_info && decoder->private->stream_info.data.stream_info.min_blocksize != decoder->private->stream_info.data.stream_info.max_blocksize);
	const bool is_known_fixed_blocksize_stream = (decoder->private->has_stream_info && decoder->private->stream_info.data.stream_info.min_blocksize == decoder->private->stream_info.data.stream_info.max_blocksize);

	FLAC__ASSERT(decoder->private->input.consumed_bits == 0); /* make sure we're byte aligned */

	/* init the raw header with the saved bits from synchronization */
	raw_header[0] = decoder->private->header_warmup[0];
	raw_header[1] = decoder->private->header_warmup[1];
	raw_header_len = 2;

	/*
	 * check to make sure that the reserved bits are 0
	 */
	if(raw_header[1] & 0x03) { /* MAGIC NUMBER */
		is_unparseable = true;
	}

	/*
	 * Note that along the way as we read the header, we look for a sync
	 * code inside.  If we find one it would indicate that our original
	 * sync was bad since there cannot be a sync code in a valid header.
	 */

	/*
	 * read in the raw header as bytes so we can CRC it, and parse it on the way
	 */
	for(i = 0; i < 2; i++) {
		if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &x, 8, read_callback_, decoder))
			return false; /* the read_callback_ sets the state for us */
		if(x == 0xff) { /* MAGIC NUMBER for the first 8 frame sync bits */
			/* if we get here it means our original sync was erroneous since the sync code cannot appear in the header */
			decoder->private->lookahead = (byte)x;
			decoder->private->cached = true;
			decoder->private->error_callback(decoder, FLAC__STREAM_DECODER_ERROR_BAD_HEADER, decoder->private->client_data);
			decoder->protected->state = FLAC__STREAM_DECODER_SEARCH_FOR_FRAME_SYNC;
			return true;
		}
		raw_header[raw_header_len++] = (byte)x;
	}

	switch(x = raw_header[2] >> 4) {
		case 0:
			if(is_known_fixed_blocksize_stream)
				decoder->private->frame.header.blocksize = decoder->private->stream_info.data.stream_info.min_blocksize;
			else
				is_unparseable = true;
			break;
		case 1:
			decoder->private->frame.header.blocksize = 192;
			break;
		case 2:
		case 3:
		case 4:
		case 5:
			decoder->private->frame.header.blocksize = 576 << (x-2);
			break;
		case 6:
		case 7:
			blocksize_hint = x;
			break;
		case 8:
		case 9:
		case 10:
		case 11:
		case 12:
		case 13:
		case 14:
		case 15:
			decoder->private->frame.header.blocksize = 256 << (x-8);
			break;
		default:
			FLAC__ASSERT(0);
			break;
	}

	switch(x = raw_header[2] & 0x0f) {
		case 0:
			if(decoder->private->has_stream_info)
				decoder->private->frame.header.sample_rate = decoder->private->stream_info.data.stream_info.sample_rate;
			else
				is_unparseable = true;
			break;
		case 1:
		case 2:
		case 3:
			is_unparseable = true;
			break;
		case 4:
			decoder->private->frame.header.sample_rate = 8000;
			break;
		case 5:
			decoder->private->frame.header.sample_rate = 16000;
			break;
		case 6:
			decoder->private->frame.header.sample_rate = 22050;
			break;
		case 7:
			decoder->private->frame.header.sample_rate = 24000;
			break;
		case 8:
			decoder->private->frame.header.sample_rate = 32000;
			break;
		case 9:
			decoder->private->frame.header.sample_rate = 44100;
			break;
		case 10:
			decoder->private->frame.header.sample_rate = 48000;
			break;
		case 11:
			decoder->private->frame.header.sample_rate = 96000;
			break;
		case 12:
		case 13:
		case 14:
			sample_rate_hint = x;
			break;
		case 15:
			decoder->private->error_callback(decoder, FLAC__STREAM_DECODER_ERROR_BAD_HEADER, decoder->private->client_data);
			decoder->protected->state = FLAC__STREAM_DECODER_SEARCH_FOR_FRAME_SYNC;
			return true;
		default:
			FLAC__ASSERT(0);
	}

	x = (unsigned)(raw_header[3] >> 4);
	if(x & 8) {
		decoder->private->frame.header.channels = 2;
		switch(x & 7) {
			case 0:
				decoder->private->frame.header.channel_assignment = FLAC__CHANNEL_ASSIGNMENT_LEFT_SIDE;
				break;
			case 1:
				decoder->private->frame.header.channel_assignment = FLAC__CHANNEL_ASSIGNMENT_RIGHT_SIDE;
				break;
			case 2:
				decoder->private->frame.header.channel_assignment = FLAC__CHANNEL_ASSIGNMENT_MID_SIDE;
				break;
			default:
				is_unparseable = true;
				break;
		}
	}
	else {
		decoder->private->frame.header.channels = (unsigned)x + 1;
		decoder->private->frame.header.channel_assignment = FLAC__CHANNEL_ASSIGNMENT_INDEPENDENT;
	}

	switch(x = (unsigned)(raw_header[3] & 0x0e) >> 1) {
		case 0:
			if(decoder->private->has_stream_info)
				decoder->private->frame.header.bits_per_sample = decoder->private->stream_info.data.stream_info.bits_per_sample;
			else
				is_unparseable = true;
			break;
		case 1:
			decoder->private->frame.header.bits_per_sample = 8;
			break;
		case 2:
			decoder->private->frame.header.bits_per_sample = 12;
			break;
		case 4:
			decoder->private->frame.header.bits_per_sample = 16;
			break;
		case 5:
			decoder->private->frame.header.bits_per_sample = 20;
			break;
		case 6:
			decoder->private->frame.header.bits_per_sample = 24;
			break;
		case 3:
		case 7:
			is_unparseable = true;
			break;
		default:
			FLAC__ASSERT(0);
			break;
	}

	if(raw_header[3] & 0x01) { /* this should be a zero padding bit */
		decoder->private->error_callback(decoder, FLAC__STREAM_DECODER_ERROR_BAD_HEADER, decoder->private->client_data);
		decoder->protected->state = FLAC__STREAM_DECODER_SEARCH_FOR_FRAME_SYNC;
		return true;
	}

	if(blocksize_hint && is_known_variable_blocksize_stream) {
		if(!FLAC__bitbuffer_read_utf8_uint64(&decoder->private->input, &xx, read_callback_, decoder, raw_header, &raw_header_len))
			return false; /* the read_callback_ sets the state for us */
		if(xx == 0xffffffffffffffff) { /* i.e. non-UTF8 code... */
			decoder->private->lookahead = raw_header[raw_header_len-1]; /* back up as much as we can */
			decoder->private->cached = true;
			decoder->private->error_callback(decoder, FLAC__STREAM_DECODER_ERROR_BAD_HEADER, decoder->private->client_data);
			decoder->protected->state = FLAC__STREAM_DECODER_SEARCH_FOR_FRAME_SYNC;
			return true;
		}
		decoder->private->frame.header.number.sample_number = xx;
	}
	else {
		if(!FLAC__bitbuffer_read_utf8_uint32(&decoder->private->input, &x, read_callback_, decoder, raw_header, &raw_header_len))
			return false; /* the read_callback_ sets the state for us */
		if(x == 0xffffffff) { /* i.e. non-UTF8 code... */
			decoder->private->lookahead = raw_header[raw_header_len-1]; /* back up as much as we can */
			decoder->private->cached = true;
			decoder->private->error_callback(decoder, FLAC__STREAM_DECODER_ERROR_BAD_HEADER, decoder->private->client_data);
			decoder->protected->state = FLAC__STREAM_DECODER_SEARCH_FOR_FRAME_SYNC;
			return true;
		}
		decoder->private->last_frame_number = x;
		if(decoder->private->has_stream_info) {
			decoder->private->frame.header.number.sample_number = (int64)decoder->private->stream_info.data.stream_info.min_blocksize * (int64)x;
		}
		else {
			is_unparseable = true;
		}
	}

	if(blocksize_hint) {
		if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &x, 8, read_callback_, decoder))
			return false; /* the read_callback_ sets the state for us */
		raw_header[raw_header_len++] = (byte)x;
		if(blocksize_hint == 7) {
			uint32 _x;
			if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &_x, 8, read_callback_, decoder))
				return false; /* the read_callback_ sets the state for us */
			raw_header[raw_header_len++] = (byte)_x;
			x = (x << 8) | _x;
		}
		decoder->private->frame.header.blocksize = x+1;
	}

	if(sample_rate_hint) {
		if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &x, 8, read_callback_, decoder))
			return false; /* the read_callback_ sets the state for us */
		raw_header[raw_header_len++] = (byte)x;
		if(sample_rate_hint != 12) {
			uint32 _x;
			if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &_x, 8, read_callback_, decoder))
				return false; /* the read_callback_ sets the state for us */
			raw_header[raw_header_len++] = (byte)_x;
			x = (x << 8) | _x;
		}
		if(sample_rate_hint == 12)
			decoder->private->frame.header.sample_rate = x*1000;
		else if(sample_rate_hint == 13)
			decoder->private->frame.header.sample_rate = x;
		else
			decoder->private->frame.header.sample_rate = x*10;
	}

	/* read the CRC-8 byte */
	if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &x, 8, read_callback_, decoder))
		return false; /* the read_callback_ sets the state for us */
	crc8 = (byte)x;

	if(FLAC__crc8(raw_header, raw_header_len) != crc8) {
		decoder->private->error_callback(decoder, FLAC__STREAM_DECODER_ERROR_BAD_HEADER, decoder->private->client_data);
		decoder->protected->state = FLAC__STREAM_DECODER_SEARCH_FOR_FRAME_SYNC;
		return true;
	}

	if(is_unparseable) {
		decoder->protected->state = FLAC__STREAM_DECODER_UNPARSEABLE_STREAM;
		return false;
	}

	return true;
}

bool stream_decoder_read_subframe_(FLAC__StreamDecoder *decoder, unsigned channel, unsigned bps)
{
	uint32 x;
	bool wasted_bits;

	if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &x, 8, read_callback_, decoder)) /* MAGIC NUMBER */
		return false; /* the read_callback_ sets the state for us */

	wasted_bits = (x & 1);
	x &= 0xfe;

	if(wasted_bits) {
		unsigned u;
		if(!FLAC__bitbuffer_read_unary_unsigned(&decoder->private->input, &u, read_callback_, decoder))
			return false; /* the read_callback_ sets the state for us */
		decoder->private->frame.subframes[channel].wasted_bits = u+1;
		bps -= decoder->private->frame.subframes[channel].wasted_bits;
	}
	else
		decoder->private->frame.subframes[channel].wasted_bits = 0;

	/*
	 * Lots of magic numbers here
	 */
	if(x & 0x80) {
		decoder->private->error_callback(decoder, FLAC__STREAM_DECODER_ERROR_LOST_SYNC, decoder->private->client_data);
		decoder->protected->state = FLAC__STREAM_DECODER_SEARCH_FOR_FRAME_SYNC;
		return true;
	}
	else if(x == 0) {
		if(!stream_decoder_read_subframe_constant_(decoder, channel, bps))
			return false;
	}
	else if(x == 2) {
		if(!stream_decoder_read_subframe_verbatim_(decoder, channel, bps))
			return false;
	}
	else if(x < 16) {
		decoder->protected->state = FLAC__STREAM_DECODER_UNPARSEABLE_STREAM;
		return false;
	}
	else if(x <= 24) {
		if(!stream_decoder_read_subframe_fixed_(decoder, channel, bps, (x>>1)&7))
			return false;
	}
	else if(x < 64) {
		decoder->protected->state = FLAC__STREAM_DECODER_UNPARSEABLE_STREAM;
		return false;
	}
	else {
		if(!stream_decoder_read_subframe_lpc_(decoder, channel, bps, ((x>>1)&31)+1))
			return false;
	}

	if(wasted_bits) {
		unsigned i;
		x = decoder->private->frame.subframes[channel].wasted_bits;
		for(i = 0; i < decoder->private->frame.header.blocksize; i++)
			decoder->private->output[channel][i] <<= x;
	}

	return true;
}

bool stream_decoder_read_subframe_constant_(FLAC__StreamDecoder *decoder, unsigned channel, unsigned bps)
{
	FLAC__Subframe_Constant *subframe = &decoder->private->frame.subframes[channel].data.constant;
	int32 x;
	unsigned i;
	int32 *output = decoder->private->output[channel];

	decoder->private->frame.subframes[channel].type = FLAC__SUBFRAME_TYPE_CONSTANT;

	if(!FLAC__bitbuffer_read_raw_int32(&decoder->private->input, &x, bps, read_callback_, decoder))
		return false; /* the read_callback_ sets the state for us */

	subframe->value = x;

	/* decode the subframe */
	for(i = 0; i < decoder->private->frame.header.blocksize; i++)
		output[i] = x;

	return true;
}

bool stream_decoder_read_subframe_fixed_(FLAC__StreamDecoder *decoder, unsigned channel, unsigned bps, const unsigned order)
{
	FLAC__Subframe_Fixed *subframe = &decoder->private->frame.subframes[channel].data.fixed;
	int32 i32;
	uint32 u32;
	unsigned u;

	decoder->private->frame.subframes[channel].type = FLAC__SUBFRAME_TYPE_FIXED;

	subframe->residual = decoder->private->residual[channel];
	subframe->order = order;

	/* read warm-up samples */
	for(u = 0; u < order; u++) {
		if(!FLAC__bitbuffer_read_raw_int32(&decoder->private->input, &i32, bps, read_callback_, decoder))
			return false; /* the read_callback_ sets the state for us */
		subframe->warmup[u] = i32;
	}

	/* read entropy coding method info */
	if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &u32, FLAC__ENTROPY_CODING_METHOD_TYPE_LEN, read_callback_, decoder))
		return false; /* the read_callback_ sets the state for us */
	subframe->entropy_coding_method.type = u32;
	switch(subframe->entropy_coding_method.type) {
		case FLAC__ENTROPY_CODING_METHOD_PARTITIONED_RICE:
			if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &u32, FLAC__ENTROPY_CODING_METHOD_PARTITIONED_RICE_ORDER_LEN, read_callback_, decoder))
				return false; /* the read_callback_ sets the state for us */
			subframe->entropy_coding_method.data.partitioned_rice.order = u32;
			break;
		default:
			decoder->protected->state = FLAC__STREAM_DECODER_UNPARSEABLE_STREAM;
			return false;
	}

	/* read residual */
	switch(subframe->entropy_coding_method.type) {
		case FLAC__ENTROPY_CODING_METHOD_PARTITIONED_RICE:
			if(!stream_decoder_read_residual_partitioned_rice_(decoder, order, subframe->entropy_coding_method.data.partitioned_rice.order, decoder->private->residual[channel]))
				return false;
			break;
		default:
			FLAC__ASSERT(0);
	}

	/* decode the subframe */
	memcpy(decoder->private->output[channel], subframe->warmup, sizeof(int32) * order);
	FLAC__fixed_restore_signal(decoder->private->residual[channel], decoder->private->frame.header.blocksize-order, order, decoder->private->output[channel]+order);

	return true;
}

bool stream_decoder_read_subframe_lpc_(FLAC__StreamDecoder *decoder, unsigned channel, unsigned bps, const unsigned order)
{
	FLAC__Subframe_LPC *subframe = &decoder->private->frame.subframes[channel].data.lpc;
	int32 i32;
	uint32 u32;
	unsigned u;

	decoder->private->frame.subframes[channel].type = FLAC__SUBFRAME_TYPE_LPC;

	subframe->residual = decoder->private->residual[channel];
	subframe->order = order;

	/* read warm-up samples */
	for(u = 0; u < order; u++) {
		if(!FLAC__bitbuffer_read_raw_int32(&decoder->private->input, &i32, bps, read_callback_, decoder))
			return false; /* the read_callback_ sets the state for us */
		subframe->warmup[u] = i32;
	}

	/* read qlp coeff precision */
	if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &u32, FLAC__SUBFRAME_LPC_QLP_COEFF_PRECISION_LEN, read_callback_, decoder))
		return false; /* the read_callback_ sets the state for us */
	if(u32 == (1u << FLAC__SUBFRAME_LPC_QLP_COEFF_PRECISION_LEN) - 1) {
		decoder->private->error_callback(decoder, FLAC__STREAM_DECODER_ERROR_LOST_SYNC, decoder->private->client_data);
		decoder->protected->state = FLAC__STREAM_DECODER_SEARCH_FOR_FRAME_SYNC;
		return true;
	}
	subframe->qlp_coeff_precision = u32+1;

	/* read qlp shift */
	if(!FLAC__bitbuffer_read_raw_int32(&decoder->private->input, &i32, FLAC__SUBFRAME_LPC_QLP_SHIFT_LEN, read_callback_, decoder))
		return false; /* the read_callback_ sets the state for us */
	subframe->quantization_level = i32;

	/* read quantized lp coefficiencts */
	for(u = 0; u < order; u++) {
		if(!FLAC__bitbuffer_read_raw_int32(&decoder->private->input, &i32, subframe->qlp_coeff_precision, read_callback_, decoder))
			return false; /* the read_callback_ sets the state for us */
		subframe->qlp_coeff[u] = i32;
	}

	/* read entropy coding method info */
	if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &u32, FLAC__ENTROPY_CODING_METHOD_TYPE_LEN, read_callback_, decoder))
		return false; /* the read_callback_ sets the state for us */
	subframe->entropy_coding_method.type = u32;
	switch(subframe->entropy_coding_method.type) {
		case FLAC__ENTROPY_CODING_METHOD_PARTITIONED_RICE:
			if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &u32, FLAC__ENTROPY_CODING_METHOD_PARTITIONED_RICE_ORDER_LEN, read_callback_, decoder))
				return false; /* the read_callback_ sets the state for us */
			subframe->entropy_coding_method.data.partitioned_rice.order = u32;
			break;
		default:
			decoder->protected->state = FLAC__STREAM_DECODER_UNPARSEABLE_STREAM;
			return false;
	}

	/* read residual */
	switch(subframe->entropy_coding_method.type) {
		case FLAC__ENTROPY_CODING_METHOD_PARTITIONED_RICE:
			if(!stream_decoder_read_residual_partitioned_rice_(decoder, order, subframe->entropy_coding_method.data.partitioned_rice.order, decoder->private->residual[channel]))
				return false;
			break;
		default:
			FLAC__ASSERT(0);
	}

	/* decode the subframe */
	memcpy(decoder->private->output[channel], subframe->warmup, sizeof(int32) * order);
	if(bps <= 16 && subframe->qlp_coeff_precision <= 16)
		decoder->private->local_lpc_restore_signal_16bit(decoder->private->residual[channel], decoder->private->frame.header.blocksize-order, subframe->qlp_coeff, order, subframe->quantization_level, decoder->private->output[channel]+order);
	else
		decoder->private->local_lpc_restore_signal(decoder->private->residual[channel], decoder->private->frame.header.blocksize-order, subframe->qlp_coeff, order, subframe->quantization_level, decoder->private->output[channel]+order);

	return true;
}

bool stream_decoder_read_subframe_verbatim_(FLAC__StreamDecoder *decoder, unsigned channel, unsigned bps)
{
	FLAC__Subframe_Verbatim *subframe = &decoder->private->frame.subframes[channel].data.verbatim;
	int32 x, *residual = decoder->private->residual[channel];
	unsigned i;

	decoder->private->frame.subframes[channel].type = FLAC__SUBFRAME_TYPE_VERBATIM;

	subframe->data = residual;

	for(i = 0; i < decoder->private->frame.header.blocksize; i++) {
		if(!FLAC__bitbuffer_read_raw_int32(&decoder->private->input, &x, bps, read_callback_, decoder))
			return false; /* the read_callback_ sets the state for us */
		residual[i] = x;
	}

	/* decode the subframe */
	memcpy(decoder->private->output[channel], subframe->data, sizeof(int32) * decoder->private->frame.header.blocksize);

	return true;
}

bool stream_decoder_read_residual_partitioned_rice_(FLAC__StreamDecoder *decoder, unsigned predictor_order, unsigned partition_order, int32 *residual)
{
	uint32 rice_parameter;
	int i;
	unsigned partition, sample, u;
	const unsigned partitions = 1u << partition_order;
	const unsigned partition_samples = partition_order > 0? decoder->private->frame.header.blocksize >> partition_order : decoder->private->frame.header.blocksize - predictor_order;

	sample = 0;
	for(partition = 0; partition < partitions; partition++) {
		if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &rice_parameter, FLAC__ENTROPY_CODING_METHOD_PARTITIONED_RICE_PARAMETER_LEN, read_callback_, decoder))
			return false; /* the read_callback_ sets the state for us */
		if(rice_parameter < FLAC__ENTROPY_CODING_METHOD_PARTITIONED_RICE_ESCAPE_PARAMETER) {
			for(u = (partition_order == 0 || partition > 0)? 0 : predictor_order; u < partition_samples; u++, sample++) {
#ifdef FLAC__SYMMETRIC_RICE
				if(!FLAC__bitbuffer_read_symmetric_rice_signed(&decoder->private->input, &i, rice_parameter, read_callback_, decoder))
					return false; /* the read_callback_ sets the state for us */
#else
				if(!FLAC__bitbuffer_read_rice_signed(&decoder->private->input, &i, rice_parameter, read_callback_, decoder))
					return false; /* the read_callback_ sets the state for us */
#endif
				residual[sample] = i;
			}
		}
		else {
			if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &rice_parameter, FLAC__ENTROPY_CODING_METHOD_PARTITIONED_RICE_RAW_LEN, read_callback_, decoder))
				return false; /* the read_callback_ sets the state for us */
			for(u = (partition_order == 0 || partition > 0)? 0 : predictor_order; u < partition_samples; u++, sample++) {
				if(!FLAC__bitbuffer_read_raw_int32(&decoder->private->input, &i, rice_parameter, read_callback_, decoder))
					return false; /* the read_callback_ sets the state for us */
				residual[sample] = i;
			}
		}
	}

	return true;
}

bool stream_decoder_read_zero_padding_(FLAC__StreamDecoder *decoder)
{
	if(decoder->private->input.consumed_bits != 0) {
		uint32 zero = 0;
		if(!FLAC__bitbuffer_read_raw_uint32(&decoder->private->input, &zero, 8-decoder->private->input.consumed_bits, read_callback_, decoder))
			return false; /* the read_callback_ sets the state for us */
		if(zero != 0) {
			decoder->private->error_callback(decoder, FLAC__STREAM_DECODER_ERROR_LOST_SYNC, decoder->private->client_data);
			decoder->protected->state = FLAC__STREAM_DECODER_SEARCH_FOR_FRAME_SYNC;
		}
	}
	return true;
}

bool read_callback_(byte buffer[], unsigned *bytes, void *client_data)
{
	FLAC__StreamDecoder *decoder = (FLAC__StreamDecoder *)client_data;
	FLAC__StreamDecoderReadStatus status;
	status = decoder->private->read_callback(decoder, buffer, bytes, decoder->private->client_data);
	if(status == FLAC__STREAM_DECODER_READ_END_OF_STREAM)
		decoder->protected->state = FLAC__STREAM_DECODER_END_OF_STREAM;
	else if(status == FLAC__STREAM_DECODER_READ_ABORT)
		decoder->protected->state = FLAC__STREAM_DECODER_ABORTED;
	return status == FLAC__STREAM_DECODER_READ_CONTINUE;
}
