/* libFLAC - Free Lossless Audio Coder library
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

#include <assert.h>
#include <stdio.h>
#include "private/encoder_framing.h"
#include "private/crc.h"

#ifdef max
#undef max
#endif
#define max(x,y) ((x)>(y)?(x):(y))

static bool subframe_add_entropy_coding_method_(FLAC__BitBuffer *bb, const FLAC__EntropyCodingMethod *method);
static bool subframe_add_residual_partitioned_rice_(FLAC__BitBuffer *bb, const int32 residual[], const unsigned residual_samples, const unsigned predictor_order, const unsigned rice_parameters[], const unsigned partition_order);

bool FLAC__add_metadata_block(const FLAC__StreamMetaData *metadata, FLAC__BitBuffer *bb)
{
	unsigned i;

	if(!FLAC__bitbuffer_write_raw_uint32(bb, metadata->is_last, FLAC__STREAM_METADATA_IS_LAST_LEN))
		return false;

	if(!FLAC__bitbuffer_write_raw_uint32(bb, metadata->type, FLAC__STREAM_METADATA_TYPE_LEN))
		return false;

	assert(metadata->length < (1u << FLAC__STREAM_METADATA_LENGTH_LEN));
	if(!FLAC__bitbuffer_write_raw_uint32(bb, metadata->length, FLAC__STREAM_METADATA_LENGTH_LEN))
		return false;

	switch(metadata->type) {
		case FLAC__METADATA_TYPE_ENCODING:
			assert(metadata->data.encoding.min_blocksize < (1u << FLAC__STREAM_METADATA_ENCODING_MIN_BLOCK_SIZE_LEN));
			if(!FLAC__bitbuffer_write_raw_uint32(bb, metadata->data.encoding.min_blocksize, FLAC__STREAM_METADATA_ENCODING_MIN_BLOCK_SIZE_LEN))
				return false;
			assert(metadata->data.encoding.max_blocksize < (1u << FLAC__STREAM_METADATA_ENCODING_MAX_BLOCK_SIZE_LEN));
			if(!FLAC__bitbuffer_write_raw_uint32(bb, metadata->data.encoding.max_blocksize, FLAC__STREAM_METADATA_ENCODING_MAX_BLOCK_SIZE_LEN))
				return false;
			assert(metadata->data.encoding.min_framesize < (1u << FLAC__STREAM_METADATA_ENCODING_MIN_FRAME_SIZE_LEN));
			if(!FLAC__bitbuffer_write_raw_uint32(bb, metadata->data.encoding.min_framesize, FLAC__STREAM_METADATA_ENCODING_MIN_FRAME_SIZE_LEN))
				return false;
			assert(metadata->data.encoding.max_framesize < (1u << FLAC__STREAM_METADATA_ENCODING_MAX_FRAME_SIZE_LEN));
			if(!FLAC__bitbuffer_write_raw_uint32(bb, metadata->data.encoding.max_framesize, FLAC__STREAM_METADATA_ENCODING_MAX_FRAME_SIZE_LEN))
				return false;
			assert(metadata->data.encoding.sample_rate > 0);
			assert(metadata->data.encoding.sample_rate < (1u << FLAC__STREAM_METADATA_ENCODING_SAMPLE_RATE_LEN));
			if(!FLAC__bitbuffer_write_raw_uint32(bb, metadata->data.encoding.sample_rate, FLAC__STREAM_METADATA_ENCODING_SAMPLE_RATE_LEN))
				return false;
			assert(metadata->data.encoding.channels > 0);
			assert(metadata->data.encoding.channels <= (1u << FLAC__STREAM_METADATA_ENCODING_CHANNELS_LEN));
			if(!FLAC__bitbuffer_write_raw_uint32(bb, metadata->data.encoding.channels-1, FLAC__STREAM_METADATA_ENCODING_CHANNELS_LEN))
				return false;
			assert(metadata->data.encoding.bits_per_sample > 0);
			assert(metadata->data.encoding.bits_per_sample <= (1u << FLAC__STREAM_METADATA_ENCODING_BITS_PER_SAMPLE_LEN));
			if(!FLAC__bitbuffer_write_raw_uint32(bb, metadata->data.encoding.bits_per_sample-1, FLAC__STREAM_METADATA_ENCODING_BITS_PER_SAMPLE_LEN))
				return false;
			if(!FLAC__bitbuffer_write_raw_uint64(bb, metadata->data.encoding.total_samples, FLAC__STREAM_METADATA_ENCODING_TOTAL_SAMPLES_LEN))
				return false;
			for(i = 0; i < 16; i++) {
				if(!FLAC__bitbuffer_write_raw_uint32(bb, metadata->data.encoding.md5sum[i], 8))
					return false;
			}
			break;
		default:
			assert(0);
	}

	return true;
}

bool FLAC__frame_add_header(const FLAC__FrameHeader *header, bool streamable_subset, bool is_last_block, FLAC__BitBuffer *bb)
{
	unsigned u, crc_start, blocksize_hint, sample_rate_hint;
	byte crc;

	assert(bb->bits == 0); /* assert that we're byte-aligned before writing */

	crc_start = bb->bytes;

	if(!FLAC__bitbuffer_write_raw_uint32(bb, FLAC__FRAME_HEADER_SYNC, FLAC__FRAME_HEADER_SYNC_LEN))
		return false;

	assert(header->blocksize > 0 && header->blocksize <= FLAC__MAX_BLOCK_SIZE);
	blocksize_hint = 0;
	switch(header->blocksize) {
		case  192: u = 1; break;
		case  576: u = 2; break;
		case 1152: u = 3; break;
		case 2304: u = 4; break;
		case 4608: u = 5; break;
		default:
			if(streamable_subset || is_last_block) {
				if(header->blocksize <= 0x100)
					blocksize_hint = u = 6;
				else
					blocksize_hint = u = 7;
			}
			else
				u = 0;
			break;
	}
	if(!FLAC__bitbuffer_write_raw_uint32(bb, u, FLAC__FRAME_HEADER_BLOCK_SIZE_LEN))
		return false;

	assert(header->sample_rate > 0 && header->sample_rate < (1u << FLAC__STREAM_METADATA_ENCODING_SAMPLE_RATE_LEN));
	sample_rate_hint = 0;
	switch(header->sample_rate) {
		case  8000: u = 4; break;
		case 16000: u = 5; break;
		case 22050: u = 6; break;
		case 24000: u = 7; break;
		case 32000: u = 8; break;
		case 44100: u = 9; break;
		case 48000: u = 10; break;
		case 96000: u = 11; break;
		default:
			if(streamable_subset) {
				if(header->sample_rate % 1000 == 0)
					sample_rate_hint = u = 12;
				else if(header->sample_rate % 10 == 0)
					sample_rate_hint = u = 14;
				else
					sample_rate_hint = u = 13;
			}
			else
				u = 0;
			break;
	}
	if(!FLAC__bitbuffer_write_raw_uint32(bb, u, FLAC__FRAME_HEADER_SAMPLE_RATE_LEN))
		return false;

	assert(header->channels > 0 && header->channels <= (1u << FLAC__STREAM_METADATA_ENCODING_CHANNELS_LEN) && header->channels <= FLAC__MAX_CHANNELS);
	switch(header->channel_assignment) {
		case FLAC__CHANNEL_ASSIGNMENT_INDEPENDENT:
			u = header->channels - 1;
			break;
		case FLAC__CHANNEL_ASSIGNMENT_LEFT_SIDE:
			assert(header->channels == 2);
			u = 8;
			break;
		case FLAC__CHANNEL_ASSIGNMENT_RIGHT_SIDE:
			assert(header->channels == 2);
			u = 9;
			break;
		case FLAC__CHANNEL_ASSIGNMENT_MID_SIDE:
			assert(header->channels == 2);
			u = 10;
			break;
		default:
			assert(0);
	}
	if(!FLAC__bitbuffer_write_raw_uint32(bb, u, FLAC__FRAME_HEADER_CHANNEL_ASSIGNMENT_LEN))
		return false;

	assert(header->bits_per_sample > 0 && header->bits_per_sample <= (1u << FLAC__STREAM_METADATA_ENCODING_BITS_PER_SAMPLE_LEN));
	switch(header->bits_per_sample) {
		case 8 : u = 1; break;
		case 12: u = 2; break;
		case 16: u = 4; break;
		case 20: u = 5; break;
		case 24: u = 6; break;
		default: u = 0; break;
	}
	if(!FLAC__bitbuffer_write_raw_uint32(bb, u, FLAC__FRAME_HEADER_BITS_PER_SAMPLE_LEN))
		return false;

	if(!FLAC__bitbuffer_write_raw_uint32(bb, 0, FLAC__FRAME_HEADER_ZERO_PAD_LEN))
		return false;

	if(!FLAC__bitbuffer_write_utf8_uint32(bb, header->number.frame_number))
		return false;

	if(blocksize_hint)
		if(!FLAC__bitbuffer_write_raw_uint32(bb, header->blocksize-1, (blocksize_hint==6)? 8:16))
			return false;

	switch(sample_rate_hint) {
		case 12:
			if(!FLAC__bitbuffer_write_raw_uint32(bb, header->sample_rate / 1000, 8))
				return false;
			break;
		case 13:
			if(!FLAC__bitbuffer_write_raw_uint32(bb, header->sample_rate, 16))
				return false;
			break;
		case 14:
			if(!FLAC__bitbuffer_write_raw_uint32(bb, header->sample_rate / 10, 16))
				return false;
			break;
	}

	/* write the CRC */
	assert(bb->buffer[crc_start] == 0xff); /* MAGIC NUMBER for the first byte of the sync code */
	assert(bb->bits == 0); /* assert that we're byte-aligned */
	crc = FLAC__crc8(bb->buffer+crc_start, bb->bytes-crc_start);
	if(!FLAC__bitbuffer_write_raw_uint32(bb, crc, FLAC__FRAME_HEADER_CRC8_LEN))
		return false;

	return true;
}

bool FLAC__subframe_add_constant(const FLAC__Subframe_Constant *subframe, unsigned bits_per_sample, FLAC__BitBuffer *bb)
{
	bool ok;

	ok =
		FLAC__bitbuffer_write_raw_uint32(bb, FLAC__SUBFRAME_TYPE_CONSTANT_BITS, FLAC__SUBFRAME_TYPE_LEN) &&
		FLAC__bitbuffer_write_raw_int32(bb, subframe->value, bits_per_sample)
	;

	return ok;
}

bool FLAC__subframe_add_fixed(const FLAC__Subframe_Fixed *subframe, unsigned residual_samples, unsigned bits_per_sample, FLAC__BitBuffer *bb)
{
	unsigned i;

	if(!FLAC__bitbuffer_write_raw_uint32(bb, FLAC__SUBFRAME_TYPE_FIXED_BITS | (subframe->order<<1), FLAC__SUBFRAME_TYPE_LEN))
		return false;

	for(i = 0; i < subframe->order; i++)
		if(!FLAC__bitbuffer_write_raw_int32(bb, subframe->warmup[i], bits_per_sample))
			return false;

	if(!subframe_add_entropy_coding_method_(bb, &subframe->entropy_coding_method))
		return false;
	switch(subframe->entropy_coding_method.type) {
		case FLAC__ENTROPY_CODING_METHOD_PARTITIONED_RICE:
			if(!subframe_add_residual_partitioned_rice_(bb, subframe->residual, residual_samples, subframe->order, subframe->entropy_coding_method.data.partitioned_rice.parameters, subframe->entropy_coding_method.data.partitioned_rice.order))
				return false;
			break;
		default:
			assert(0);
	}

	return true;
}

bool FLAC__subframe_add_lpc(const FLAC__Subframe_LPC *subframe, unsigned residual_samples, unsigned bits_per_sample, FLAC__BitBuffer *bb)
{
	unsigned i;

	if(!FLAC__bitbuffer_write_raw_uint32(bb, FLAC__SUBFRAME_TYPE_LPC_BITS | ((subframe->order-1)<<1), FLAC__SUBFRAME_TYPE_LEN))
		return false;

	for(i = 0; i < subframe->order; i++)
		if(!FLAC__bitbuffer_write_raw_int32(bb, subframe->warmup[i], bits_per_sample))
			return false;

	if(!FLAC__bitbuffer_write_raw_uint32(bb, subframe->qlp_coeff_precision-1, FLAC__SUBFRAME_LPC_QLP_COEFF_PRECISION_LEN))
		return false;
	if(!FLAC__bitbuffer_write_raw_int32(bb, subframe->quantization_level, FLAC__SUBFRAME_LPC_QLP_SHIFT_LEN))
		return false;
	for(i = 0; i < subframe->order; i++)
		if(!FLAC__bitbuffer_write_raw_int32(bb, subframe->qlp_coeff[i], subframe->qlp_coeff_precision))
			return false;

	if(!subframe_add_entropy_coding_method_(bb, &subframe->entropy_coding_method))
		return false;
	switch(subframe->entropy_coding_method.type) {
		case FLAC__ENTROPY_CODING_METHOD_PARTITIONED_RICE:
			if(!subframe_add_residual_partitioned_rice_(bb, subframe->residual, residual_samples, subframe->order, subframe->entropy_coding_method.data.partitioned_rice.parameters, subframe->entropy_coding_method.data.partitioned_rice.order))
				return false;
			break;
		default:
			assert(0);
	}

	return true;
}

bool FLAC__subframe_add_verbatim(const FLAC__Subframe_Verbatim *subframe, unsigned samples, unsigned bits_per_sample, FLAC__BitBuffer *bb)
{
	unsigned i;
	const int32 *signal = subframe->data;

	if(!FLAC__bitbuffer_write_raw_uint32(bb, FLAC__SUBFRAME_TYPE_VERBATIM_BITS, FLAC__SUBFRAME_TYPE_LEN))
		return false;

	for(i = 0; i < samples; i++)
		if(!FLAC__bitbuffer_write_raw_int32(bb, signal[i], bits_per_sample))
			return false;

	return true;
}

bool subframe_add_entropy_coding_method_(FLAC__BitBuffer *bb, const FLAC__EntropyCodingMethod *method)
{
	if(!FLAC__bitbuffer_write_raw_uint32(bb, method->type, FLAC__ENTROPY_CODING_METHOD_TYPE_LEN))
		return false;
	switch(method->type) {
		case FLAC__ENTROPY_CODING_METHOD_PARTITIONED_RICE:
			if(!FLAC__bitbuffer_write_raw_uint32(bb, method->data.partitioned_rice.order, FLAC__ENTROPY_CODING_METHOD_PARTITIONED_RICE_ORDER_LEN))
				return false;
			break;
		default:
			assert(0);
	}
	return true;
}

bool subframe_add_residual_partitioned_rice_(FLAC__BitBuffer *bb, const int32 residual[], const unsigned residual_samples, const unsigned predictor_order, const unsigned rice_parameters[], const unsigned partition_order)
{
	if(partition_order == 0) {
		unsigned i;
		if(!FLAC__bitbuffer_write_raw_uint32(bb, rice_parameters[0], FLAC__ENTROPY_CODING_METHOD_PARTITIONED_RICE_PARAMETER_LEN))
			return false;
		for(i = 0; i < residual_samples; i++) {
			if(!FLAC__bitbuffer_write_rice_signed(bb, residual[i], rice_parameters[0]))
				return false;
		}
		return true;
	}
	else {
		unsigned i, j, k = 0, k_last = 0;
		unsigned partition_samples;
		for(i = 0; i < (1u<<partition_order); i++) {
			if(!FLAC__bitbuffer_write_raw_uint32(bb, rice_parameters[i], FLAC__ENTROPY_CODING_METHOD_PARTITIONED_RICE_PARAMETER_LEN))
				return false;
			partition_samples = (residual_samples+predictor_order) >> partition_order;
			if(i == 0)
				partition_samples -= predictor_order;
			k += partition_samples;
			for(j = k_last; j < k; j++)
				if(!FLAC__bitbuffer_write_rice_signed(bb, residual[j], rice_parameters[i]))
					return false;
			k_last = k;
		}
		return true;
	}
}
