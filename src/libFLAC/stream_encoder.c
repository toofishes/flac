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
#include <string.h> /* for memcpy() */
#include "FLAC/assert.h"
#include "FLAC/seek_table.h"
#include "protected/stream_encoder.h"
#include "private/bitbuffer.h"
#include "private/bitmath.h"
#include "private/crc.h"
#include "private/cpu.h"
#include "private/stream_encoder_framing.h"
#include "private/fixed.h"
#include "private/lpc.h"
#include "private/md5.h"
#include "private/memory.h"

#ifdef min
#undef min
#endif
#define min(x,y) ((x)<(y)?(x):(y))

#ifdef max
#undef max
#endif
#define max(x,y) ((x)>(y)?(x):(y))

/***********************************************************************
 *
 * Private class method prototypes
 *
 ***********************************************************************/

static bool stream_encoder_resize_buffers_(FLAC__StreamEncoder *encoder, unsigned new_size);
static bool stream_encoder_process_frame_(FLAC__StreamEncoder *encoder, bool is_last_frame);
static bool stream_encoder_process_subframes_(FLAC__StreamEncoder *encoder, bool is_last_frame);
static bool stream_encoder_process_subframe_(FLAC__StreamEncoder *encoder, unsigned min_partition_order, unsigned max_partition_order, bool verbatim_only, const FLAC__FrameHeader *frame_header, unsigned subframe_bps, const int32 integer_signal[], const real real_signal[], FLAC__Subframe *subframe[2], int32 *residual[2], unsigned *best_subframe, unsigned *best_bits);
static bool stream_encoder_add_subframe_(FLAC__StreamEncoder *encoder, const FLAC__FrameHeader *frame_header, unsigned subframe_bps, const FLAC__Subframe *subframe, FLAC__BitBuffer *frame);
static unsigned stream_encoder_evaluate_constant_subframe_(const int32 signal, unsigned subframe_bps, FLAC__Subframe *subframe);
static unsigned stream_encoder_evaluate_fixed_subframe_(const int32 signal[], int32 residual[], uint32 abs_residual[], uint32 abs_residual_partition_sums[], unsigned raw_bits_per_partition[], unsigned blocksize, unsigned subframe_bps, unsigned order, unsigned rice_parameter, unsigned min_partition_order, unsigned max_partition_order, unsigned rice_parameter_search_dist, FLAC__Subframe *subframe);
static unsigned stream_encoder_evaluate_lpc_subframe_(FLAC__StreamEncoder *encoder, const int32 signal[], int32 residual[], uint32 abs_residual[], uint32 abs_residual_partition_sums[], unsigned raw_bits_per_partition[], const real lp_coeff[], unsigned blocksize, unsigned subframe_bps, unsigned order, unsigned qlp_coeff_precision, unsigned rice_parameter, unsigned min_partition_order, unsigned max_partition_order, unsigned rice_parameter_search_dist, FLAC__Subframe *subframe);
static unsigned stream_encoder_evaluate_verbatim_subframe_(const int32 signal[], unsigned blocksize, unsigned subframe_bps, FLAC__Subframe *subframe);
static unsigned stream_encoder_find_best_partition_order_(const int32 residual[], uint32 abs_residual[], uint32 abs_residual_partition_sums[], unsigned raw_bits_per_partition[], unsigned residual_samples, unsigned predictor_order, unsigned rice_parameter, unsigned min_partition_order, unsigned max_partition_order, unsigned rice_parameter_search_dist, unsigned *best_partition_order, unsigned best_parameters[], unsigned best_raw_bits[]);
#if (defined FLAC__PRECOMPUTE_PARTITION_SUMS) || (defined FLAC__SEARCH_FOR_ESCAPES)
static unsigned stream_encoder_precompute_partition_info_(const int32 residual[], uint32 abs_residual[], uint32 abs_residual_partition_sums[], unsigned raw_bits_per_partition[], unsigned residual_samples, unsigned predictor_order, unsigned min_partition_order, unsigned max_partition_order);
#endif
static bool stream_encoder_set_partitioned_rice_(const uint32 abs_residual[], const uint32 abs_residual_partition_sums[], const unsigned raw_bits_per_partition[], const unsigned residual_samples, const unsigned predictor_order, const unsigned suggested_rice_parameter, const unsigned rice_parameter_search_dist, const unsigned partition_order, unsigned parameters[], unsigned raw_bits[], unsigned *bits);
static unsigned stream_encoder_get_wasted_bits_(int32 signal[], unsigned samples);

/***********************************************************************
 *
 * Private class data
 *
 ***********************************************************************/

typedef struct FLAC__StreamEncoderPrivate {
	unsigned input_capacity;                    /* current size (in samples) of the signal and residual buffers */
	int32 *integer_signal[FLAC__MAX_CHANNELS];  /* the integer version of the input signal */
	int32 *integer_signal_mid_side[2];          /* the integer version of the mid-side input signal (stereo only) */
	real *real_signal[FLAC__MAX_CHANNELS];      /* the floating-point version of the input signal */
	real *real_signal_mid_side[2];              /* the floating-point version of the mid-side input signal (stereo only) */
	unsigned subframe_bps[FLAC__MAX_CHANNELS];  /* the effective bits per sample of the input signal (stream bps - wasted bits) */
	unsigned subframe_bps_mid_side[2];          /* the effective bits per sample of the mid-side input signal (stream bps - wasted bits + 0/1) */
	int32 *residual_workspace[FLAC__MAX_CHANNELS][2]; /* each channel has a candidate and best workspace where the subframe residual signals will be stored */
	int32 *residual_workspace_mid_side[2][2];
	FLAC__Subframe subframe_workspace[FLAC__MAX_CHANNELS][2];
	FLAC__Subframe subframe_workspace_mid_side[2][2];
	FLAC__Subframe *subframe_workspace_ptr[FLAC__MAX_CHANNELS][2];
	FLAC__Subframe *subframe_workspace_ptr_mid_side[2][2];
	unsigned best_subframe[FLAC__MAX_CHANNELS]; /* index into the above workspaces */
	unsigned best_subframe_mid_side[2];
	unsigned best_subframe_bits[FLAC__MAX_CHANNELS]; /* size in bits of the best subframe for each channel */
	unsigned best_subframe_bits_mid_side[2];
	uint32 *abs_residual;                       /* workspace where abs(candidate residual) is stored */
	uint32 *abs_residual_partition_sums;        /* workspace where the sum of abs(candidate residual) for each partition is stored */
	unsigned *raw_bits_per_partition;           /* workspace where the sum of silog2(candidate residual) for each partition is stored */
	FLAC__BitBuffer frame;                      /* the current frame being worked on */
	double loose_mid_side_stereo_frames_exact;  /* exact number of frames the encoder will use before trying both independent and mid/side frames again */
	unsigned loose_mid_side_stereo_frames;      /* rounded number of frames the encoder will use before trying both independent and mid/side frames again */
	unsigned loose_mid_side_stereo_frame_count; /* number of frames using the current channel assignment */
	FLAC__ChannelAssignment last_channel_assignment;
	FLAC__StreamMetaData metadata;
	unsigned current_sample_number;
	unsigned current_frame_number;
	struct MD5Context md5context;
	FLAC__CPUInfo cpuinfo;
	unsigned (*local_fixed_compute_best_predictor)(const int32 data[], unsigned data_len, real residual_bits_per_sample[FLAC__MAX_FIXED_ORDER+1]);
	void (*local_lpc_compute_autocorrelation)(const real data[], unsigned data_len, unsigned lag, real autoc[]);
	void (*local_lpc_compute_residual_from_qlp_coefficients)(const int32 data[], unsigned data_len, const int32 qlp_coeff[], unsigned order, int lp_quantization, int32 residual[]);
	void (*local_lpc_compute_residual_from_qlp_coefficients_16bit)(const int32 data[], unsigned data_len, const int32 qlp_coeff[], unsigned order, int lp_quantization, int32 residual[]);
	bool use_slow;                              /* use slow 64-bit versions of some functions */
	FLAC__StreamEncoderWriteStatus (*write_callback)(const FLAC__StreamEncoder *encoder, const byte buffer[], unsigned bytes, unsigned samples, unsigned current_frame, void *client_data);
	void (*metadata_callback)(const FLAC__StreamEncoder *encoder, const FLAC__StreamMetaData *metadata, void *client_data);
	void *client_data;
	/* unaligned (original) pointers to allocated data */
	int32 *integer_signal_unaligned[FLAC__MAX_CHANNELS];
	int32 *integer_signal_mid_side_unaligned[2];
	real *real_signal_unaligned[FLAC__MAX_CHANNELS];
	real *real_signal_mid_side_unaligned[2];
	int32 *residual_workspace_unaligned[FLAC__MAX_CHANNELS][2];
	int32 *residual_workspace_mid_side_unaligned[2][2];
	uint32 *abs_residual_unaligned;
	uint32 *abs_residual_partition_sums_unaligned;
	unsigned *raw_bits_per_partition_unaligned;
} FLAC__StreamEncoderPrivate;

/***********************************************************************
 *
 * Public static class data
 *
 ***********************************************************************/

const char *FLAC__StreamEncoderStateString[] = {
	"FLAC__STREAM_ENCODER_OK",
	"FLAC__STREAM_ENCODER_INVALID_NUMBER_OF_CHANNELS",
	"FLAC__STREAM_ENCODER_INVALID_BITS_PER_SAMPLE",
	"FLAC__STREAM_ENCODER_INVALID_SAMPLE_RATE",
	"FLAC__STREAM_ENCODER_INVALID_BLOCK_SIZE",
	"FLAC__STREAM_ENCODER_INVALID_QLP_COEFF_PRECISION",
	"FLAC__STREAM_ENCODER_MID_SIDE_CHANNELS_MISMATCH",
	"FLAC__STREAM_ENCODER_MID_SIDE_SAMPLE_SIZE_MISMATCH",
	"FLAC__STREAM_ENCODER_ILLEGAL_MID_SIDE_FORCE",
	"FLAC__STREAM_ENCODER_BLOCK_SIZE_TOO_SMALL_FOR_LPC_ORDER",
	"FLAC__STREAM_ENCODER_NOT_STREAMABLE",
	"FLAC__STREAM_ENCODER_FRAMING_ERROR",
	"FLAC__STREAM_ENCODER_FATAL_ERROR_WHILE_ENCODING",
	"FLAC__STREAM_ENCODER_FATAL_ERROR_WHILE_WRITING",
	"FLAC__STREAM_ENCODER_MEMORY_ALLOCATION_ERROR",
	"FLAC__STREAM_ENCODER_ALREADY_INITIALIZED",
	"FLAC__STREAM_ENCODER_UNINITIALIZED"
};

const char *FLAC__StreamEncoderWriteStatusString[] = {
	"FLAC__STREAM_ENCODER_WRITE_OK",
	"FLAC__STREAM_ENCODER_WRITE_FATAL_ERROR"
};

/***********************************************************************
 *
 * Class constructor/destructor
 *
 ***********************************************************************/
FLAC__StreamEncoder *FLAC__stream_encoder_new()
{
	FLAC__StreamEncoder *encoder;

	FLAC__ASSERT(sizeof(int) >= 4); /* we want to die right away if this is not true */

	encoder = (FLAC__StreamEncoder*)malloc(sizeof(FLAC__StreamEncoder));
	if(encoder == 0) {
		return 0;
	}
	encoder->protected = (FLAC__StreamEncoderProtected*)malloc(sizeof(FLAC__StreamEncoderProtected));
	if(encoder->protected == 0) {
		free(encoder);
		return 0;
	}
	encoder->private = (FLAC__StreamEncoderPrivate*)malloc(sizeof(FLAC__StreamEncoderPrivate));
	if(encoder->private == 0) {
		free(encoder->protected);
		free(encoder);
		return 0;
	}

	encoder->protected->state = FLAC__STREAM_ENCODER_UNINITIALIZED;

	return encoder;
}

void FLAC__stream_encoder_delete(FLAC__StreamEncoder *encoder)
{
	FLAC__ASSERT(encoder != 0);
	FLAC__ASSERT(encoder->protected != 0);
	FLAC__ASSERT(encoder->private != 0);

	free(encoder->private);
	free(encoder->protected);
	free(encoder);
}

/***********************************************************************
 *
 * Public class methods
 *
 ***********************************************************************/

FLAC__StreamEncoderState FLAC__stream_encoder_init(
	FLAC__StreamEncoder *encoder,
	bool streamable_subset,
	bool do_mid_side_stereo,
	bool loose_mid_side_stereo,
	unsigned channels,
	unsigned bits_per_sample,
	unsigned sample_rate,
	unsigned blocksize,
	unsigned max_lpc_order,
	unsigned qlp_coeff_precision,
	bool do_qlp_coeff_prec_search,
	bool do_exhaustive_model_search,
	unsigned min_residual_partition_order,
	unsigned max_residual_partition_order,
	unsigned rice_parameter_search_dist,
	uint64 total_samples_estimate,
	const FLAC__StreamMetaData_SeekTable *seek_table,
	unsigned padding,
	FLAC__StreamEncoderWriteStatus (*write_callback)(const FLAC__StreamEncoder *encoder, const byte buffer[], unsigned bytes, unsigned samples, unsigned current_frame, void *client_data),
	void (*metadata_callback)(const FLAC__StreamEncoder *encoder, const FLAC__StreamMetaData *metadata, void *client_data),
	void *client_data)
{
	unsigned i;
	FLAC__StreamMetaData padding_block;
	FLAC__StreamMetaData seek_table_block;

	FLAC__ASSERT(encoder != 0);
	FLAC__ASSERT(write_callback != 0);
	FLAC__ASSERT(metadata_callback != 0);

	if(encoder->protected->state != FLAC__STREAM_ENCODER_UNINITIALIZED)
		return encoder->protected->state = FLAC__STREAM_ENCODER_ALREADY_INITIALIZED;

	encoder->protected->state = FLAC__STREAM_ENCODER_OK;

	encoder->protected->streamable_subset = streamable_subset;
	encoder->protected->do_mid_side_stereo = do_mid_side_stereo;
	encoder->protected->loose_mid_side_stereo = loose_mid_side_stereo;
	encoder->protected->channels = channels;
	encoder->protected->bits_per_sample = bits_per_sample;
	encoder->protected->sample_rate = sample_rate;
	encoder->protected->blocksize = blocksize;
	encoder->protected->max_lpc_order = max_lpc_order;
	encoder->protected->qlp_coeff_precision = qlp_coeff_precision;
	encoder->protected->do_qlp_coeff_prec_search = do_qlp_coeff_prec_search;
	encoder->protected->do_exhaustive_model_search = do_exhaustive_model_search;
	encoder->protected->min_residual_partition_order = min_residual_partition_order;
	encoder->protected->max_residual_partition_order = max_residual_partition_order;
	encoder->protected->rice_parameter_search_dist = rice_parameter_search_dist;
	encoder->protected->total_samples_estimate = total_samples_estimate;
	encoder->protected->seek_table = seek_table;
	encoder->protected->padding = padding;

	if(encoder->protected->channels == 0 || encoder->protected->channels > FLAC__MAX_CHANNELS)
		return encoder->protected->state = FLAC__STREAM_ENCODER_INVALID_NUMBER_OF_CHANNELS;

	if(encoder->protected->do_mid_side_stereo && encoder->protected->channels != 2)
		return encoder->protected->state = FLAC__STREAM_ENCODER_MID_SIDE_CHANNELS_MISMATCH;

	if(encoder->protected->loose_mid_side_stereo && !encoder->protected->do_mid_side_stereo)
		return encoder->protected->state = FLAC__STREAM_ENCODER_ILLEGAL_MID_SIDE_FORCE;

	if(encoder->protected->bits_per_sample >= 32)
		encoder->protected->do_mid_side_stereo = false; /* since we do 32-bit math, the side channel would have 33 bps and overflow */

	if(encoder->protected->bits_per_sample < FLAC__MIN_BITS_PER_SAMPLE || encoder->protected->bits_per_sample > FLAC__MAX_BITS_PER_SAMPLE)
		return encoder->protected->state = FLAC__STREAM_ENCODER_INVALID_BITS_PER_SAMPLE;

	if(encoder->protected->sample_rate == 0 || encoder->protected->sample_rate > FLAC__MAX_SAMPLE_RATE)
		return encoder->protected->state = FLAC__STREAM_ENCODER_INVALID_SAMPLE_RATE;

	if(encoder->protected->blocksize < FLAC__MIN_BLOCK_SIZE || encoder->protected->blocksize > FLAC__MAX_BLOCK_SIZE)
		return encoder->protected->state = FLAC__STREAM_ENCODER_INVALID_BLOCK_SIZE;

	if(encoder->protected->blocksize < encoder->protected->max_lpc_order)
		return encoder->protected->state = FLAC__STREAM_ENCODER_BLOCK_SIZE_TOO_SMALL_FOR_LPC_ORDER;

	if(encoder->protected->qlp_coeff_precision == 0) {
		if(encoder->protected->bits_per_sample < 16) {
			/* @@@ need some data about how to set this here w.r.t. blocksize and sample rate */
			/* @@@ until then we'll make a guess */
			encoder->protected->qlp_coeff_precision = max(5, 2 + encoder->protected->bits_per_sample / 2);
		}
		else if(encoder->protected->bits_per_sample == 16) {
			if(encoder->protected->blocksize <= 192)
				encoder->protected->qlp_coeff_precision = 7;
			else if(encoder->protected->blocksize <= 384)
				encoder->protected->qlp_coeff_precision = 8;
			else if(encoder->protected->blocksize <= 576)
				encoder->protected->qlp_coeff_precision = 9;
			else if(encoder->protected->blocksize <= 1152)
				encoder->protected->qlp_coeff_precision = 10;
			else if(encoder->protected->blocksize <= 2304)
				encoder->protected->qlp_coeff_precision = 11;
			else if(encoder->protected->blocksize <= 4608)
				encoder->protected->qlp_coeff_precision = 12;
			else
				encoder->protected->qlp_coeff_precision = 13;
		}
		else {
			encoder->protected->qlp_coeff_precision = min(13, 8*sizeof(int32) - encoder->protected->bits_per_sample - 1);
		}
	}
	else if(encoder->protected->qlp_coeff_precision < FLAC__MIN_QLP_COEFF_PRECISION || encoder->protected->qlp_coeff_precision + encoder->protected->bits_per_sample >= 8*sizeof(uint32) || encoder->protected->qlp_coeff_precision >= (1u<<FLAC__SUBFRAME_LPC_QLP_COEFF_PRECISION_LEN))
		return encoder->protected->state = FLAC__STREAM_ENCODER_INVALID_QLP_COEFF_PRECISION;

	if(encoder->protected->streamable_subset) {
		//@@@ add check for blocksize here
		if(encoder->protected->bits_per_sample != 8 && encoder->protected->bits_per_sample != 12 && encoder->protected->bits_per_sample != 16 && encoder->protected->bits_per_sample != 20 && encoder->protected->bits_per_sample != 24)
			return encoder->protected->state = FLAC__STREAM_ENCODER_NOT_STREAMABLE;
		if(encoder->protected->sample_rate > 655350)
			return encoder->protected->state = FLAC__STREAM_ENCODER_NOT_STREAMABLE;
	}

	if(encoder->protected->max_residual_partition_order >= (1u << FLAC__ENTROPY_CODING_METHOD_PARTITIONED_RICE_ORDER_LEN))
		encoder->protected->max_residual_partition_order = (1u << FLAC__ENTROPY_CODING_METHOD_PARTITIONED_RICE_ORDER_LEN) - 1;
	if(encoder->protected->min_residual_partition_order >= encoder->protected->max_residual_partition_order)
		encoder->protected->min_residual_partition_order = encoder->protected->max_residual_partition_order;

	encoder->private->input_capacity = 0;
	for(i = 0; i < encoder->protected->channels; i++) {
		encoder->private->integer_signal_unaligned[i] = encoder->private->integer_signal[i] = 0;
		encoder->private->real_signal_unaligned[i] = encoder->private->real_signal[i] = 0;
	}
	for(i = 0; i < 2; i++) {
		encoder->private->integer_signal_mid_side_unaligned[i] = encoder->private->integer_signal_mid_side[i] = 0;
		encoder->private->real_signal_mid_side_unaligned[i] = encoder->private->real_signal_mid_side[i] = 0;
	}
	for(i = 0; i < encoder->protected->channels; i++) {
		encoder->private->residual_workspace_unaligned[i][0] = encoder->private->residual_workspace[i][0] = 0;
		encoder->private->residual_workspace_unaligned[i][1] = encoder->private->residual_workspace[i][1] = 0;
		encoder->private->best_subframe[i] = 0;
	}
	for(i = 0; i < 2; i++) {
		encoder->private->residual_workspace_mid_side_unaligned[i][0] = encoder->private->residual_workspace_mid_side[i][0] = 0;
		encoder->private->residual_workspace_mid_side_unaligned[i][1] = encoder->private->residual_workspace_mid_side[i][1] = 0;
		encoder->private->best_subframe_mid_side[i] = 0;
	}
	for(i = 0; i < encoder->protected->channels; i++) {
		encoder->private->subframe_workspace_ptr[i][0] = &encoder->private->subframe_workspace[i][0];
		encoder->private->subframe_workspace_ptr[i][1] = &encoder->private->subframe_workspace[i][1];
	}
	for(i = 0; i < 2; i++) {
		encoder->private->subframe_workspace_ptr_mid_side[i][0] = &encoder->private->subframe_workspace_mid_side[i][0];
		encoder->private->subframe_workspace_ptr_mid_side[i][1] = &encoder->private->subframe_workspace_mid_side[i][1];
	}
	encoder->private->abs_residual_unaligned = encoder->private->abs_residual = 0;
	encoder->private->abs_residual_partition_sums_unaligned = encoder->private->abs_residual_partition_sums = 0;
	encoder->private->raw_bits_per_partition_unaligned = encoder->private->raw_bits_per_partition = 0;
	encoder->private->loose_mid_side_stereo_frames_exact = (double)encoder->protected->sample_rate * 0.4 / (double)encoder->protected->blocksize;
	encoder->private->loose_mid_side_stereo_frames = (unsigned)(encoder->private->loose_mid_side_stereo_frames_exact + 0.5);
	if(encoder->private->loose_mid_side_stereo_frames == 0)
		encoder->private->loose_mid_side_stereo_frames = 1;
	encoder->private->loose_mid_side_stereo_frame_count = 0;
	encoder->private->current_sample_number = 0;
	encoder->private->current_frame_number = 0;

	/*
	 * get the CPU info and set the function pointers
	 */
	FLAC__cpu_info(&encoder->private->cpuinfo);
	/* first default to the non-asm routines */
	encoder->private->local_lpc_compute_autocorrelation = FLAC__lpc_compute_autocorrelation;
	encoder->private->local_fixed_compute_best_predictor = FLAC__fixed_compute_best_predictor;
	encoder->private->local_lpc_compute_residual_from_qlp_coefficients = FLAC__lpc_compute_residual_from_qlp_coefficients;
	encoder->private->local_lpc_compute_residual_from_qlp_coefficients_16bit = FLAC__lpc_compute_residual_from_qlp_coefficients;
	/* now override with asm where appropriate */
#ifndef FLAC__NO_ASM
	FLAC__ASSERT(encoder->private->cpuinfo.use_asm);
#ifdef FLAC__CPU_IA32
	FLAC__ASSERT(encoder->private->cpuinfo.type == FLAC__CPUINFO_TYPE_IA32);
#ifdef FLAC__HAS_NASM
	if(0 && encoder->private->cpuinfo.data.ia32.sse) { /* SSE version lacks necessary resolution, plus SSE flag doesn't check for OS support */
		if(encoder->protected->max_lpc_order < 4)
			encoder->private->local_lpc_compute_autocorrelation = FLAC__lpc_compute_autocorrelation_asm_ia32_sse_lag_4;
		else if(encoder->protected->max_lpc_order < 8)
			encoder->private->local_lpc_compute_autocorrelation = FLAC__lpc_compute_autocorrelation_asm_ia32_sse_lag_8;
		else if(encoder->protected->max_lpc_order < 12)
			encoder->private->local_lpc_compute_autocorrelation = FLAC__lpc_compute_autocorrelation_asm_ia32_sse_lag_12;
		else
			encoder->private->local_lpc_compute_autocorrelation = FLAC__lpc_compute_autocorrelation_asm_ia32;
	}
	else
		encoder->private->local_lpc_compute_autocorrelation = FLAC__lpc_compute_autocorrelation_asm_ia32;
	if(encoder->private->cpuinfo.data.ia32.mmx && encoder->private->cpuinfo.data.ia32.cmov)
		encoder->private->local_fixed_compute_best_predictor = FLAC__fixed_compute_best_predictor_asm_ia32_mmx_cmov;
	if(encoder->private->cpuinfo.data.ia32.mmx) {
		encoder->private->local_lpc_compute_residual_from_qlp_coefficients = FLAC__lpc_compute_residual_from_qlp_coefficients_asm_ia32;
		encoder->private->local_lpc_compute_residual_from_qlp_coefficients_16bit = FLAC__lpc_compute_residual_from_qlp_coefficients_asm_ia32_mmx;
	}
	else {
		encoder->private->local_lpc_compute_residual_from_qlp_coefficients = FLAC__lpc_compute_residual_from_qlp_coefficients_asm_ia32;
		encoder->private->local_lpc_compute_residual_from_qlp_coefficients_16bit = FLAC__lpc_compute_residual_from_qlp_coefficients_asm_ia32;
	}
#endif
#endif
#endif

	if(encoder->protected->bits_per_sample + FLAC__bitmath_ilog2(encoder->protected->blocksize)+1 > 30)
		encoder->private->use_slow = true;
	else
		encoder->private->use_slow = false;

	if(!stream_encoder_resize_buffers_(encoder, encoder->protected->blocksize)) {
		/* the above function sets the state for us in case of an error */
		return encoder->protected->state;
	}
	FLAC__bitbuffer_init(&encoder->private->frame);
	encoder->private->write_callback = write_callback;
	encoder->private->metadata_callback = metadata_callback;
	encoder->private->client_data = client_data;

	/*
	 * write the stream header
	 */

	if(!FLAC__bitbuffer_clear(&encoder->private->frame))
		return encoder->protected->state = FLAC__STREAM_ENCODER_MEMORY_ALLOCATION_ERROR;
	if(!FLAC__bitbuffer_write_raw_uint32(&encoder->private->frame, FLAC__STREAM_SYNC, FLAC__STREAM_SYNC_LEN))
		return encoder->protected->state = FLAC__STREAM_ENCODER_FRAMING_ERROR;

	encoder->private->metadata.type = FLAC__METADATA_TYPE_STREAMINFO;
	encoder->private->metadata.is_last = (encoder->protected->seek_table == 0 && encoder->protected->padding == 0);
	encoder->private->metadata.length = FLAC__STREAM_METADATA_STREAMINFO_LENGTH;
	encoder->private->metadata.data.stream_info.min_blocksize = encoder->protected->blocksize; /* this encoder uses the same blocksize for the whole stream */
	encoder->private->metadata.data.stream_info.max_blocksize = encoder->protected->blocksize;
	encoder->private->metadata.data.stream_info.min_framesize = 0; /* we don't know this yet; have to fill it in later */
	encoder->private->metadata.data.stream_info.max_framesize = 0; /* we don't know this yet; have to fill it in later */
	encoder->private->metadata.data.stream_info.sample_rate = encoder->protected->sample_rate;
	encoder->private->metadata.data.stream_info.channels = encoder->protected->channels;
	encoder->private->metadata.data.stream_info.bits_per_sample = encoder->protected->bits_per_sample;
	encoder->private->metadata.data.stream_info.total_samples = encoder->protected->total_samples_estimate; /* we will replace this later with the real total */
	memset(encoder->private->metadata.data.stream_info.md5sum, 0, 16); /* we don't know this yet; have to fill it in later */
	MD5Init(&encoder->private->md5context);
	if(!FLAC__add_metadata_block(&encoder->private->metadata, &encoder->private->frame))
		return encoder->protected->state = FLAC__STREAM_ENCODER_FRAMING_ERROR;

	if(0 != encoder->protected->seek_table) {
		if(!FLAC__seek_table_is_valid(encoder->protected->seek_table))
			return encoder->protected->state = FLAC__STREAM_ENCODER_INVALID_SEEK_TABLE;
		seek_table_block.type = FLAC__METADATA_TYPE_SEEKTABLE;
		seek_table_block.is_last = (encoder->protected->padding == 0);
		seek_table_block.length = encoder->protected->seek_table->num_points * FLAC__STREAM_METADATA_SEEKPOINT_LEN;
		seek_table_block.data.seek_table = *encoder->protected->seek_table;
		if(!FLAC__add_metadata_block(&seek_table_block, &encoder->private->frame))
			return encoder->protected->state = FLAC__STREAM_ENCODER_FRAMING_ERROR;
	}

	/* add a PADDING block if requested */
	if(encoder->protected->padding > 0) {
		padding_block.type = FLAC__METADATA_TYPE_PADDING;
		padding_block.is_last = true;
		padding_block.length = encoder->protected->padding;
		if(!FLAC__add_metadata_block(&padding_block, &encoder->private->frame))
			return encoder->protected->state = FLAC__STREAM_ENCODER_FRAMING_ERROR;
	}

	FLAC__ASSERT(encoder->private->frame.bits == 0); /* assert that we're byte-aligned before writing */
	FLAC__ASSERT(encoder->private->frame.total_consumed_bits == 0); /* assert that no reading of the buffer was done */
	if(encoder->private->write_callback(encoder, encoder->private->frame.buffer, encoder->private->frame.bytes, 0, encoder->private->current_frame_number, encoder->private->client_data) != FLAC__STREAM_ENCODER_WRITE_OK)
		return encoder->protected->state = FLAC__STREAM_ENCODER_FATAL_ERROR_WHILE_WRITING;

	/* now that the metadata block is written, we can init this to an absurdly-high value... */
	encoder->private->metadata.data.stream_info.min_framesize = (1u << FLAC__STREAM_METADATA_STREAMINFO_MIN_FRAME_SIZE_LEN) - 1;
	/* ... and clear this to 0 */
	encoder->private->metadata.data.stream_info.total_samples = 0;

	return encoder->protected->state;
}

void FLAC__stream_encoder_finish(FLAC__StreamEncoder *encoder)
{
	unsigned i, channel;

	FLAC__ASSERT(encoder != 0);
	if(encoder->protected->state == FLAC__STREAM_ENCODER_UNINITIALIZED)
		return;
	if(encoder->private->current_sample_number != 0) {
		encoder->protected->blocksize = encoder->private->current_sample_number;
		stream_encoder_process_frame_(encoder, true); /* true => is last frame */
	}
	MD5Final(encoder->private->metadata.data.stream_info.md5sum, &encoder->private->md5context);
	encoder->private->metadata_callback(encoder, &encoder->private->metadata, encoder->private->client_data);
	for(i = 0; i < encoder->protected->channels; i++) {
		if(encoder->private->integer_signal_unaligned[i] != 0) {
			free(encoder->private->integer_signal_unaligned[i]);
			encoder->private->integer_signal_unaligned[i] = 0;
		}
		if(encoder->private->real_signal_unaligned[i] != 0) {
			free(encoder->private->real_signal_unaligned[i]);
			encoder->private->real_signal_unaligned[i] = 0;
		}
	}
	for(i = 0; i < 2; i++) {
		if(encoder->private->integer_signal_mid_side_unaligned[i] != 0) {
			free(encoder->private->integer_signal_mid_side_unaligned[i]);
			encoder->private->integer_signal_mid_side_unaligned[i] = 0;
		}
		if(encoder->private->real_signal_mid_side_unaligned[i] != 0) {
			free(encoder->private->real_signal_mid_side_unaligned[i]);
			encoder->private->real_signal_mid_side_unaligned[i] = 0;
		}
	}
	for(channel = 0; channel < encoder->protected->channels; channel++) {
		for(i = 0; i < 2; i++) {
			if(encoder->private->residual_workspace_unaligned[channel][i] != 0) {
				free(encoder->private->residual_workspace_unaligned[channel][i]);
				encoder->private->residual_workspace_unaligned[channel][i] = 0;
			}
		}
	}
	for(channel = 0; channel < 2; channel++) {
		for(i = 0; i < 2; i++) {
			if(encoder->private->residual_workspace_mid_side_unaligned[channel][i] != 0) {
				free(encoder->private->residual_workspace_mid_side_unaligned[channel][i]);
				encoder->private->residual_workspace_mid_side_unaligned[channel][i] = 0;
			}
		}
	}
	if(encoder->private->abs_residual_unaligned != 0) {
		free(encoder->private->abs_residual_unaligned);
		encoder->private->abs_residual_unaligned = 0;
	}
	if(encoder->private->abs_residual_partition_sums_unaligned != 0) {
		free(encoder->private->abs_residual_partition_sums_unaligned);
		encoder->private->abs_residual_partition_sums_unaligned = 0;
	}
	if(encoder->private->raw_bits_per_partition_unaligned != 0) {
		free(encoder->private->raw_bits_per_partition_unaligned);
		encoder->private->raw_bits_per_partition_unaligned = 0;
	}
	FLAC__bitbuffer_free(&encoder->private->frame);

	encoder->protected->state = FLAC__STREAM_ENCODER_UNINITIALIZED;
}

FLAC__StreamEncoderState FLAC__stream_encoder_state(const FLAC__StreamEncoder *encoder)
{
	return encoder->protected->state;
}

bool FLAC__stream_encoder_streamable_subset(const FLAC__StreamEncoder *encoder)
{
	return encoder->protected->streamable_subset;
}

bool FLAC__stream_encoder_do_mid_side_stereo(const FLAC__StreamEncoder *encoder)
{
	return encoder->protected->do_mid_side_stereo;
}

bool FLAC__stream_encoder_loose_mid_side_stereo(const FLAC__StreamEncoder *encoder)
{
	return encoder->protected->loose_mid_side_stereo;
}

unsigned FLAC__stream_encoder_channels(const FLAC__StreamEncoder *encoder)
{
	return encoder->protected->channels;
}

unsigned FLAC__stream_encoder_bits_per_sample(const FLAC__StreamEncoder *encoder)
{
	return encoder->protected->bits_per_sample;
}

unsigned FLAC__stream_encoder_sample_rate(const FLAC__StreamEncoder *encoder)
{
	return encoder->protected->sample_rate;
}

unsigned FLAC__stream_encoder_blocksize(const FLAC__StreamEncoder *encoder)
{
	return encoder->protected->blocksize;
}

unsigned FLAC__stream_encoder_max_lpc_order(const FLAC__StreamEncoder *encoder)
{
	return encoder->protected->max_lpc_order;
}

unsigned FLAC__stream_encoder_qlp_coeff_precision(const FLAC__StreamEncoder *encoder)
{
	return encoder->protected->qlp_coeff_precision;
}

bool FLAC__stream_encoder_do_qlp_coeff_prec_search(const FLAC__StreamEncoder *encoder)
{
	return encoder->protected->do_qlp_coeff_prec_search;
}

bool FLAC__stream_encoder_do_exhaustive_model_search(const FLAC__StreamEncoder *encoder)
{
	return encoder->protected->do_exhaustive_model_search;
}

unsigned FLAC__stream_encoder_min_residual_partition_order(const FLAC__StreamEncoder *encoder)
{
	return encoder->protected->min_residual_partition_order;
}

unsigned FLAC__stream_encoder_max_residual_partition_order(const FLAC__StreamEncoder *encoder)
{
	return encoder->protected->max_residual_partition_order;
}

unsigned FLAC__stream_encoder_rice_parameter_search_dist(const FLAC__StreamEncoder *encoder)
{
	return encoder->protected->rice_parameter_search_dist;
}

bool FLAC__stream_encoder_process(FLAC__StreamEncoder *encoder, const int32 *buf[], unsigned samples)
{
	unsigned i, j, channel;
	int32 x, mid, side;
	const unsigned channels = encoder->protected->channels, blocksize = encoder->protected->blocksize;

	FLAC__ASSERT(encoder != 0);
	FLAC__ASSERT(encoder->protected->state == FLAC__STREAM_ENCODER_OK);

	j = 0;
	if(encoder->protected->do_mid_side_stereo && channels == 2) {
		do {
			for(i = encoder->private->current_sample_number; i < blocksize && j < samples; i++, j++) {
				x = mid = side = buf[0][j];
				encoder->private->integer_signal[0][i] = x;
				encoder->private->real_signal[0][i] = (real)x;
				x = buf[1][j];
				encoder->private->integer_signal[1][i] = x;
				encoder->private->real_signal[1][i] = (real)x;
				mid += x;
				side -= x;
				mid >>= 1; /* NOTE: not the same as 'mid = (buf[0][j] + buf[1][j]) / 2' ! */
				encoder->private->integer_signal_mid_side[1][i] = side;
				encoder->private->integer_signal_mid_side[0][i] = mid;
				encoder->private->real_signal_mid_side[1][i] = (real)side;
				encoder->private->real_signal_mid_side[0][i] = (real)mid;
				encoder->private->current_sample_number++;
			}
			if(i == blocksize) {
				if(!stream_encoder_process_frame_(encoder, false)) /* false => not last frame */
					return false;
			}
		} while(j < samples);
	}
	else {
		do {
			for(i = encoder->private->current_sample_number; i < blocksize && j < samples; i++, j++) {
				for(channel = 0; channel < channels; channel++) {
					x = buf[channel][j];
					encoder->private->integer_signal[channel][i] = x;
					encoder->private->real_signal[channel][i] = (real)x;
				}
				encoder->private->current_sample_number++;
			}
			if(i == blocksize) {
				if(!stream_encoder_process_frame_(encoder, false)) /* false => not last frame */
					return false;
			}
		} while(j < samples);
	}

	return true;
}

/* 'samples' is channel-wide samples, e.g. for 1 second at 44100Hz, 'samples' = 44100 regardless of the number of channels */
bool FLAC__stream_encoder_process_interleaved(FLAC__StreamEncoder *encoder, const int32 buf[], unsigned samples)
{
	unsigned i, j, k, channel;
	int32 x, mid, side;
	const unsigned channels = encoder->protected->channels, blocksize = encoder->protected->blocksize;

	FLAC__ASSERT(encoder != 0);
	FLAC__ASSERT(encoder->protected->state == FLAC__STREAM_ENCODER_OK);

	j = k = 0;
	if(encoder->protected->do_mid_side_stereo && channels == 2) {
		do {
			for(i = encoder->private->current_sample_number; i < blocksize && j < samples; i++, j++) {
				x = mid = side = buf[k++];
				encoder->private->integer_signal[0][i] = x;
				encoder->private->real_signal[0][i] = (real)x;
				x = buf[k++];
				encoder->private->integer_signal[1][i] = x;
				encoder->private->real_signal[1][i] = (real)x;
				mid += x;
				side -= x;
				mid >>= 1; /* NOTE: not the same as 'mid = (left + right) / 2' ! */
				encoder->private->integer_signal_mid_side[1][i] = side;
				encoder->private->integer_signal_mid_side[0][i] = mid;
				encoder->private->real_signal_mid_side[1][i] = (real)side;
				encoder->private->real_signal_mid_side[0][i] = (real)mid;
				encoder->private->current_sample_number++;
			}
			if(i == blocksize) {
				if(!stream_encoder_process_frame_(encoder, false)) /* false => not last frame */
					return false;
			}
		} while(j < samples);
	}
	else {
		do {
			for(i = encoder->private->current_sample_number; i < blocksize && j < samples; i++, j++) {
				for(channel = 0; channel < channels; channel++) {
					x = buf[k++];
					encoder->private->integer_signal[channel][i] = x;
					encoder->private->real_signal[channel][i] = (real)x;
				}
				encoder->private->current_sample_number++;
			}
			if(i == blocksize) {
				if(!stream_encoder_process_frame_(encoder, false)) /* false => not last frame */
					return false;
			}
		} while(j < samples);
	}

	return true;
}

bool stream_encoder_resize_buffers_(FLAC__StreamEncoder *encoder, unsigned new_size)
{
	bool ok;
	unsigned i, channel;

	FLAC__ASSERT(new_size > 0);
	FLAC__ASSERT(encoder->protected->state == FLAC__STREAM_ENCODER_OK);
	FLAC__ASSERT(encoder->private->current_sample_number == 0);

	/* To avoid excessive malloc'ing, we only grow the buffer; no shrinking. */
	if(new_size <= encoder->private->input_capacity)
		return true;

	ok = true;
	for(i = 0; ok && i < encoder->protected->channels; i++) {
		ok = ok && FLAC__memory_alloc_aligned_int32_array(new_size, &encoder->private->integer_signal_unaligned[i], &encoder->private->integer_signal[i]);
		ok = ok && FLAC__memory_alloc_aligned_real_array(new_size, &encoder->private->real_signal_unaligned[i], &encoder->private->real_signal[i]);
	}
	for(i = 0; ok && i < 2; i++) {
		ok = ok && FLAC__memory_alloc_aligned_int32_array(new_size, &encoder->private->integer_signal_mid_side_unaligned[i], &encoder->private->integer_signal_mid_side[i]);
		ok = ok && FLAC__memory_alloc_aligned_real_array(new_size, &encoder->private->real_signal_mid_side_unaligned[i], &encoder->private->real_signal_mid_side[i]);
	}
	for(channel = 0; ok && channel < encoder->protected->channels; channel++) {
		for(i = 0; ok && i < 2; i++) {
			ok = ok && FLAC__memory_alloc_aligned_int32_array(new_size, &encoder->private->residual_workspace_unaligned[channel][i], &encoder->private->residual_workspace[channel][i]);
		}
	}
	for(channel = 0; ok && channel < 2; channel++) {
		for(i = 0; ok && i < 2; i++) {
			ok = ok && FLAC__memory_alloc_aligned_int32_array(new_size, &encoder->private->residual_workspace_mid_side_unaligned[channel][i], &encoder->private->residual_workspace_mid_side[channel][i]);
		}
	}
	ok = ok && FLAC__memory_alloc_aligned_uint32_array(new_size, &encoder->private->abs_residual_unaligned, &encoder->private->abs_residual);
#ifdef FLAC__PRECOMPUTE_PARTITION_SUMS
	ok = ok && FLAC__memory_alloc_aligned_uint32_array(new_size * 2, &encoder->private->abs_residual_partition_sums_unaligned, &encoder->private->abs_residual_partition_sums);
#endif
#ifdef FLAC__SEARCH_FOR_ESCAPES
	ok = ok && FLAC__memory_alloc_aligned_unsigned_array(new_size * 2, &encoder->private->raw_bits_per_partition_unaligned, &encoder->private->raw_bits_per_partition);
#endif

	if(ok)
		encoder->private->input_capacity = new_size;
	else
		encoder->protected->state = FLAC__STREAM_ENCODER_MEMORY_ALLOCATION_ERROR;

	return ok;
}

/***********************************************************************
 *
 * Private class methods
 *
 ***********************************************************************/

bool stream_encoder_process_frame_(FLAC__StreamEncoder *encoder, bool is_last_frame)
{
	FLAC__ASSERT(encoder->protected->state == FLAC__STREAM_ENCODER_OK);

	/*
	 * Accumulate raw signal to the MD5 signature
	 */
	/* NOTE: some versions of GCC can't figure out const-ness right and will give you an 'incompatible pointer type' warning on arg 2 here: */
	if(!FLAC__MD5Accumulate(&encoder->private->md5context, encoder->private->integer_signal, encoder->protected->channels, encoder->protected->blocksize, (encoder->protected->bits_per_sample+7) / 8)) {
		encoder->protected->state = FLAC__STREAM_ENCODER_MEMORY_ALLOCATION_ERROR;
		return false;
	}

	/*
	 * Process the frame header and subframes into the frame bitbuffer
	 */
	if(!stream_encoder_process_subframes_(encoder, is_last_frame)) {
		/* the above function sets the state for us in case of an error */
		return false;
	}

	/*
	 * Zero-pad the frame to a byte_boundary
	 */
	if(!FLAC__bitbuffer_zero_pad_to_byte_boundary(&encoder->private->frame)) {
		encoder->protected->state = FLAC__STREAM_ENCODER_MEMORY_ALLOCATION_ERROR;
		return false;
	}

	/*
	 * CRC-16 the whole thing
	 */
	FLAC__ASSERT(encoder->private->frame.bits == 0); /* assert that we're byte-aligned */
	FLAC__ASSERT(encoder->private->frame.total_consumed_bits == 0); /* assert that no reading of the buffer was done */
	FLAC__bitbuffer_write_raw_uint32(&encoder->private->frame, FLAC__crc16(encoder->private->frame.buffer, encoder->private->frame.bytes), FLAC__FRAME_FOOTER_CRC_LEN);

	/*
	 * Write it
	 */
	if(encoder->private->write_callback(encoder, encoder->private->frame.buffer, encoder->private->frame.bytes, encoder->protected->blocksize, encoder->private->current_frame_number, encoder->private->client_data) != FLAC__STREAM_ENCODER_WRITE_OK) {
		encoder->protected->state = FLAC__STREAM_ENCODER_FATAL_ERROR_WHILE_WRITING;
		return false;
	}

	/*
	 * Get ready for the next frame
	 */
	encoder->private->current_sample_number = 0;
	encoder->private->current_frame_number++;
	encoder->private->metadata.data.stream_info.total_samples += (uint64)encoder->protected->blocksize;
	encoder->private->metadata.data.stream_info.min_framesize = min(encoder->private->frame.bytes, encoder->private->metadata.data.stream_info.min_framesize);
	encoder->private->metadata.data.stream_info.max_framesize = max(encoder->private->frame.bytes, encoder->private->metadata.data.stream_info.max_framesize);

	return true;
}

bool stream_encoder_process_subframes_(FLAC__StreamEncoder *encoder, bool is_last_frame)
{
	FLAC__FrameHeader frame_header;
	unsigned channel, min_partition_order = encoder->protected->min_residual_partition_order, max_partition_order;
	bool do_independent, do_mid_side;

	/*
	 * Calculate the min,max Rice partition orders
	 */
	if(is_last_frame) {
		max_partition_order = 0;
	}
	else {
		unsigned limit = 0, b = encoder->protected->blocksize;
		while(!(b & 1)) {
			limit++;
			b >>= 1;
		}
		max_partition_order = min(encoder->protected->max_residual_partition_order, limit);
	}
	min_partition_order = min(min_partition_order, max_partition_order);

	/*
	 * Setup the frame
	 */
	if(!FLAC__bitbuffer_clear(&encoder->private->frame)) {
		encoder->protected->state = FLAC__STREAM_ENCODER_MEMORY_ALLOCATION_ERROR;
		return false;
	}
	frame_header.blocksize = encoder->protected->blocksize;
	frame_header.sample_rate = encoder->protected->sample_rate;
	frame_header.channels = encoder->protected->channels;
	frame_header.channel_assignment = FLAC__CHANNEL_ASSIGNMENT_INDEPENDENT; /* the default unless the encoder determines otherwise */
	frame_header.bits_per_sample = encoder->protected->bits_per_sample;
	frame_header.number.frame_number = encoder->private->current_frame_number;

	/*
	 * Figure out what channel assignments to try
	 */
	if(encoder->protected->do_mid_side_stereo) {
		if(encoder->protected->loose_mid_side_stereo) {
			if(encoder->private->loose_mid_side_stereo_frame_count == 0) {
				do_independent = true;
				do_mid_side = true;
			}
			else {
				do_independent = (encoder->private->last_channel_assignment == FLAC__CHANNEL_ASSIGNMENT_INDEPENDENT);
				do_mid_side = !do_independent;
			}
		}
		else {
			do_independent = true;
			do_mid_side = true;
		}
	}
	else {
		do_independent = true;
		do_mid_side = false;
	}

	FLAC__ASSERT(do_independent || do_mid_side);

	/*
	 * Check for wasted bits; set effective bps for each subframe
	 */
	if(do_independent) {
		unsigned w;
		for(channel = 0; channel < encoder->protected->channels; channel++) {
			w = stream_encoder_get_wasted_bits_(encoder->private->integer_signal[channel], encoder->protected->blocksize);
			encoder->private->subframe_workspace[channel][0].wasted_bits = encoder->private->subframe_workspace[channel][1].wasted_bits = w;
			encoder->private->subframe_bps[channel] = encoder->protected->bits_per_sample - w;
		}
	}
	if(do_mid_side) {
		unsigned w;
		FLAC__ASSERT(encoder->protected->channels == 2);
		for(channel = 0; channel < 2; channel++) {
			w = stream_encoder_get_wasted_bits_(encoder->private->integer_signal_mid_side[channel], encoder->protected->blocksize);
			encoder->private->subframe_workspace_mid_side[channel][0].wasted_bits = encoder->private->subframe_workspace_mid_side[channel][1].wasted_bits = w;
			encoder->private->subframe_bps_mid_side[channel] = encoder->protected->bits_per_sample - w + (channel==0? 0:1);
		}
	}

	/*
	 * First do a normal encoding pass of each independent channel
	 */
	if(do_independent) {
		for(channel = 0; channel < encoder->protected->channels; channel++) {
			if(!stream_encoder_process_subframe_(encoder, min_partition_order, max_partition_order, false, &frame_header, encoder->private->subframe_bps[channel], encoder->private->integer_signal[channel], encoder->private->real_signal[channel], encoder->private->subframe_workspace_ptr[channel], encoder->private->residual_workspace[channel], encoder->private->best_subframe+channel, encoder->private->best_subframe_bits+channel))
				return false;
		}
	}

	/*
	 * Now do mid and side channels if requested
	 */
	if(do_mid_side) {
		FLAC__ASSERT(encoder->protected->channels == 2);

		for(channel = 0; channel < 2; channel++) {
			if(!stream_encoder_process_subframe_(encoder, min_partition_order, max_partition_order, false, &frame_header, encoder->private->subframe_bps_mid_side[channel], encoder->private->integer_signal_mid_side[channel], encoder->private->real_signal_mid_side[channel], encoder->private->subframe_workspace_ptr_mid_side[channel], encoder->private->residual_workspace_mid_side[channel], encoder->private->best_subframe_mid_side+channel, encoder->private->best_subframe_bits_mid_side+channel))
				return false;
		}
	}

	/*
	 * Compose the frame bitbuffer
	 */
	if(do_mid_side) {
		unsigned left_bps = 0, right_bps = 0; /* initialized only to prevent superfluous compiler warning */
		FLAC__Subframe *left_subframe = 0, *right_subframe = 0; /* initialized only to prevent superfluous compiler warning */
		FLAC__ChannelAssignment channel_assignment;

		FLAC__ASSERT(encoder->protected->channels == 2);

		if(encoder->protected->loose_mid_side_stereo && encoder->private->loose_mid_side_stereo_frame_count > 0) {
			channel_assignment = (encoder->private->last_channel_assignment == FLAC__CHANNEL_ASSIGNMENT_INDEPENDENT? FLAC__CHANNEL_ASSIGNMENT_INDEPENDENT : FLAC__CHANNEL_ASSIGNMENT_MID_SIDE);
		}
		else {
			unsigned bits[4]; /* WATCHOUT - indexed by FLAC__ChannelAssignment */
			unsigned min_bits;
			FLAC__ChannelAssignment ca;

			FLAC__ASSERT(do_independent && do_mid_side);

			/* We have to figure out which channel assignent results in the smallest frame */
			bits[FLAC__CHANNEL_ASSIGNMENT_INDEPENDENT] = encoder->private->best_subframe_bits         [0] + encoder->private->best_subframe_bits         [1];
			bits[FLAC__CHANNEL_ASSIGNMENT_LEFT_SIDE  ] = encoder->private->best_subframe_bits         [0] + encoder->private->best_subframe_bits_mid_side[1];
			bits[FLAC__CHANNEL_ASSIGNMENT_RIGHT_SIDE ] = encoder->private->best_subframe_bits         [1] + encoder->private->best_subframe_bits_mid_side[1];
			bits[FLAC__CHANNEL_ASSIGNMENT_MID_SIDE   ] = encoder->private->best_subframe_bits_mid_side[0] + encoder->private->best_subframe_bits_mid_side[1];

			for(channel_assignment = 0, min_bits = bits[0], ca = 1; ca <= 3; ca++) {
				if(bits[ca] < min_bits) {
					min_bits = bits[ca];
					channel_assignment = ca;
				}
			}
		}

		frame_header.channel_assignment = channel_assignment;

		if(!FLAC__frame_add_header(&frame_header, encoder->protected->streamable_subset, is_last_frame, &encoder->private->frame)) {
			encoder->protected->state = FLAC__STREAM_ENCODER_FRAMING_ERROR;
			return false;
		}

		switch(channel_assignment) {
			case FLAC__CHANNEL_ASSIGNMENT_INDEPENDENT:
				left_subframe  = &encoder->private->subframe_workspace         [0][encoder->private->best_subframe         [0]];
				right_subframe = &encoder->private->subframe_workspace         [1][encoder->private->best_subframe         [1]];
				break;
			case FLAC__CHANNEL_ASSIGNMENT_LEFT_SIDE:
				left_subframe  = &encoder->private->subframe_workspace         [0][encoder->private->best_subframe         [0]];
				right_subframe = &encoder->private->subframe_workspace_mid_side[1][encoder->private->best_subframe_mid_side[1]];
				break;
			case FLAC__CHANNEL_ASSIGNMENT_RIGHT_SIDE:
				left_subframe  = &encoder->private->subframe_workspace_mid_side[1][encoder->private->best_subframe_mid_side[1]];
				right_subframe = &encoder->private->subframe_workspace         [1][encoder->private->best_subframe         [1]];
				break;
			case FLAC__CHANNEL_ASSIGNMENT_MID_SIDE:
				left_subframe  = &encoder->private->subframe_workspace_mid_side[0][encoder->private->best_subframe_mid_side[0]];
				right_subframe = &encoder->private->subframe_workspace_mid_side[1][encoder->private->best_subframe_mid_side[1]];
				break;
			default:
				FLAC__ASSERT(0);
		}

		switch(channel_assignment) {
			case FLAC__CHANNEL_ASSIGNMENT_INDEPENDENT:
				left_bps  = encoder->private->subframe_bps         [0];
				right_bps = encoder->private->subframe_bps         [1];
				break;
			case FLAC__CHANNEL_ASSIGNMENT_LEFT_SIDE:
				left_bps  = encoder->private->subframe_bps         [0];
				right_bps = encoder->private->subframe_bps_mid_side[1];
				break;
			case FLAC__CHANNEL_ASSIGNMENT_RIGHT_SIDE:
				left_bps  = encoder->private->subframe_bps_mid_side[1];
				right_bps = encoder->private->subframe_bps         [1];
				break;
			case FLAC__CHANNEL_ASSIGNMENT_MID_SIDE:
				left_bps  = encoder->private->subframe_bps_mid_side[0];
				right_bps = encoder->private->subframe_bps_mid_side[1];
				break;
			default:
				FLAC__ASSERT(0);
		}

		/* note that encoder_add_subframe_ sets the state for us in case of an error */
		if(!stream_encoder_add_subframe_(encoder, &frame_header, left_bps , left_subframe , &encoder->private->frame))
			return false;
		if(!stream_encoder_add_subframe_(encoder, &frame_header, right_bps, right_subframe, &encoder->private->frame))
			return false;
	}
	else {
		if(!FLAC__frame_add_header(&frame_header, encoder->protected->streamable_subset, is_last_frame, &encoder->private->frame)) {
			encoder->protected->state = FLAC__STREAM_ENCODER_FRAMING_ERROR;
			return false;
		}

		for(channel = 0; channel < encoder->protected->channels; channel++) {
			if(!stream_encoder_add_subframe_(encoder, &frame_header, encoder->private->subframe_bps[channel], &encoder->private->subframe_workspace[channel][encoder->private->best_subframe[channel]], &encoder->private->frame)) {
				/* the above function sets the state for us in case of an error */
				return false;
			}
		}
	}

	if(encoder->protected->loose_mid_side_stereo) {
		encoder->private->loose_mid_side_stereo_frame_count++;
		if(encoder->private->loose_mid_side_stereo_frame_count >= encoder->private->loose_mid_side_stereo_frames)
			encoder->private->loose_mid_side_stereo_frame_count = 0;
	}

	encoder->private->last_channel_assignment = frame_header.channel_assignment;

	return true;
}

bool stream_encoder_process_subframe_(FLAC__StreamEncoder *encoder, unsigned min_partition_order, unsigned max_partition_order, bool verbatim_only, const FLAC__FrameHeader *frame_header, unsigned subframe_bps, const int32 integer_signal[], const real real_signal[], FLAC__Subframe *subframe[2], int32 *residual[2], unsigned *best_subframe, unsigned *best_bits)
{
	real fixed_residual_bits_per_sample[FLAC__MAX_FIXED_ORDER+1];
	real lpc_residual_bits_per_sample;
	real autoc[FLAC__MAX_LPC_ORDER+1]; /* WATCHOUT: the size is important even though encoder->protected->max_lpc_order might be less; some asm routines need all the space */
	real lp_coeff[FLAC__MAX_LPC_ORDER][FLAC__MAX_LPC_ORDER];
	real lpc_error[FLAC__MAX_LPC_ORDER];
	unsigned min_lpc_order, max_lpc_order, lpc_order;
	unsigned min_fixed_order, max_fixed_order, guess_fixed_order, fixed_order;
	unsigned min_qlp_coeff_precision, max_qlp_coeff_precision, qlp_coeff_precision;
	unsigned rice_parameter;
	unsigned _candidate_bits, _best_bits;
	unsigned _best_subframe;

	/* verbatim subframe is the baseline against which we measure other compressed subframes */
	_best_subframe = 0;
	_best_bits = stream_encoder_evaluate_verbatim_subframe_(integer_signal, frame_header->blocksize, subframe_bps, subframe[_best_subframe]);

	if(!verbatim_only && frame_header->blocksize >= FLAC__MAX_FIXED_ORDER) {
		/* check for constant subframe */
		if(encoder->private->use_slow)
			guess_fixed_order = FLAC__fixed_compute_best_predictor_slow(integer_signal+FLAC__MAX_FIXED_ORDER, frame_header->blocksize-FLAC__MAX_FIXED_ORDER, fixed_residual_bits_per_sample);
		else
			guess_fixed_order = encoder->private->local_fixed_compute_best_predictor(integer_signal+FLAC__MAX_FIXED_ORDER, frame_header->blocksize-FLAC__MAX_FIXED_ORDER, fixed_residual_bits_per_sample);
		if(fixed_residual_bits_per_sample[1] == 0.0) {
			/* the above means integer_signal+FLAC__MAX_FIXED_ORDER is constant, now we just have to check the warmup samples */
			unsigned i, signal_is_constant = true;
			for(i = 1; i <= FLAC__MAX_FIXED_ORDER; i++) {
				if(integer_signal[0] != integer_signal[i]) {
					signal_is_constant = false;
					break;
				}
			}
			if(signal_is_constant) {
				_candidate_bits = stream_encoder_evaluate_constant_subframe_(integer_signal[0], subframe_bps, subframe[!_best_subframe]);
				if(_candidate_bits < _best_bits) {
					_best_subframe = !_best_subframe;
					_best_bits = _candidate_bits;
				}
			}
		}
		else {
			/* encode fixed */
			if(encoder->protected->do_exhaustive_model_search) {
				min_fixed_order = 0;
				max_fixed_order = FLAC__MAX_FIXED_ORDER;
			}
			else {
				min_fixed_order = max_fixed_order = guess_fixed_order;
			}
			for(fixed_order = min_fixed_order; fixed_order <= max_fixed_order; fixed_order++) {
				if(fixed_residual_bits_per_sample[fixed_order] >= (real)subframe_bps)
					continue; /* don't even try */
				rice_parameter = (fixed_residual_bits_per_sample[fixed_order] > 0.0)? (unsigned)(fixed_residual_bits_per_sample[fixed_order]+0.5) : 0; /* 0.5 is for rounding */
#ifndef FLAC__SYMMETRIC_RICE
				rice_parameter++; /* to account for the signed->unsigned conversion during rice coding */
#endif
				if(rice_parameter >= FLAC__ENTROPY_CODING_METHOD_PARTITIONED_RICE_ESCAPE_PARAMETER)
					rice_parameter = FLAC__ENTROPY_CODING_METHOD_PARTITIONED_RICE_ESCAPE_PARAMETER - 1;
				_candidate_bits = stream_encoder_evaluate_fixed_subframe_(integer_signal, residual[!_best_subframe], encoder->private->abs_residual, encoder->private->abs_residual_partition_sums, encoder->private->raw_bits_per_partition, frame_header->blocksize, subframe_bps, fixed_order, rice_parameter, min_partition_order, max_partition_order, encoder->protected->rice_parameter_search_dist, subframe[!_best_subframe]);
				if(_candidate_bits < _best_bits) {
					_best_subframe = !_best_subframe;
					_best_bits = _candidate_bits;
				}
			}

			/* encode lpc */
			if(encoder->protected->max_lpc_order > 0) {
				if(encoder->protected->max_lpc_order >= frame_header->blocksize)
					max_lpc_order = frame_header->blocksize-1;
				else
					max_lpc_order = encoder->protected->max_lpc_order;
				if(max_lpc_order > 0) {
					encoder->private->local_lpc_compute_autocorrelation(real_signal, frame_header->blocksize, max_lpc_order+1, autoc);
					/* if autoc[0] == 0.0, the signal is constant and we usually won't get here, but it can happen */
					if(autoc[0] != 0.0) {
						FLAC__lpc_compute_lp_coefficients(autoc, max_lpc_order, lp_coeff, lpc_error);
						if(encoder->protected->do_exhaustive_model_search) {
							min_lpc_order = 1;
						}
						else {
							unsigned guess_lpc_order = FLAC__lpc_compute_best_order(lpc_error, max_lpc_order, frame_header->blocksize, subframe_bps);
							min_lpc_order = max_lpc_order = guess_lpc_order;
						}
						if(encoder->protected->do_qlp_coeff_prec_search) {
							min_qlp_coeff_precision = FLAC__MIN_QLP_COEFF_PRECISION;
							max_qlp_coeff_precision = min(32 - subframe_bps - 1, (1u<<FLAC__SUBFRAME_LPC_QLP_COEFF_PRECISION_LEN)-1);
						}
						else {
							min_qlp_coeff_precision = max_qlp_coeff_precision = encoder->protected->qlp_coeff_precision;
						}
						for(lpc_order = min_lpc_order; lpc_order <= max_lpc_order; lpc_order++) {
							lpc_residual_bits_per_sample = FLAC__lpc_compute_expected_bits_per_residual_sample(lpc_error[lpc_order-1], frame_header->blocksize-lpc_order);
							if(lpc_residual_bits_per_sample >= (real)subframe_bps)
								continue; /* don't even try */
							rice_parameter = (lpc_residual_bits_per_sample > 0.0)? (unsigned)(lpc_residual_bits_per_sample+0.5) : 0; /* 0.5 is for rounding */
#ifndef FLAC__SYMMETRIC_RICE
							rice_parameter++; /* to account for the signed->unsigned conversion during rice coding */
#endif
							if(rice_parameter >= FLAC__ENTROPY_CODING_METHOD_PARTITIONED_RICE_ESCAPE_PARAMETER)
								rice_parameter = FLAC__ENTROPY_CODING_METHOD_PARTITIONED_RICE_ESCAPE_PARAMETER - 1;
							for(qlp_coeff_precision = min_qlp_coeff_precision; qlp_coeff_precision <= max_qlp_coeff_precision; qlp_coeff_precision++) {
								_candidate_bits = stream_encoder_evaluate_lpc_subframe_(encoder, integer_signal, residual[!_best_subframe], encoder->private->abs_residual, encoder->private->abs_residual_partition_sums, encoder->private->raw_bits_per_partition, lp_coeff[lpc_order-1], frame_header->blocksize, subframe_bps, lpc_order, qlp_coeff_precision, rice_parameter, min_partition_order, max_partition_order, encoder->protected->rice_parameter_search_dist, subframe[!_best_subframe]);
								if(_candidate_bits > 0) { /* if == 0, there was a problem quantizing the lpcoeffs */
									if(_candidate_bits < _best_bits) {
										_best_subframe = !_best_subframe;
										_best_bits = _candidate_bits;
									}
								}
							}
						}
					}
				}
			}
		}
	}

	*best_subframe = _best_subframe;
	*best_bits = _best_bits;

	return true;
}

bool stream_encoder_add_subframe_(FLAC__StreamEncoder *encoder, const FLAC__FrameHeader *frame_header, unsigned subframe_bps, const FLAC__Subframe *subframe, FLAC__BitBuffer *frame)
{
	switch(subframe->type) {
		case FLAC__SUBFRAME_TYPE_CONSTANT:
			if(!FLAC__subframe_add_constant(&(subframe->data.constant), subframe_bps, subframe->wasted_bits, frame)) {
				encoder->protected->state = FLAC__STREAM_ENCODER_FATAL_ERROR_WHILE_ENCODING;
				return false;
			}
			break;
		case FLAC__SUBFRAME_TYPE_FIXED:
			if(!FLAC__subframe_add_fixed(&(subframe->data.fixed), frame_header->blocksize - subframe->data.fixed.order, subframe_bps, subframe->wasted_bits, frame)) {
				encoder->protected->state = FLAC__STREAM_ENCODER_FATAL_ERROR_WHILE_ENCODING;
				return false;
			}
			break;
		case FLAC__SUBFRAME_TYPE_LPC:
			if(!FLAC__subframe_add_lpc(&(subframe->data.lpc), frame_header->blocksize - subframe->data.lpc.order, subframe_bps, subframe->wasted_bits, frame)) {
				encoder->protected->state = FLAC__STREAM_ENCODER_FATAL_ERROR_WHILE_ENCODING;
				return false;
			}
			break;
		case FLAC__SUBFRAME_TYPE_VERBATIM:
			if(!FLAC__subframe_add_verbatim(&(subframe->data.verbatim), frame_header->blocksize, subframe_bps, subframe->wasted_bits, frame)) {
				encoder->protected->state = FLAC__STREAM_ENCODER_FATAL_ERROR_WHILE_ENCODING;
				return false;
			}
			break;
		default:
			FLAC__ASSERT(0);
	}

	return true;
}

unsigned stream_encoder_evaluate_constant_subframe_(const int32 signal, unsigned subframe_bps, FLAC__Subframe *subframe)
{
	subframe->type = FLAC__SUBFRAME_TYPE_CONSTANT;
	subframe->data.constant.value = signal;

	return FLAC__SUBFRAME_ZERO_PAD_LEN + FLAC__SUBFRAME_TYPE_LEN + FLAC__SUBFRAME_WASTED_BITS_FLAG_LEN + subframe_bps;
}

unsigned stream_encoder_evaluate_fixed_subframe_(const int32 signal[], int32 residual[], uint32 abs_residual[], uint32 abs_residual_partition_sums[], unsigned raw_bits_per_partition[], unsigned blocksize, unsigned subframe_bps, unsigned order, unsigned rice_parameter, unsigned min_partition_order, unsigned max_partition_order, unsigned rice_parameter_search_dist, FLAC__Subframe *subframe)
{
	unsigned i, residual_bits;
	const unsigned residual_samples = blocksize - order;

	FLAC__fixed_compute_residual(signal+order, residual_samples, order, residual);

	subframe->type = FLAC__SUBFRAME_TYPE_FIXED;

	subframe->data.fixed.entropy_coding_method.type = FLAC__ENTROPY_CODING_METHOD_PARTITIONED_RICE;
	subframe->data.fixed.residual = residual;

	residual_bits = stream_encoder_find_best_partition_order_(residual, abs_residual, abs_residual_partition_sums, raw_bits_per_partition, residual_samples, order, rice_parameter, min_partition_order, max_partition_order, rice_parameter_search_dist, &subframe->data.fixed.entropy_coding_method.data.partitioned_rice.order, subframe->data.fixed.entropy_coding_method.data.partitioned_rice.parameters, subframe->data.fixed.entropy_coding_method.data.partitioned_rice.raw_bits);

	subframe->data.fixed.order = order;
	for(i = 0; i < order; i++)
		subframe->data.fixed.warmup[i] = signal[i];

	return FLAC__SUBFRAME_ZERO_PAD_LEN + FLAC__SUBFRAME_TYPE_LEN + FLAC__SUBFRAME_WASTED_BITS_FLAG_LEN + (order * subframe_bps) + residual_bits;
}

unsigned stream_encoder_evaluate_lpc_subframe_(FLAC__StreamEncoder *encoder, const int32 signal[], int32 residual[], uint32 abs_residual[], uint32 abs_residual_partition_sums[], unsigned raw_bits_per_partition[], const real lp_coeff[], unsigned blocksize, unsigned subframe_bps, unsigned order, unsigned qlp_coeff_precision, unsigned rice_parameter, unsigned min_partition_order, unsigned max_partition_order, unsigned rice_parameter_search_dist, FLAC__Subframe *subframe)
{
	int32 qlp_coeff[FLAC__MAX_LPC_ORDER];
	unsigned i, residual_bits;
	int quantization, ret;
	const unsigned residual_samples = blocksize - order;

	ret = FLAC__lpc_quantize_coefficients(lp_coeff, order, qlp_coeff_precision, subframe_bps, qlp_coeff, &quantization);
	if(ret != 0)
		return 0; /* this is a hack to indicate to the caller that we can't do lp at this order on this subframe */

	if(subframe_bps <= 16 && qlp_coeff_precision <= 16)
		encoder->private->local_lpc_compute_residual_from_qlp_coefficients_16bit(signal+order, residual_samples, qlp_coeff, order, quantization, residual);
	else
		encoder->private->local_lpc_compute_residual_from_qlp_coefficients(signal+order, residual_samples, qlp_coeff, order, quantization, residual);

	subframe->type = FLAC__SUBFRAME_TYPE_LPC;

	subframe->data.lpc.entropy_coding_method.type = FLAC__ENTROPY_CODING_METHOD_PARTITIONED_RICE;
	subframe->data.lpc.residual = residual;

	residual_bits = stream_encoder_find_best_partition_order_(residual, abs_residual, abs_residual_partition_sums, raw_bits_per_partition, residual_samples, order, rice_parameter, min_partition_order, max_partition_order, rice_parameter_search_dist, &subframe->data.lpc.entropy_coding_method.data.partitioned_rice.order, subframe->data.lpc.entropy_coding_method.data.partitioned_rice.parameters, subframe->data.lpc.entropy_coding_method.data.partitioned_rice.raw_bits);

	subframe->data.lpc.order = order;
	subframe->data.lpc.qlp_coeff_precision = qlp_coeff_precision;
	subframe->data.lpc.quantization_level = quantization;
	memcpy(subframe->data.lpc.qlp_coeff, qlp_coeff, sizeof(int32)*FLAC__MAX_LPC_ORDER);
	for(i = 0; i < order; i++)
		subframe->data.lpc.warmup[i] = signal[i];

	return FLAC__SUBFRAME_ZERO_PAD_LEN + FLAC__SUBFRAME_TYPE_LEN + FLAC__SUBFRAME_WASTED_BITS_FLAG_LEN + FLAC__SUBFRAME_LPC_QLP_COEFF_PRECISION_LEN + FLAC__SUBFRAME_LPC_QLP_SHIFT_LEN + (order * (qlp_coeff_precision + subframe_bps)) + residual_bits;
}

unsigned stream_encoder_evaluate_verbatim_subframe_(const int32 signal[], unsigned blocksize, unsigned subframe_bps, FLAC__Subframe *subframe)
{
	subframe->type = FLAC__SUBFRAME_TYPE_VERBATIM;

	subframe->data.verbatim.data = signal;

	return FLAC__SUBFRAME_ZERO_PAD_LEN + FLAC__SUBFRAME_TYPE_LEN + FLAC__SUBFRAME_WASTED_BITS_FLAG_LEN + (blocksize * subframe_bps);
}

unsigned stream_encoder_find_best_partition_order_(const int32 residual[], uint32 abs_residual[], uint32 abs_residual_partition_sums[], unsigned raw_bits_per_partition[], unsigned residual_samples, unsigned predictor_order, unsigned rice_parameter, unsigned min_partition_order, unsigned max_partition_order, unsigned rice_parameter_search_dist, unsigned *best_partition_order, unsigned best_parameters[], unsigned best_raw_bits[])
{
	int32 r;
#if (defined FLAC__PRECOMPUTE_PARTITION_SUMS) || (defined FLAC__SEARCH_FOR_ESCAPES)
	unsigned sum;
	int partition_order;
#else
	unsigned partition_order;
#endif
	unsigned residual_bits, best_residual_bits = 0;
	unsigned residual_sample;
	unsigned best_parameters_index = 0, parameters[2][1 << FLAC__MAX_RICE_PARTITION_ORDER], raw_bits[2][1 << FLAC__MAX_RICE_PARTITION_ORDER];

	/* compute abs(residual) for use later */
	for(residual_sample = 0; residual_sample < residual_samples; residual_sample++) {
		r = residual[residual_sample];
		abs_residual[residual_sample] = (uint32)(r<0? -r : r);
	}

#if (defined FLAC__PRECOMPUTE_PARTITION_SUMS) || (defined FLAC__SEARCH_FOR_ESCAPES)
	max_partition_order = stream_encoder_precompute_partition_info_(residual, abs_residual, abs_residual_partition_sums, raw_bits_per_partition, residual_samples, predictor_order, min_partition_order, max_partition_order);
	min_partition_order = min(min_partition_order, max_partition_order);

	for(partition_order = (int)max_partition_order, sum = 0; partition_order >= (int)min_partition_order; partition_order--) {
		if(!stream_encoder_set_partitioned_rice_(abs_residual, abs_residual_partition_sums+sum, raw_bits_per_partition+sum, residual_samples, predictor_order, rice_parameter, rice_parameter_search_dist, (unsigned)partition_order, parameters[!best_parameters_index], raw_bits[!best_parameters_index], &residual_bits)) {
			FLAC__ASSERT(0); /* stream_encoder_precompute_partition_info_ should keep this from ever happening */
		}
		sum += 1u << partition_order;
		if(best_residual_bits == 0 || residual_bits < best_residual_bits) {
			best_residual_bits = residual_bits;
			*best_partition_order = partition_order;
			best_parameters_index = !best_parameters_index;
		}
	}
#else
	for(partition_order = min_partition_order; partition_order <= max_partition_order; partition_order++) {
		if(!stream_encoder_set_partitioned_rice_(abs_residual, 0, 0, residual_samples, predictor_order, rice_parameter, rice_parameter_search_dist, partition_order, parameters[!best_parameters_index], raw_bits[!best_parameters_index], &residual_bits)) {
			FLAC__ASSERT(best_residual_bits != 0);
			break;
		}
		if(best_residual_bits == 0 || residual_bits < best_residual_bits) {
			best_residual_bits = residual_bits;
			*best_partition_order = partition_order;
			best_parameters_index = !best_parameters_index;
		}
	}
#endif
	memcpy(best_parameters, parameters[best_parameters_index], sizeof(unsigned)*(1<<(*best_partition_order)));
	memcpy(best_raw_bits, raw_bits[best_parameters_index], sizeof(unsigned)*(1<<(*best_partition_order)));

	return best_residual_bits;
}

#if (defined FLAC__PRECOMPUTE_PARTITION_SUMS) || (defined FLAC__SEARCH_FOR_ESCAPES)
unsigned stream_encoder_precompute_partition_info_(const int32 residual[], uint32 abs_residual[], uint32 abs_residual_partition_sums[], unsigned raw_bits_per_partition[], unsigned residual_samples, unsigned predictor_order, unsigned min_partition_order, unsigned max_partition_order)
{
	int partition_order;
	unsigned from_partition, to_partition = 0;
	const unsigned blocksize = residual_samples + predictor_order;

	/* first do max_partition_order */
	for(partition_order = (int)max_partition_order; partition_order >= 0; partition_order--) {
#ifdef FLAC__PRECOMPUTE_PARTITION_SUMS
		uint32 abs_residual_partition_sum;
#endif
#ifdef FLAC__SEARCH_FOR_ESCAPES
		uint32 abs_residual_partition_max;
		unsigned abs_residual_partition_max_index = 0; /* initialized to silence superfluous compiler warning */
#endif
		uint32 abs_r;
		unsigned partition, partition_sample, partition_samples, residual_sample;
		const unsigned partitions = 1u << partition_order;
		const unsigned default_partition_samples = blocksize >> partition_order;

		if(default_partition_samples <= predictor_order) {
			FLAC__ASSERT(max_partition_order > 0);
			max_partition_order--;
		}
		else {
			for(partition = residual_sample = 0; partition < partitions; partition++) {
				partition_samples = default_partition_samples;
				if(partition == 0)
					partition_samples -= predictor_order;
#ifdef FLAC__PRECOMPUTE_PARTITION_SUMS
				abs_residual_partition_sum = 0;
#endif
#ifdef FLAC__SEARCH_FOR_ESCAPES
				abs_residual_partition_max = 0;
#endif
				for(partition_sample = 0; partition_sample < partition_samples; partition_sample++) {
					abs_r = abs_residual[residual_sample];
#ifdef FLAC__PRECOMPUTE_PARTITION_SUMS
					abs_residual_partition_sum += abs_r; /* @@@ this can overflow with small max_partition_order and (large blocksizes or bits-per-sample), FIX! */
#endif
#ifdef FLAC__SEARCH_FOR_ESCAPES
					if(abs_r > abs_residual_partition_max) {
						abs_residual_partition_max = abs_r;
						abs_residual_partition_max_index = residual_sample;
					}
#endif
					residual_sample++;
				}
#ifdef FLAC__PRECOMPUTE_PARTITION_SUMS
				abs_residual_partition_sums[partition] = abs_residual_partition_sum;
#endif
#ifdef FLAC__SEARCH_FOR_ESCAPES
				if(abs_residual_partition_max > 0)
					raw_bits_per_partition[partition] = FLAC__bitmath_silog2(residual[abs_residual_partition_max_index]);
				else
					raw_bits_per_partition[partition] = FLAC__bitmath_silog2(0);
#endif
			}
			to_partition = partitions;
			break;
		}
	}

	/* now merge for lower orders */
	for(from_partition = 0, --partition_order; partition_order >= (int)min_partition_order; partition_order--) {
#ifdef FLAC__PRECOMPUTE_PARTITION_SUMS
		uint32 s;
#endif
#ifdef FLAC__SEARCH_FOR_ESCAPES
		unsigned m;
#endif
		unsigned i;
		const unsigned partitions = 1u << partition_order;
		for(i = 0; i < partitions; i++) {
#ifdef FLAC__PRECOMPUTE_PARTITION_SUMS
			s = abs_residual_partition_sums[from_partition];
#endif
#ifdef FLAC__SEARCH_FOR_ESCAPES
			m = raw_bits_per_partition[from_partition];
#endif
			from_partition++;
#ifdef FLAC__PRECOMPUTE_PARTITION_SUMS
			abs_residual_partition_sums[to_partition] = s + abs_residual_partition_sums[from_partition];
#endif
#ifdef FLAC__SEARCH_FOR_ESCAPES
			raw_bits_per_partition[to_partition] = max(m, raw_bits_per_partition[from_partition]);
#endif
			from_partition++;
			to_partition++;
		}
	}

	return max_partition_order;
}
#endif

#ifdef VARIABLE_RICE_BITS
#undef VARIABLE_RICE_BITS
#endif
#define VARIABLE_RICE_BITS(value, parameter) ((value) >> (parameter))

bool stream_encoder_set_partitioned_rice_(const uint32 abs_residual[], const uint32 abs_residual_partition_sums[], const unsigned raw_bits_per_partition[], const unsigned residual_samples, const unsigned predictor_order, const unsigned suggested_rice_parameter, const unsigned rice_parameter_search_dist, const unsigned partition_order, unsigned parameters[], unsigned raw_bits[], unsigned *bits)
{
	unsigned rice_parameter, partition_bits;
#ifndef NO_RICE_SEARCH
	unsigned best_partition_bits;
	unsigned min_rice_parameter, max_rice_parameter, best_rice_parameter = 0;
#endif
#ifdef FLAC__SEARCH_FOR_ESCAPES
	unsigned flat_bits;
#endif
	unsigned bits_ = FLAC__ENTROPY_CODING_METHOD_TYPE_LEN + FLAC__ENTROPY_CODING_METHOD_PARTITIONED_RICE_ORDER_LEN;

	FLAC__ASSERT(suggested_rice_parameter < FLAC__ENTROPY_CODING_METHOD_PARTITIONED_RICE_ESCAPE_PARAMETER);

	if(partition_order == 0) {
		unsigned i;

#ifndef NO_RICE_SEARCH
		if(rice_parameter_search_dist) {
			if(suggested_rice_parameter < rice_parameter_search_dist)
				min_rice_parameter = 0;
			else
				min_rice_parameter = suggested_rice_parameter - rice_parameter_search_dist;
			max_rice_parameter = suggested_rice_parameter + rice_parameter_search_dist;
			if(max_rice_parameter >= FLAC__ENTROPY_CODING_METHOD_PARTITIONED_RICE_ESCAPE_PARAMETER)
				max_rice_parameter = FLAC__ENTROPY_CODING_METHOD_PARTITIONED_RICE_ESCAPE_PARAMETER - 1;
		}
		else
			min_rice_parameter = max_rice_parameter = suggested_rice_parameter;

		best_partition_bits = 0xffffffff;
		for(rice_parameter = min_rice_parameter; rice_parameter <= max_rice_parameter; rice_parameter++) {
#endif
#ifdef VARIABLE_RICE_BITS
#ifdef FLAC__SYMMETRIC_RICE
			partition_bits = (2+rice_parameter) * residual_samples;
#else
			const unsigned rice_parameter_estimate = rice_parameter-1;
			partition_bits = (1+rice_parameter) * residual_samples;
#endif
#else
			partition_bits = 0;
#endif
			partition_bits += FLAC__ENTROPY_CODING_METHOD_PARTITIONED_RICE_PARAMETER_LEN;
			for(i = 0; i < residual_samples; i++) {
#ifdef VARIABLE_RICE_BITS
#ifdef FLAC__SYMMETRIC_RICE
				partition_bits += VARIABLE_RICE_BITS(abs_residual[i], rice_parameter);
#else
				partition_bits += VARIABLE_RICE_BITS(abs_residual[i], rice_parameter_estimate);
#endif
#else
				partition_bits += FLAC__bitbuffer_rice_bits(residual[i], rice_parameter); /* NOTE: we will need to pass in residual[] instead of abs_residual[] */
#endif
			}
#ifndef NO_RICE_SEARCH
			if(partition_bits < best_partition_bits) {
				best_rice_parameter = rice_parameter;
				best_partition_bits = partition_bits;
			}
		}
#endif
#ifdef FLAC__SEARCH_FOR_ESCAPES
		flat_bits = raw_bits_per_partition[0] * residual_samples;
		if(flat_bits <= best_partition_bits) {
			raw_bits[0] = raw_bits_per_partition[0];
			best_rice_parameter = FLAC__ENTROPY_CODING_METHOD_PARTITIONED_RICE_ESCAPE_PARAMETER;
			best_partition_bits = flat_bits;
		}
#endif
		parameters[0] = best_rice_parameter;
		bits_ += best_partition_bits;
	}
	else {
		unsigned partition, residual_sample, save_residual_sample, partition_sample;
		unsigned mean, partition_samples;
		const unsigned partitions = 1u << partition_order;
		for(partition = residual_sample = 0; partition < partitions; partition++) {
			partition_samples = (residual_samples+predictor_order) >> partition_order;
			if(partition == 0) {
				if(partition_samples <= predictor_order)
					return false;
				else
					partition_samples -= predictor_order;
			}
			mean = partition_samples >> 1;
#ifdef FLAC__PRECOMPUTE_PARTITION_SUMS
			mean += abs_residual_partition_sums[partition];
#else
			save_residual_sample = residual_sample;
			for(partition_sample = 0; partition_sample < partition_samples; residual_sample++, partition_sample++)
				mean += abs_residual[residual_sample];
			residual_sample = save_residual_sample;
#endif
			mean /= partition_samples;
#ifdef FLAC__SYMMETRIC_RICE
			/* calc rice_parameter = floor(log2(mean)) */
			rice_parameter = 0;
			mean>>=1;
			while(mean) {
				rice_parameter++;
				mean >>= 1;
			}
#else
			/* calc rice_parameter = floor(log2(mean)) + 1 */
			rice_parameter = 0;
			while(mean) {
				rice_parameter++;
				mean >>= 1;
			}
#endif
			if(rice_parameter >= FLAC__ENTROPY_CODING_METHOD_PARTITIONED_RICE_ESCAPE_PARAMETER)
				rice_parameter = FLAC__ENTROPY_CODING_METHOD_PARTITIONED_RICE_ESCAPE_PARAMETER - 1;

#ifndef NO_RICE_SEARCH
			if(rice_parameter_search_dist) {
				if(rice_parameter < rice_parameter_search_dist)
					min_rice_parameter = 0;
				else
					min_rice_parameter = rice_parameter - rice_parameter_search_dist;
				max_rice_parameter = rice_parameter + rice_parameter_search_dist;
				if(max_rice_parameter >= FLAC__ENTROPY_CODING_METHOD_PARTITIONED_RICE_ESCAPE_PARAMETER)
					max_rice_parameter = FLAC__ENTROPY_CODING_METHOD_PARTITIONED_RICE_ESCAPE_PARAMETER - 1;
			}
			else
				min_rice_parameter = max_rice_parameter = rice_parameter;

			best_partition_bits = 0xffffffff;
			for(rice_parameter = min_rice_parameter; rice_parameter <= max_rice_parameter; rice_parameter++) {
#endif
#ifdef VARIABLE_RICE_BITS
#ifdef FLAC__SYMMETRIC_RICE
				partition_bits = (2+rice_parameter) * partition_samples;
#else
				const unsigned rice_parameter_estimate = rice_parameter-1;
				partition_bits = (1+rice_parameter) * partition_samples;
#endif
#else
				partition_bits = 0;
#endif
				partition_bits += FLAC__ENTROPY_CODING_METHOD_PARTITIONED_RICE_PARAMETER_LEN;
				save_residual_sample = residual_sample;
				for(partition_sample = 0; partition_sample < partition_samples; residual_sample++, partition_sample++) {
#ifdef VARIABLE_RICE_BITS
#ifdef FLAC__SYMMETRIC_RICE
					partition_bits += VARIABLE_RICE_BITS(abs_residual[residual_sample], rice_parameter);
#else
					partition_bits += VARIABLE_RICE_BITS(abs_residual[residual_sample], rice_parameter_estimate);
#endif
#else
					partition_bits += FLAC__bitbuffer_rice_bits(residual[residual_sample], rice_parameter); /* NOTE: we will need to pass in residual[] instead of abs_residual[] */
#endif
				}
#ifndef NO_RICE_SEARCH
				if(rice_parameter != max_rice_parameter)
					residual_sample = save_residual_sample;
				if(partition_bits < best_partition_bits) {
					best_rice_parameter = rice_parameter;
					best_partition_bits = partition_bits;
				}
			}
#endif
#ifdef FLAC__SEARCH_FOR_ESCAPES
			flat_bits = raw_bits_per_partition[partition] * partition_samples;
			if(flat_bits <= best_partition_bits) {
				raw_bits[partition] = raw_bits_per_partition[partition];
				best_rice_parameter = FLAC__ENTROPY_CODING_METHOD_PARTITIONED_RICE_ESCAPE_PARAMETER;
				best_partition_bits = flat_bits;
			}
#endif
			parameters[partition] = best_rice_parameter;
			bits_ += best_partition_bits;
		}
	}

	*bits = bits_;
	return true;
}

unsigned stream_encoder_get_wasted_bits_(int32 signal[], unsigned samples)
{
	unsigned i, shift;
	int32 x = 0;

	for(i = 0; i < samples && !(x&1); i++)
		x |= signal[i];

	if(x == 0) {
		shift = 0;
	}
	else {
		for(shift = 0; !(x&1); shift++)
			x >>= 1;
	}

	if(shift > 0) {
		for(i = 0; i < samples; i++)
			 signal[i] >>= shift;
	}

	return shift;
}

