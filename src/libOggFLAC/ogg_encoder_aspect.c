/* libOggFLAC - Free Lossless Audio Codec + Ogg library
 * Copyright (C) 2002,2003,2004  Josh Coalson
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * - Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * - Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * - Neither the name of the Xiph.org Foundation nor the names of its
 * contributors may be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * ``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE FOUNDATION OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#include <string.h> /* for memset() */
#include "FLAC/assert.h"
#include "private/ogg_encoder_aspect.h"

/***********************************************************************
 *
 * Public class methods
 *
 ***********************************************************************/

FLAC__bool OggFLAC__ogg_encoder_aspect_init(OggFLAC__OggEncoderAspect *aspect)
{
	/* we will determine the serial number later if necessary */
	if(ogg_stream_init(&aspect->stream_state, aspect->serial_number) != 0)
		return false;

	aspect->seen_magic = false;
	aspect->is_first_packet = true;
	aspect->samples_written = 0;

	return true;
}

void OggFLAC__ogg_encoder_aspect_finish(OggFLAC__OggEncoderAspect *aspect)
{
	(void)ogg_stream_clear(&aspect->stream_state);
	/*@@@ what aobut the page? */
}

void OggFLAC__ogg_encoder_aspect_set_serial_number(OggFLAC__OggEncoderAspect *aspect, long value)
{
	aspect->serial_number = value;
}

void OggFLAC__ogg_encoder_aspect_set_defaults(OggFLAC__OggEncoderAspect *aspect)
{
	aspect->serial_number = 0;
}

/*
 * The basic FLAC -> Ogg mapping goes like this:
 *
 * - 'fLaC' magic and STREAMINFO block get combined into the first
 *   packet
 * - the first packet is flushed to the first page
 * - each subsequent metadata block goes into its own packet
 * - each metadata packet is flushed to page (this is not required,
 *   the mapping only requires that a flush must occur after all
 *   metadata is written)
 * - each subsequent FLAC audio frame goes into its own packet.
 *
 * WATCHOUT:
 * This depends on the behavior of FLAC__StreamEncoder that we get a
 * separate write callback for the fLaC magic, and then separate write
 * callbacks for each metadata block and audio frame.
 */
FLAC__StreamEncoderWriteStatus OggFLAC__ogg_encoder_aspect_write_callback_wrapper(OggFLAC__OggEncoderAspect *aspect, const FLAC__uint64 total_samples_estimate, const FLAC__byte buffer[], unsigned bytes, unsigned samples, unsigned current_frame, OggFLAC__OggEncoderAspectWriteCallbackProxy write_callback, void *encoder, void *client_data)
{
	/* WATCHOUT:
	 * This depends on the behavior of FLAC__StreamEncoder that 'samples'
	 * will be 0 for metadata writes.
	 */
	const FLAC__bool is_metadata = (samples == 0);

	/*
	 * Treat fLaC magic packet specially.  We will note when we see it, then
	 * wait until we get the STREAMINFO and prepend it in that packet
	 */
	if(aspect->seen_magic) {
		ogg_packet packet;

		memset(&packet, 0, sizeof(packet));
		packet.granulepos = aspect->samples_written + samples;

		if(aspect->is_first_packet) {
			FLAC__byte newbuffer[FLAC__STREAM_SYNC_LENGTH + FLAC__STREAM_METADATA_HEADER_LENGTH + FLAC__STREAM_METADATA_STREAMINFO_LENGTH];
			if(bytes != FLAC__STREAM_METADATA_HEADER_LENGTH + FLAC__STREAM_METADATA_STREAMINFO_LENGTH) {
				/*
				 * If we get here, our assumption about the way write callbacks happen
				 * explained above is wrong
				 */
				FLAC__ASSERT(0);
				return FLAC__STREAM_ENCODER_WRITE_STATUS_FATAL_ERROR;
			}
			memcpy(newbuffer, FLAC__STREAM_SYNC_STRING, FLAC__STREAM_SYNC_LENGTH);
			memcpy(newbuffer + FLAC__STREAM_SYNC_LENGTH, buffer, bytes);
			packet.packet = (unsigned char *)newbuffer;
			packet.bytes = sizeof(newbuffer);

			packet.b_o_s = 1;
			aspect->is_first_packet = false;
		}
		else {
			packet.packet = (unsigned char *)buffer;
			packet.bytes = bytes;
		}

		if(total_samples_estimate > 0 && total_samples_estimate == aspect->samples_written + samples)
			packet.e_o_s = 1;

		if(ogg_stream_packetin(&aspect->stream_state, &packet) != 0)
			return FLAC__STREAM_ENCODER_WRITE_STATUS_FATAL_ERROR;

		/*@@@@@@ can't figure out a way to pass a useful number for 'samples' to the write_callback, so we'll just pass 0 */
		if(is_metadata) {
			while(ogg_stream_flush(&aspect->stream_state, &aspect->page) != 0) {
				if(write_callback(encoder, aspect->page.header, aspect->page.header_len, 0, current_frame, client_data) != FLAC__STREAM_ENCODER_WRITE_STATUS_OK)
					return FLAC__STREAM_ENCODER_WRITE_STATUS_FATAL_ERROR;
				if(write_callback(encoder, aspect->page.body, aspect->page.body_len, 0, current_frame, client_data) != FLAC__STREAM_ENCODER_WRITE_STATUS_OK)
					return FLAC__STREAM_ENCODER_WRITE_STATUS_FATAL_ERROR;
			}
		}
		else {
			while(ogg_stream_pageout(&aspect->stream_state, &aspect->page) != 0) {
				if(write_callback(encoder, aspect->page.header, aspect->page.header_len, 0, current_frame, client_data) != FLAC__STREAM_ENCODER_WRITE_STATUS_OK)
					return FLAC__STREAM_ENCODER_WRITE_STATUS_FATAL_ERROR;
				if(write_callback(encoder, aspect->page.body, aspect->page.body_len, 0, current_frame, client_data) != FLAC__STREAM_ENCODER_WRITE_STATUS_OK)
					return FLAC__STREAM_ENCODER_WRITE_STATUS_FATAL_ERROR;
			}
		}
	}
	else if(is_metadata && current_frame == 0 && samples == 0 && bytes == 4 && 0 == memcmp(buffer, FLAC__STREAM_SYNC_STRING, sizeof(FLAC__STREAM_SYNC_STRING))) {
		aspect->seen_magic = true;
	}
	else {
		/*
		 * If we get here, our assumption about the way write callbacks happen
		 * explained above is wrong
		 */
		FLAC__ASSERT(0);
		return FLAC__STREAM_ENCODER_WRITE_STATUS_FATAL_ERROR;
	}

	aspect->samples_written += samples;

	return FLAC__STREAM_ENCODER_WRITE_STATUS_OK;
}
