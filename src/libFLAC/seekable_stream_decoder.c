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
#include "FLAC/assert.h"
#include "protected/seekable_stream_decoder.h"
#include "protected/stream_decoder.h"
#include "private/md5.h"

/***********************************************************************
 *
 * Private class method prototypes
 *
 ***********************************************************************/

static FLAC__StreamDecoderReadStatus read_callback_(const FLAC__StreamDecoder *decoder, FLAC__byte buffer[], unsigned *bytes, void *client_data);
static FLAC__StreamDecoderWriteStatus write_callback_(const FLAC__StreamDecoder *decoder, const FLAC__Frame *frame, const FLAC__int32 *buffer[], void *client_data);
static void metadata_callback_(const FLAC__StreamDecoder *decoder, const FLAC__StreamMetaData *metadata, void *client_data);
static void error_callback_(const FLAC__StreamDecoder *decoder, FLAC__StreamDecoderErrorStatus status, void *client_data);
static FLAC__bool seek_to_absolute_sample_(FLAC__SeekableStreamDecoder *decoder, FLAC__uint64 stream_length, FLAC__uint64 target_sample);

/***********************************************************************
 *
 * Private class data
 *
 ***********************************************************************/

typedef struct FLAC__SeekableStreamDecoderPrivate {
	FLAC__SeekableStreamDecoderReadStatus (*read_callback)(const FLAC__SeekableStreamDecoder *decoder, FLAC__byte buffer[], unsigned *bytes, void *client_data);
	FLAC__SeekableStreamDecoderSeekStatus (*seek_callback)(const FLAC__SeekableStreamDecoder *decoder, FLAC__uint64 absolute_byte_offset, void *client_data);
	FLAC__SeekableStreamDecoderTellStatus (*tell_callback)(const FLAC__SeekableStreamDecoder *decoder, FLAC__uint64 *absolute_byte_offset, void *client_data);
	FLAC__SeekableStreamDecoderLengthStatus (*length_callback)(const FLAC__SeekableStreamDecoder *decoder, FLAC__uint64 *stream_length, void *client_data);
	FLAC__bool (*eof_callback)(const FLAC__SeekableStreamDecoder *decoder, void *client_data);
	FLAC__StreamDecoderWriteStatus (*write_callback)(const FLAC__SeekableStreamDecoder *decoder, const FLAC__Frame *frame, const FLAC__int32 *buffer[], void *client_data);
	void (*metadata_callback)(const FLAC__SeekableStreamDecoder *decoder, const FLAC__StreamMetaData *metadata, void *client_data);
	void (*error_callback)(const FLAC__SeekableStreamDecoder *decoder, FLAC__StreamDecoderErrorStatus status, void *client_data);
	void *client_data;
	FLAC__StreamDecoder *stream_decoder;
	struct MD5Context md5context;
	FLAC__byte stored_md5sum[16]; /* this is what is stored in the metadata */
	FLAC__byte computed_md5sum[16]; /* this is the sum we computed from the decoded data */
	/* the rest of these are only used for seeking: */
	FLAC__StreamMetaData_StreamInfo stream_info; /* we keep this around so we can figure out how to seek quickly */
	const FLAC__StreamMetaData_SeekTable *seek_table; /* we hold a pointer to the stream decoder's seek table for the same reason */
	FLAC__Frame last_frame; /* holds the info of the last frame we seeked to */
	FLAC__uint64 target_sample;
} FLAC__SeekableStreamDecoderPrivate;

/***********************************************************************
 *
 * Public static class data
 *
 ***********************************************************************/

const char *FLAC__SeekableStreamDecoderStateString[] = {
	"FLAC__SEEKABLE_STREAM_DECODER_OK",
	"FLAC__SEEKABLE_STREAM_DECODER_SEEKING",
	"FLAC__SEEKABLE_STREAM_DECODER_END_OF_STREAM",
	"FLAC__SEEKABLE_STREAM_DECODER_MEMORY_ALLOCATION_ERROR",
	"FLAC__SEEKABLE_STREAM_DECODER_STREAM_ERROR",
	"FLAC__SEEKABLE_STREAM_DECODER_READ_ERROR",
	"FLAC__SEEKABLE_STREAM_DECODER_SEEK_ERROR",
    "FLAC__SEEKABLE_STREAM_DECODER_ALREADY_INITIALIZED",
    "FLAC__SEEKABLE_STREAM_DECODER_INVALID_CALLBACK",
    "FLAC__SEEKABLE_STREAM_DECODER_UNINITIALIZED"
};

const char *FLAC__SeekableStreamDecoderReadStatusString[] = {
	"FLAC__STREAM_DECODER_READ_STATUS_OK",
	"FLAC__STREAM_DECODER_READ_STATUS_ERROR"
};

const char *FLAC__SeekableStreamDecoderSeekStatusString[] = {
	"FLAC__STREAM_DECODER_SEEK_STATUS_OK",
	"FLAC__STREAM_DECODER_SEEK_STATUS_ERROR"
};

const char *FLAC__SeekableStreamDecoderTellStatusString[] = {
	"FLAC__STREAM_DECODER_TELL_STATUS_OK",
	"FLAC__STREAM_DECODER_TELL_STATUS_ERROR"
};

const char *FLAC__SeekableStreamDecoderLengthStatusString[] = {
	"FLAC__STREAM_DECODER_LENGTH_STATUS_OK",
	"FLAC__STREAM_DECODER_LENGTH_STATUS_ERROR"
};

/***********************************************************************
 *
 * Class constructor/destructor
 *
 ***********************************************************************/

FLAC__SeekableStreamDecoder *FLAC__seekable_stream_decoder_new()
{
	FLAC__SeekableStreamDecoder *decoder;

	FLAC__ASSERT(sizeof(int) >= 4); /* we want to die right away if this is not true */

	decoder = (FLAC__SeekableStreamDecoder*)malloc(sizeof(FLAC__SeekableStreamDecoder));
	if(decoder == 0) {
		return 0;
	}
	decoder->protected_ = (FLAC__SeekableStreamDecoderProtected*)malloc(sizeof(FLAC__SeekableStreamDecoderProtected));
	if(decoder->protected_ == 0) {
		free(decoder);
		return 0;
	}
	decoder->private_ = (FLAC__SeekableStreamDecoderPrivate*)malloc(sizeof(FLAC__SeekableStreamDecoderPrivate));
	if(decoder->private_ == 0) {
		free(decoder->protected_);
		free(decoder);
		return 0;
	}

	decoder->protected_->state = FLAC__SEEKABLE_STREAM_DECODER_UNINITIALIZED;

	decoder->private_->read_callback = 0;
	decoder->private_->seek_callback = 0;
	decoder->private_->tell_callback = 0;
	decoder->private_->length_callback = 0;
	decoder->private_->eof_callback = 0;
	decoder->private_->write_callback = 0;
	decoder->private_->metadata_callback = 0;
	decoder->private_->error_callback = 0;
	decoder->private_->client_data = 0;

	return decoder;
}

void FLAC__seekable_stream_decoder_delete(FLAC__SeekableStreamDecoder *decoder)
{
	FLAC__ASSERT(decoder != 0);
	FLAC__ASSERT(decoder->protected_ != 0);
	FLAC__ASSERT(decoder->private_ != 0);

	free(decoder->private_);
	free(decoder->protected_);
	free(decoder);
}

/***********************************************************************
 *
 * Public class methods
 *
 ***********************************************************************/

FLAC__SeekableStreamDecoderState FLAC__seekable_stream_decoder_init(FLAC__SeekableStreamDecoder *decoder)
{
	FLAC__ASSERT(decoder != 0);

	if(decoder->protected_->state != FLAC__SEEKABLE_STREAM_DECODER_UNINITIALIZED)
		return decoder->protected_->state = FLAC__SEEKABLE_STREAM_DECODER_ALREADY_INITIALIZED;

	decoder->protected_->state = FLAC__SEEKABLE_STREAM_DECODER_OK;

	if(0 == decoder->private_->read_callback || 0 == decoder->private_->seek_callback || 0 == decoder->private_->tell_callback || 0 == decoder->private_->length_callback || 0 == decoder->private_->eof_callback)
		return decoder->protected_->state = FLAC__SEEKABLE_STREAM_DECODER_INVALID_CALLBACK;

	if(0 == decoder->private_->write_callback || 0 == decoder->private_->metadata_callback || 0 == decoder->private_->error_callback)
		return decoder->protected_->state = FLAC__SEEKABLE_STREAM_DECODER_INVALID_CALLBACK;

	decoder->private_->stream_decoder = 0;
	decoder->private_->seek_table = 0;

	/* We initialize the MD5Context even though we may never use it.  This is
	 * because md5_checking may be turned on to start and then turned off if a
	 * seek occurs.  So we always init the context here and finalize it in
	 * FLAC__seekable_stream_decoder_finish() to make sure things are always
	 * cleaned up properly.
	 */
	MD5Init(&decoder->private_->md5context);

	decoder->private_->stream_decoder = FLAC__stream_decoder_new();

	if(0 == decoder->private_->stream_decoder)
		return decoder->protected_->state = FLAC__SEEKABLE_STREAM_DECODER_MEMORY_ALLOCATION_ERROR;

	FLAC__stream_decoder_set_read_callback(decoder->private_->stream_decoder, read_callback_);
	FLAC__stream_decoder_set_write_callback(decoder->private_->stream_decoder, write_callback_);
	FLAC__stream_decoder_set_metadata_callback(decoder->private_->stream_decoder, metadata_callback_);
	FLAC__stream_decoder_set_error_callback(decoder->private_->stream_decoder, error_callback_);
	FLAC__stream_decoder_set_client_data(decoder->private_->stream_decoder, decoder);

	if(FLAC__stream_decoder_init(decoder->private_->stream_decoder) != FLAC__STREAM_DECODER_SEARCH_FOR_METADATA)
		return decoder->protected_->state = FLAC__SEEKABLE_STREAM_DECODER_STREAM_ERROR;

	return decoder->protected_->state;
}

FLAC__bool FLAC__seekable_stream_decoder_finish(FLAC__SeekableStreamDecoder *decoder)
{
	FLAC__bool md5_failed = false;

	FLAC__ASSERT(decoder != 0);
	if(decoder->protected_->state == FLAC__SEEKABLE_STREAM_DECODER_UNINITIALIZED)
		return true;
	/* see the comment in FLAC__seekable_stream_decoder_init() as to why we
	 * always call MD5Final()
	 */
	MD5Final(decoder->private_->computed_md5sum, &decoder->private_->md5context);
	if(decoder->private_->stream_decoder != 0) {
		FLAC__stream_decoder_finish(decoder->private_->stream_decoder);
		FLAC__stream_decoder_delete(decoder->private_->stream_decoder);
	}
	if(decoder->protected_->md5_checking) {
		if(memcmp(decoder->private_->stored_md5sum, decoder->private_->computed_md5sum, 16))
			md5_failed = true;
	}
	decoder->protected_->state = FLAC__SEEKABLE_STREAM_DECODER_UNINITIALIZED;
	return !md5_failed;
}

FLAC__bool FLAC__seekable_stream_decoder_set_md5_checking(const FLAC__SeekableStreamDecoder *decoder, FLAC__bool value)
{
	if(decoder->protected_->state != FLAC__SEEKABLE_STREAM_DECODER_UNINITIALIZED)
		return false;
	decoder->protected_->md5_checking = value;
	return true;
}

FLAC__bool FLAC__seekable_stream_decoder_set_read_callback(const FLAC__SeekableStreamDecoder *decoder, FLAC__SeekableStreamDecoderReadStatus (*value)(const FLAC__SeekableStreamDecoder *decoder, FLAC__byte buffer[], unsigned *bytes, void *client_data))
{
	if(decoder->protected_->state != FLAC__SEEKABLE_STREAM_DECODER_UNINITIALIZED)
		return false;
	decoder->private_->read_callback = value;
	return true;
}

FLAC__bool FLAC__seekable_stream_decoder_set_seek_callback(const FLAC__SeekableStreamDecoder *decoder, FLAC__SeekableStreamDecoderSeekStatus (*value)(const FLAC__SeekableStreamDecoder *decoder, FLAC__uint64 absolute_byte_offset, void *client_data))
{
	if(decoder->protected_->state != FLAC__SEEKABLE_STREAM_DECODER_UNINITIALIZED)
		return false;
	decoder->private_->seek_callback = value;
	return true;
}

FLAC__bool FLAC__seekable_stream_decoder_set_tell_callback(const FLAC__SeekableStreamDecoder *decoder, FLAC__SeekableStreamDecoderTellStatus (*value)(const FLAC__SeekableStreamDecoder *decoder, FLAC__uint64 *absolute_byte_offset, void *client_data))
{
	if(decoder->protected_->state != FLAC__SEEKABLE_STREAM_DECODER_UNINITIALIZED)
		return false;
	decoder->private_->tell_callback = value;
	return true;
}

FLAC__bool FLAC__seekable_stream_decoder_set_length_callback(const FLAC__SeekableStreamDecoder *decoder, FLAC__SeekableStreamDecoderLengthStatus (*value)(const FLAC__SeekableStreamDecoder *decoder, FLAC__uint64 *stream_length, void *client_data))
{
	if(decoder->protected_->state != FLAC__SEEKABLE_STREAM_DECODER_UNINITIALIZED)
		return false;
	decoder->private_->length_callback = value;
	return true;
}

FLAC__bool FLAC__seekable_stream_decoder_set_eof_callback(const FLAC__SeekableStreamDecoder *decoder, FLAC__bool (*value)(const FLAC__SeekableStreamDecoder *decoder, void *client_data))
{
	if(decoder->protected_->state != FLAC__SEEKABLE_STREAM_DECODER_UNINITIALIZED)
		return false;
	decoder->private_->eof_callback = value;
	return true;
}

FLAC__bool FLAC__seekable_stream_decoder_set_write_callback(const FLAC__SeekableStreamDecoder *decoder, FLAC__StreamDecoderWriteStatus (*value)(const FLAC__SeekableStreamDecoder *decoder, const FLAC__Frame *frame, const FLAC__int32 *buffer[], void *client_data))
{
	if(decoder->protected_->state != FLAC__SEEKABLE_STREAM_DECODER_UNINITIALIZED)
		return false;
	decoder->private_->write_callback = value;
	return true;
}

FLAC__bool FLAC__seekable_stream_decoder_set_metadata_callback(const FLAC__SeekableStreamDecoder *decoder, void (*value)(const FLAC__SeekableStreamDecoder *decoder, const FLAC__StreamMetaData *metadata, void *client_data))
{
	if(decoder->protected_->state != FLAC__SEEKABLE_STREAM_DECODER_UNINITIALIZED)
		return false;
	decoder->private_->metadata_callback = value;
	return true;
}

FLAC__bool FLAC__seekable_stream_decoder_set_error_callback(const FLAC__SeekableStreamDecoder *decoder, void (*value)(const FLAC__SeekableStreamDecoder *decoder, FLAC__StreamDecoderErrorStatus status, void *client_data))
{
	if(decoder->protected_->state != FLAC__SEEKABLE_STREAM_DECODER_UNINITIALIZED)
		return false;
	decoder->private_->error_callback = value;
	return true;
}

FLAC__bool FLAC__seekable_stream_decoder_set_client_data(const FLAC__SeekableStreamDecoder *decoder, void *value)
{
	if(decoder->protected_->state != FLAC__SEEKABLE_STREAM_DECODER_UNINITIALIZED)
		return false;
	decoder->private_->client_data = value;
	return true;
}

FLAC__SeekableStreamDecoderState FLAC__seekable_stream_decoder_get_state(const FLAC__SeekableStreamDecoder *decoder)
{
	return decoder->protected_->state;
}

FLAC__bool FLAC__seekable_stream_decoder_get_md5_checking(const FLAC__SeekableStreamDecoder *decoder)
{
	return decoder->protected_->md5_checking;
}

FLAC__bool FLAC__seekable_stream_decoder_process_whole_stream(FLAC__SeekableStreamDecoder *decoder)
{
	FLAC__bool ret;
	FLAC__ASSERT(decoder != 0);

	if(decoder->private_->stream_decoder->protected_->state == FLAC__STREAM_DECODER_END_OF_STREAM)
		decoder->protected_->state = FLAC__SEEKABLE_STREAM_DECODER_END_OF_STREAM;

	if(decoder->protected_->state == FLAC__SEEKABLE_STREAM_DECODER_END_OF_STREAM)
		return true;

	FLAC__ASSERT(decoder->protected_->state == FLAC__SEEKABLE_STREAM_DECODER_OK);

	ret = FLAC__stream_decoder_process_whole_stream(decoder->private_->stream_decoder);
	if(!ret)
		decoder->protected_->state = FLAC__SEEKABLE_STREAM_DECODER_STREAM_ERROR;

	return ret;
}

FLAC__bool FLAC__seekable_stream_decoder_process_metadata(FLAC__SeekableStreamDecoder *decoder)
{
	FLAC__bool ret;
	FLAC__ASSERT(decoder != 0);

	if(decoder->private_->stream_decoder->protected_->state == FLAC__STREAM_DECODER_END_OF_STREAM)
		decoder->protected_->state = FLAC__SEEKABLE_STREAM_DECODER_END_OF_STREAM;

	if(decoder->protected_->state == FLAC__SEEKABLE_STREAM_DECODER_END_OF_STREAM)
		return true;

	FLAC__ASSERT(decoder->protected_->state == FLAC__SEEKABLE_STREAM_DECODER_OK);

	ret = FLAC__stream_decoder_process_metadata(decoder->private_->stream_decoder);
	if(!ret)
		decoder->protected_->state = FLAC__SEEKABLE_STREAM_DECODER_STREAM_ERROR;

	return ret;
}

FLAC__bool FLAC__seekable_stream_decoder_process_one_frame(FLAC__SeekableStreamDecoder *decoder)
{
	FLAC__bool ret;
	FLAC__ASSERT(decoder != 0);

	if(decoder->private_->stream_decoder->protected_->state == FLAC__STREAM_DECODER_END_OF_STREAM)
		decoder->protected_->state = FLAC__SEEKABLE_STREAM_DECODER_END_OF_STREAM;

	if(decoder->protected_->state == FLAC__SEEKABLE_STREAM_DECODER_END_OF_STREAM)
		return true;

	FLAC__ASSERT(decoder->protected_->state == FLAC__SEEKABLE_STREAM_DECODER_OK);

	ret = FLAC__stream_decoder_process_one_frame(decoder->private_->stream_decoder);
	if(!ret)
		decoder->protected_->state = FLAC__SEEKABLE_STREAM_DECODER_STREAM_ERROR;

	return ret;
}

FLAC__bool FLAC__seekable_stream_decoder_process_remaining_frames(FLAC__SeekableStreamDecoder *decoder)
{
	FLAC__bool ret;
	FLAC__ASSERT(decoder != 0);

	if(decoder->private_->stream_decoder->protected_->state == FLAC__STREAM_DECODER_END_OF_STREAM)
		decoder->protected_->state = FLAC__SEEKABLE_STREAM_DECODER_END_OF_STREAM;

	if(decoder->protected_->state == FLAC__SEEKABLE_STREAM_DECODER_END_OF_STREAM)
		return true;

	FLAC__ASSERT(decoder->protected_->state == FLAC__SEEKABLE_STREAM_DECODER_OK);

	ret = FLAC__stream_decoder_process_remaining_frames(decoder->private_->stream_decoder);
	if(!ret)
		decoder->protected_->state = FLAC__SEEKABLE_STREAM_DECODER_STREAM_ERROR;

	return ret;
}

FLAC__bool FLAC__seekable_stream_decoder_seek_absolute(FLAC__SeekableStreamDecoder *decoder, FLAC__uint64 sample)
{
	FLAC__uint64 length;

	FLAC__ASSERT(decoder != 0);
	FLAC__ASSERT(decoder->protected_->state == FLAC__SEEKABLE_STREAM_DECODER_OK);

	decoder->protected_->state = FLAC__SEEKABLE_STREAM_DECODER_SEEKING;

	/* turn off md5 checking if a seek is attempted */
	decoder->protected_->md5_checking = false;

	if(!FLAC__stream_decoder_reset(decoder->private_->stream_decoder)) {
		decoder->protected_->state = FLAC__SEEKABLE_STREAM_DECODER_STREAM_ERROR;
		return false;
	}
	/* get the file length */
	if(decoder->private_->length_callback(decoder, &length, decoder->private_->client_data) != FLAC__SEEKABLE_STREAM_DECODER_LENGTH_STATUS_OK) {
		decoder->protected_->state = FLAC__SEEKABLE_STREAM_DECODER_SEEK_ERROR;
		return false;
	}
	/* rewind */
	if(decoder->private_->seek_callback(decoder, 0, decoder->private_->client_data) != FLAC__SEEKABLE_STREAM_DECODER_SEEK_STATUS_OK) {
		decoder->protected_->state = FLAC__SEEKABLE_STREAM_DECODER_SEEK_ERROR;
		return false;
	}
	if(!FLAC__stream_decoder_process_metadata(decoder->private_->stream_decoder)) {
		decoder->protected_->state = FLAC__SEEKABLE_STREAM_DECODER_STREAM_ERROR;
		return false;
	}
	if(sample > decoder->private_->stream_info.total_samples) {
		decoder->protected_->state = FLAC__SEEKABLE_STREAM_DECODER_SEEK_ERROR;
		return false;
	}

	return seek_to_absolute_sample_(decoder, length, sample);
}

/***********************************************************************
 *
 * Private class methods
 *
 ***********************************************************************/

FLAC__StreamDecoderReadStatus read_callback_(const FLAC__StreamDecoder *decoder, FLAC__byte buffer[], unsigned *bytes, void *client_data)
{
	FLAC__SeekableStreamDecoder *seekable_stream_decoder = (FLAC__SeekableStreamDecoder *)client_data;
	(void)decoder;
	if(seekable_stream_decoder->private_->eof_callback(seekable_stream_decoder, seekable_stream_decoder->private_->client_data)) {
		seekable_stream_decoder->protected_->state = FLAC__SEEKABLE_STREAM_DECODER_END_OF_STREAM;
		return FLAC__STREAM_DECODER_READ_END_OF_STREAM;
	}
	else if(*bytes > 0) {
		unsigned bytes_read = *bytes;
		if(seekable_stream_decoder->private_->read_callback(seekable_stream_decoder, buffer, &bytes_read, seekable_stream_decoder->private_->client_data) != FLAC__SEEKABLE_STREAM_DECODER_READ_STATUS_OK) {
			seekable_stream_decoder->protected_->state = FLAC__SEEKABLE_STREAM_DECODER_READ_ERROR;
			return FLAC__STREAM_DECODER_READ_ABORT;
		}
		if(bytes_read == 0) {
			if(seekable_stream_decoder->private_->eof_callback(seekable_stream_decoder, seekable_stream_decoder->private_->client_data)) {
				seekable_stream_decoder->protected_->state = FLAC__SEEKABLE_STREAM_DECODER_END_OF_STREAM;
				return FLAC__STREAM_DECODER_READ_END_OF_STREAM;
			}
			else
				return FLAC__STREAM_DECODER_READ_CONTINUE;
		}
		else {
			*bytes = bytes_read;
			return FLAC__STREAM_DECODER_READ_CONTINUE;
		}
	}
	else
		return FLAC__STREAM_DECODER_READ_ABORT; /* abort to avoid a deadlock */
}

FLAC__StreamDecoderWriteStatus write_callback_(const FLAC__StreamDecoder *decoder, const FLAC__Frame *frame, const FLAC__int32 *buffer[], void *client_data)
{
	FLAC__SeekableStreamDecoder *seekable_stream_decoder = (FLAC__SeekableStreamDecoder *)client_data;
	(void)decoder;

	if(seekable_stream_decoder->protected_->state == FLAC__SEEKABLE_STREAM_DECODER_SEEKING) {
		FLAC__uint64 this_frame_sample = frame->header.number.sample_number;
		FLAC__uint64 next_frame_sample = this_frame_sample + (FLAC__uint64)frame->header.blocksize;
		FLAC__uint64 target_sample = seekable_stream_decoder->private_->target_sample;

		FLAC__ASSERT(frame->header.number_type == FLAC__FRAME_NUMBER_TYPE_SAMPLE_NUMBER);

		seekable_stream_decoder->private_->last_frame = *frame; /* save the frame */
		if(this_frame_sample <= target_sample && target_sample < next_frame_sample) { /* we hit our target frame */
			unsigned delta = (unsigned)(target_sample - this_frame_sample);
			/* kick out of seek mode */
			seekable_stream_decoder->protected_->state = FLAC__SEEKABLE_STREAM_DECODER_OK;
			/* shift out the samples before target_sample */
			if(delta > 0) {
				unsigned channel;
				const FLAC__int32 *newbuffer[FLAC__MAX_CHANNELS];
				for(channel = 0; channel < frame->header.channels; channel++)
					newbuffer[channel] = buffer[channel] + delta;
				seekable_stream_decoder->private_->last_frame.header.blocksize -= delta;
				seekable_stream_decoder->private_->last_frame.header.number.sample_number += (FLAC__uint64)delta;
				/* write the relevant samples */
				return seekable_stream_decoder->private_->write_callback(seekable_stream_decoder, &seekable_stream_decoder->private_->last_frame, newbuffer, seekable_stream_decoder->private_->client_data);
			}
			else {
				/* write the relevant samples */
				return seekable_stream_decoder->private_->write_callback(seekable_stream_decoder, frame, buffer, seekable_stream_decoder->private_->client_data);
			}
		}
		else {
			return FLAC__STREAM_DECODER_WRITE_CONTINUE;
		}
	}
	else {
		if(seekable_stream_decoder->protected_->md5_checking) {
			if(!FLAC__MD5Accumulate(&seekable_stream_decoder->private_->md5context, buffer, frame->header.channels, frame->header.blocksize, (frame->header.bits_per_sample+7) / 8))
				return FLAC__STREAM_DECODER_WRITE_ABORT;
		}
		return seekable_stream_decoder->private_->write_callback(seekable_stream_decoder, frame, buffer, seekable_stream_decoder->private_->client_data);
	}
}

void metadata_callback_(const FLAC__StreamDecoder *decoder, const FLAC__StreamMetaData *metadata, void *client_data)
{
	FLAC__SeekableStreamDecoder *seekable_stream_decoder = (FLAC__SeekableStreamDecoder *)client_data;
	(void)decoder;

	if(metadata->type == FLAC__METADATA_TYPE_STREAMINFO) {
		seekable_stream_decoder->private_->stream_info = metadata->data.stream_info;
		/* save the MD5 signature for comparison later */
		memcpy(seekable_stream_decoder->private_->stored_md5sum, metadata->data.stream_info.md5sum, 16);
		if(0 == memcmp(seekable_stream_decoder->private_->stored_md5sum, "\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0", 16))
			seekable_stream_decoder->protected_->md5_checking = false;
	}
	else if(metadata->type == FLAC__METADATA_TYPE_SEEKTABLE) {
		seekable_stream_decoder->private_->seek_table = &metadata->data.seek_table;
	}

	if(seekable_stream_decoder->protected_->state != FLAC__SEEKABLE_STREAM_DECODER_SEEKING)
		seekable_stream_decoder->private_->metadata_callback(seekable_stream_decoder, metadata, seekable_stream_decoder->private_->client_data);
}

void error_callback_(const FLAC__StreamDecoder *decoder, FLAC__StreamDecoderErrorStatus status, void *client_data)
{
	FLAC__SeekableStreamDecoder *seekable_stream_decoder = (FLAC__SeekableStreamDecoder *)client_data;
	(void)decoder;

	if(seekable_stream_decoder->protected_->state != FLAC__SEEKABLE_STREAM_DECODER_SEEKING)
		seekable_stream_decoder->private_->error_callback(seekable_stream_decoder, status, seekable_stream_decoder->private_->client_data);
}

FLAC__bool seek_to_absolute_sample_(FLAC__SeekableStreamDecoder *decoder, FLAC__uint64 stream_length, FLAC__uint64 target_sample)
{
	FLAC__uint64 first_frame_offset, lower_bound, upper_bound;
	FLAC__int64 pos = -1, last_pos = -1;
	int i, lower_seek_point = -1, upper_seek_point = -1;
	unsigned approx_bytes_per_frame;
	FLAC__uint64 last_frame_sample = 0xffffffffffffffff;
	FLAC__bool needs_seek;
	const FLAC__bool is_variable_blocksize_stream = (decoder->private_->stream_info.min_blocksize != decoder->private_->stream_info.max_blocksize);

	/* we are just guessing here, but we want to guess high, not low */
	if(decoder->private_->stream_info.max_framesize > 0) {
		approx_bytes_per_frame = decoder->private_->stream_info.max_framesize;
	}
	else if(!is_variable_blocksize_stream) {
		/* note there are no () around 'decoder->private_->stream_info.bits_per_sample/8' to keep precision up since it's an integer calulation */
		approx_bytes_per_frame = decoder->private_->stream_info.min_blocksize * decoder->private_->stream_info.channels * decoder->private_->stream_info.bits_per_sample/8 + 64;
	}
	else
		approx_bytes_per_frame = 1152 * decoder->private_->stream_info.channels * decoder->private_->stream_info.bits_per_sample/8 + 64;

	/*
	 * The stream position is currently at the first frame plus any read
	 * ahead data, so first we get the stream position, then subtract
	 * uncomsumed bytes to get the position of the first frame in the
	 * stream.
	 */
	if(decoder->private_->tell_callback(decoder, &first_frame_offset, decoder->private_->client_data) != FLAC__SEEKABLE_STREAM_DECODER_TELL_STATUS_OK) {
		decoder->protected_->state = FLAC__SEEKABLE_STREAM_DECODER_SEEK_ERROR;
		return false;
	}
	FLAC__ASSERT(first_frame_offset >= FLAC__stream_decoder_get_input_bytes_unconsumed(decoder->private_->stream_decoder));
	first_frame_offset -= FLAC__stream_decoder_get_input_bytes_unconsumed(decoder->private_->stream_decoder);

	/*
	 * First, we set an upper and lower bound on where in the
	 * stream we will search.  For now we assume the worst case
	 * scenario, which is our best guess at the beginning of
	 * the first and last frames.
	 */
	lower_bound = first_frame_offset;

	/* calc the upper_bound, beyond which we never want to seek */
	if(decoder->private_->stream_info.max_framesize > 0)
		upper_bound = stream_length - (decoder->private_->stream_info.max_framesize + 128 + 2); /* 128 for a possible ID3V1 tag, 2 for indexing differences */
	else
		upper_bound = stream_length - ((decoder->private_->stream_info.channels * decoder->private_->stream_info.bits_per_sample * FLAC__MAX_BLOCK_SIZE) / 8 + 128 + 2);

	/*
	 * Now we refine the bounds if we have a seektable with
	 * suitable points.  Note that according to the spec they
	 * must be ordered by ascending sample number.
	 */
	if(0 != decoder->private_->seek_table) {
		/* find the closest seek point <= target_sample, if it exists */
		for(i = (int)decoder->private_->seek_table->num_points - 1; i >= 0; i--) {
			if(decoder->private_->seek_table->points[i].sample_number != FLAC__STREAM_METADATA_SEEKPOINT_PLACEHOLDER && decoder->private_->seek_table->points[i].sample_number <= target_sample)
				break;
		}
		if(i >= 0) { /* i.e. we found a suitable seek point... */
			lower_bound = first_frame_offset + decoder->private_->seek_table->points[i].stream_offset;
			lower_seek_point = i;
		}

		/* find the closest seek point > target_sample, if it exists */
		for(i = 0; i < (int)decoder->private_->seek_table->num_points; i++) {
			if(decoder->private_->seek_table->points[i].sample_number != FLAC__STREAM_METADATA_SEEKPOINT_PLACEHOLDER && decoder->private_->seek_table->points[i].sample_number > target_sample)
				break;
		}
		if(i < (int)decoder->private_->seek_table->num_points) { /* i.e. we found a suitable seek point... */
			upper_bound = first_frame_offset + decoder->private_->seek_table->points[i].stream_offset;
			upper_seek_point = i;
		}
	}

	/*
	 * Now guess at where within those bounds our target
	 * sample will be.
	 */
	if(lower_seek_point >= 0) {
		/* first see if our sample is within a few frames of the lower seekpoint */
		if(decoder->private_->seek_table->points[lower_seek_point].sample_number <= target_sample && target_sample < decoder->private_->seek_table->points[lower_seek_point].sample_number + (decoder->private_->seek_table->points[lower_seek_point].frame_samples * 4)) {
			pos = (FLAC__int64)lower_bound;
		}
		else if(upper_seek_point >= 0) {
			const FLAC__uint64 target_offset = target_sample - decoder->private_->seek_table->points[lower_seek_point].sample_number;
			const FLAC__uint64 range_samples = decoder->private_->seek_table->points[upper_seek_point].sample_number - decoder->private_->seek_table->points[lower_seek_point].sample_number;
			const FLAC__uint64 range_bytes = upper_bound - lower_bound;
#if defined _MSC_VER || defined __MINGW32__
			/* with VC++ you have to spoon feed it the casting */
			pos = (FLAC__int64)lower_bound + (FLAC__int64)((double)(FLAC__int64)target_offset / (double)(FLAC__int64)range_samples * (double)(FLAC__int64)(range_bytes-1)) - approx_bytes_per_frame;
#else
			pos = (FLAC__int64)lower_bound + (FLAC__int64)((double)target_offset / (double)range_samples * (double)(range_bytes-1)) - approx_bytes_per_frame;
#endif
		}
	}
	if(pos < 0) {
		/* We need to use the metadata and the filelength to estimate the position of the frame with the correct sample */
#if defined _MSC_VER || defined __MINGW32__
		/* with VC++ you have to spoon feed it the casting */
		pos = (FLAC__int64)first_frame_offset + (FLAC__int64)((double)(FLAC__int64)target_sample / (double)(FLAC__int64)decoder->private_->stream_info.total_samples * (double)(FLAC__int64)(stream_length-first_frame_offset-1)) - approx_bytes_per_frame;
#else
		pos = (FLAC__int64)first_frame_offset + (FLAC__int64)((double)target_sample / (double)decoder->private_->stream_info.total_samples * (double)(stream_length-first_frame_offset-1)) - approx_bytes_per_frame;
#endif
	}

	/* clip the position to the bounds, lower bound takes precedence */
	if(pos >= (FLAC__int64)upper_bound)
		pos = (FLAC__int64)upper_bound-1;
	if(pos < (FLAC__int64)lower_bound)
		pos = (FLAC__int64)lower_bound;
	needs_seek = true;

	decoder->private_->target_sample = target_sample;
	while(1) {
		if(needs_seek) {
			if(decoder->private_->seek_callback(decoder, (FLAC__uint64)pos, decoder->private_->client_data) != FLAC__SEEKABLE_STREAM_DECODER_SEEK_STATUS_OK) {
				decoder->protected_->state = FLAC__SEEKABLE_STREAM_DECODER_SEEK_ERROR;
				return false;
			}
			if(!FLAC__stream_decoder_flush(decoder->private_->stream_decoder)) {
				decoder->protected_->state = FLAC__SEEKABLE_STREAM_DECODER_STREAM_ERROR;
				return false;
			}
		}
		if(!FLAC__stream_decoder_process_one_frame(decoder->private_->stream_decoder)) {
			decoder->protected_->state = FLAC__SEEKABLE_STREAM_DECODER_SEEK_ERROR;
			return false;
		}
		/* our write callback will change the state when it gets to the target frame */
		if(decoder->protected_->state != FLAC__SEEKABLE_STREAM_DECODER_SEEKING) {
			break;
		}
		else { /* we need to narrow the search */
			FLAC__uint64 this_frame_sample = decoder->private_->last_frame.header.number.sample_number;
			FLAC__ASSERT(decoder->private_->last_frame.header.number_type == FLAC__FRAME_NUMBER_TYPE_SAMPLE_NUMBER);
			if(this_frame_sample == last_frame_sample) {
				/* our last move backwards wasn't big enough */
				pos -= (last_pos - pos);
				needs_seek = true;
			}
			else {
				if(target_sample < this_frame_sample) {
					last_pos = pos;
					approx_bytes_per_frame = decoder->private_->last_frame.header.blocksize * decoder->private_->last_frame.header.channels * decoder->private_->last_frame.header.bits_per_sample/8 + 64;
					pos -= approx_bytes_per_frame;
					needs_seek = true;
				}
				else { /* target_sample >= this_frame_sample + this frame's blocksize */
					last_pos = pos;
					if(decoder->private_->tell_callback(decoder, (FLAC__uint64*)(&pos), decoder->private_->client_data) != FLAC__SEEKABLE_STREAM_DECODER_TELL_STATUS_OK) {
						decoder->protected_->state = FLAC__SEEKABLE_STREAM_DECODER_SEEK_ERROR;
						return false;
					}
					pos -= FLAC__stream_decoder_get_input_bytes_unconsumed(decoder->private_->stream_decoder);
					needs_seek = false;
				}
			}
			if(pos < (FLAC__int64)lower_bound)
				pos = (FLAC__int64)lower_bound;
			last_frame_sample = this_frame_sample;
		}
	}

	return true;
}