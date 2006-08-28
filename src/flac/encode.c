/* flac - Command-line FLAC encoder/decoder
 * Copyright (C) 2000,2001,2002,2003,2004,2005,2006  Josh Coalson
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
 */

#if HAVE_CONFIG_H
#  include <config.h>
#endif

#if defined _WIN32 && !defined __CYGWIN__
/* where MSVC puts unlink() */
# include <io.h>
#else
# include <unistd.h>
#endif
#if defined _MSC_VER || defined __MINGW32__
#include <sys/types.h> /* for off_t */
//@@@ [2G limit] hacks for MSVC6
#define fseeko fseek
#define ftello ftell
#endif
#include <errno.h>
#include <limits.h> /* for LONG_MAX */
#include <math.h> /* for floor() */
#include <stdio.h> /* for FILE etc. */
#include <stdlib.h> /* for malloc */
#include <string.h> /* for strcmp(), strerror( */
#include "FLAC/all.h"
#include "share/grabbag.h"
#include "encode.h"

#ifdef FLAC__HAS_OGG
#include "OggFLAC/stream_encoder.h"
#include "OggFLAC/file_encoder.h"
#endif

#ifdef min
#undef min
#endif
#define min(x,y) ((x)<(y)?(x):(y))
#ifdef max
#undef max
#endif
#define max(x,y) ((x)>(y)?(x):(y))

/* this MUST be >= 588 so that sector aligning can take place with one read */
#define CHUNK_OF_SAMPLES 2048

typedef struct {
#ifdef FLAC__HAS_OGG
	FLAC__bool use_ogg;
#endif
	FLAC__bool verify;
	FLAC__bool is_stdout;
	const char *inbasefilename;
	const char *outfilename;

	FLAC__uint64 skip;
	FLAC__uint64 until; /* a value of 0 mean end-of-stream (i.e. --until=-0) */
	FLAC__bool replay_gain;
	unsigned channels;
	unsigned bits_per_sample;
	unsigned sample_rate;
	FLAC__uint64 unencoded_size;
	FLAC__uint64 total_samples_to_encode;
	FLAC__uint64 bytes_written;
	FLAC__uint64 samples_written;
	unsigned blocksize;
	unsigned stats_mask;

	/*
	 * We use *.stream for encoding to stdout
	 * We use *.file for encoding to a regular file
	 */
	union {
		union {
			FLAC__StreamEncoder *stream;
			FLAC__FileEncoder *file;
		} flac;
#ifdef FLAC__HAS_OGG
		union {
			OggFLAC__StreamEncoder *stream;
			OggFLAC__FileEncoder *file;
		} ogg;
#endif
	} encoder;

	FILE *fin;
	FILE *fout;
	FLAC__StreamMetadata *seek_table_template;
} EncoderSession;

/* this is data attached to the FLAC decoder when encoding from a FLAC file */
typedef struct {
	EncoderSession *encoder_session;
	off_t filesize;
	const FLAC__byte *lookahead;
	unsigned lookahead_length;
	size_t num_metadata_blocks;
	FLAC__StreamMetadata *metadata_blocks[1024]; /*@@@ BAD MAGIC number */
	FLAC__uint64 samples_left_to_process;
	FLAC__bool fatal_error;
} FLACDecoderData;

const int FLAC_ENCODE__DEFAULT_PADDING = 4096;

static FLAC__bool is_big_endian_host_;

static unsigned char ucbuffer_[CHUNK_OF_SAMPLES*FLAC__MAX_CHANNELS*((FLAC__REFERENCE_CODEC_MAX_BITS_PER_SAMPLE+7)/8)];
static signed char *scbuffer_ = (signed char *)ucbuffer_;
static FLAC__uint16 *usbuffer_ = (FLAC__uint16 *)ucbuffer_;
static FLAC__int16 *ssbuffer_ = (FLAC__int16 *)ucbuffer_;

static FLAC__int32 in_[FLAC__MAX_CHANNELS][CHUNK_OF_SAMPLES];
static FLAC__int32 *input_[FLAC__MAX_CHANNELS];


/*
 * unpublished debug routines from the FLAC libs
 */
extern FLAC__bool FLAC__stream_encoder_disable_constant_subframes(FLAC__StreamEncoder *encoder, FLAC__bool value);
extern FLAC__bool FLAC__stream_encoder_disable_fixed_subframes(FLAC__StreamEncoder *encoder, FLAC__bool value);
extern FLAC__bool FLAC__stream_encoder_disable_verbatim_subframes(FLAC__StreamEncoder *encoder, FLAC__bool value);
extern FLAC__bool FLAC__file_encoder_disable_constant_subframes(FLAC__FileEncoder *encoder, FLAC__bool value);
extern FLAC__bool FLAC__file_encoder_disable_fixed_subframes(FLAC__FileEncoder *encoder, FLAC__bool value);
extern FLAC__bool FLAC__file_encoder_disable_verbatim_subframes(FLAC__FileEncoder *encoder, FLAC__bool value);
#ifdef FLAC__HAS_OGG
extern FLAC__bool OggFLAC__stream_encoder_disable_constant_subframes(OggFLAC__StreamEncoder *encoder, FLAC__bool value);
extern FLAC__bool OggFLAC__stream_encoder_disable_fixed_subframes(OggFLAC__StreamEncoder *encoder, FLAC__bool value);
extern FLAC__bool OggFLAC__stream_encoder_disable_verbatim_subframes(OggFLAC__StreamEncoder *encoder, FLAC__bool value);
extern FLAC__bool OggFLAC__file_encoder_disable_constant_subframes(OggFLAC__FileEncoder *encoder, FLAC__bool value);
extern FLAC__bool OggFLAC__file_encoder_disable_fixed_subframes(OggFLAC__FileEncoder *encoder, FLAC__bool value);
extern FLAC__bool OggFLAC__file_encoder_disable_verbatim_subframes(OggFLAC__FileEncoder *encoder, FLAC__bool value);
#endif

/*
 * local routines
 */
static FLAC__bool EncoderSession_construct(EncoderSession *e, FLAC__bool use_ogg, FLAC__bool verify, FILE *infile, const char *infilename, const char *outfilename);
static void EncoderSession_destroy(EncoderSession *e);
static int EncoderSession_finish_ok(EncoderSession *e, int info_align_carry, int info_align_zero);
static int EncoderSession_finish_error(EncoderSession *e);
static FLAC__bool EncoderSession_init_encoder(EncoderSession *e, encode_options_t options, unsigned channels, unsigned bps, unsigned sample_rate, FLACDecoderData *flac_decoder_data);
static FLAC__bool EncoderSession_process(EncoderSession *e, const FLAC__int32 * const buffer[], unsigned samples);
static FLAC__bool convert_to_seek_table_template(const char *requested_seek_points, int num_requested_seek_points, FLAC__StreamMetadata *cuesheet, EncoderSession *e);
static FLAC__bool canonicalize_until_specification(utils__SkipUntilSpecification *spec, const char *inbasefilename, unsigned sample_rate, FLAC__uint64 skip, FLAC__uint64 total_samples_in_input);
static void format_input(FLAC__int32 *dest[], unsigned wide_samples, FLAC__bool is_big_endian, FLAC__bool is_unsigned_samples, unsigned channels, unsigned bps);
#ifdef FLAC__HAS_OGG
static FLAC__StreamEncoderWriteStatus ogg_stream_encoder_write_callback(const OggFLAC__StreamEncoder *encoder, const FLAC__byte buffer[], unsigned bytes, unsigned samples, unsigned current_frame, void *client_data);
static void ogg_stream_encoder_metadata_callback(const OggFLAC__StreamEncoder *encoder, const FLAC__StreamMetadata *metadata, void *client_data);
static void ogg_file_encoder_progress_callback(const OggFLAC__FileEncoder *encoder, FLAC__uint64 bytes_written, FLAC__uint64 samples_written, unsigned frames_written, unsigned total_frames_estimate, void *client_data);
#endif
static FLAC__StreamEncoderWriteStatus flac_stream_encoder_write_callback(const FLAC__StreamEncoder *encoder, const FLAC__byte buffer[], unsigned bytes, unsigned samples, unsigned current_frame, void *client_data);
static void flac_stream_encoder_metadata_callback(const FLAC__StreamEncoder *encoder, const FLAC__StreamMetadata *metadata, void *client_data);
static void flac_file_encoder_progress_callback(const FLAC__FileEncoder *encoder, FLAC__uint64 bytes_written, FLAC__uint64 samples_written, unsigned frames_written, unsigned total_frames_estimate, void *client_data);
static FLAC__SeekableStreamDecoderReadStatus flac_decoder_read_callback(const FLAC__SeekableStreamDecoder *decoder, FLAC__byte buffer[], unsigned *bytes, void *client_data);
static FLAC__SeekableStreamDecoderSeekStatus flac_decoder_seek_callback(const FLAC__SeekableStreamDecoder *decoder, FLAC__uint64 absolute_byte_offset, void *client_data);
static FLAC__SeekableStreamDecoderTellStatus flac_decoder_tell_callback(const FLAC__SeekableStreamDecoder *decoder, FLAC__uint64 *absolute_byte_offset, void *client_data);
static FLAC__SeekableStreamDecoderLengthStatus flac_decoder_length_callback(const FLAC__SeekableStreamDecoder *decoder, FLAC__uint64 *stream_length, void *client_data);
static FLAC__bool flac_decoder_eof_callback(const FLAC__SeekableStreamDecoder *decoder, void *client_data);
static FLAC__StreamDecoderWriteStatus flac_decoder_write_callback(const FLAC__SeekableStreamDecoder *decoder, const FLAC__Frame *frame, const FLAC__int32 * const buffer[], void *client_data);
static void flac_decoder_metadata_callback(const FLAC__SeekableStreamDecoder *decoder, const FLAC__StreamMetadata *metadata, void *client_data);
static void flac_decoder_error_callback(const FLAC__SeekableStreamDecoder *decoder, FLAC__StreamDecoderErrorStatus status, void *client_data);
static FLAC__bool parse_cuesheet(FLAC__StreamMetadata **cuesheet, const char *cuesheet_filename, const char *inbasefilename, FLAC__bool is_cdda, FLAC__uint64 lead_out_offset);
static void print_stats(const EncoderSession *encoder_session);
static void print_error_with_state(const EncoderSession *e, const char *message);
static void print_verify_error(EncoderSession *e);
static FLAC__bool read_little_endian_uint16(FILE *f, FLAC__uint16 *val, FLAC__bool eof_ok, const char *fn);
static FLAC__bool read_little_endian_uint32(FILE *f, FLAC__uint32 *val, FLAC__bool eof_ok, const char *fn);
static FLAC__bool read_big_endian_uint16(FILE *f, FLAC__uint16 *val, FLAC__bool eof_ok, const char *fn);
static FLAC__bool read_big_endian_uint32(FILE *f, FLAC__uint32 *val, FLAC__bool eof_ok, const char *fn);
static FLAC__bool read_sane_extended(FILE *f, FLAC__uint32 *val, FLAC__bool eof_ok, const char *fn);
static FLAC__bool fskip_ahead(FILE *f, FLAC__uint64 offset);

/*
 * public routines
 */
int flac__encode_aif(FILE *infile, off_t infilesize, const char *infilename, const char *outfilename, const FLAC__byte *lookahead, unsigned lookahead_length, wav_encode_options_t options, FLAC__bool is_aifc)
{
	EncoderSession encoder_session;
	FLAC__uint16 x;
	FLAC__uint32 xx;
	unsigned int channels= 0U, bps= 0U, sample_rate= 0U, sample_frames= 0U;
	FLAC__bool got_comm_chunk= false, got_ssnd_chunk= false;
	int info_align_carry= -1, info_align_zero= -1;
	FLAC__bool is_big_endian_pcm = true;

	(void)infilesize; /* silence compiler warning about unused parameter */
	(void)lookahead; /* silence compiler warning about unused parameter */
	(void)lookahead_length; /* silence compiler warning about unused parameter */

	if(!
		EncoderSession_construct(
			&encoder_session,
#ifdef FLAC__HAS_OGG
			options.common.use_ogg,
#else
			/*use_ogg=*/false,
#endif
			options.common.verify,
			infile,
			infilename,
			outfilename
		)
	)
		return 1;

	/* lookahead[] already has "FORMxxxxAIFF", do sub-chunks */

	while(1) {
		size_t c= 0U;
		char chunk_id[5] = { '\0', '\0', '\0', '\0', '\0' }; /* one extra byte for terminating NUL so we can also treat it like a C string */

		/* chunk identifier; really conservative about behavior of fread() and feof() */
		if(feof(infile) || ((c= fread(chunk_id, 1U, 4U, infile)), c==0U && feof(infile)))
			break;
		else if(c<4U || feof(infile)) {
			flac__utils_printf(stderr, 1, "%s: ERROR: incomplete chunk identifier\n", encoder_session.inbasefilename);
			return EncoderSession_finish_error(&encoder_session);
		}

		if(got_comm_chunk==false && !memcmp(chunk_id, "COMM", 4)) { /* common chunk */
			unsigned long skip;
			const FLAC__uint32 minimum_comm_size = (is_aifc? 22 : 18);

			/* COMM chunk size */
			if(!read_big_endian_uint32(infile, &xx, false, encoder_session.inbasefilename))
				return EncoderSession_finish_error(&encoder_session);
			else if(xx<minimum_comm_size) {
				flac__utils_printf(stderr, 1, "%s: ERROR: non-standard %s 'COMM' chunk has length = %u\n", encoder_session.inbasefilename, is_aifc? "AIFF-C" : "AIFF", (unsigned int)xx);
				return EncoderSession_finish_error(&encoder_session);
			}
			else if(!is_aifc && xx!=minimum_comm_size) {
				flac__utils_printf(stderr, 1, "%s: WARNING: non-standard %s 'COMM' chunk has length = %u, expected %u\n", encoder_session.inbasefilename, is_aifc? "AIFF-C" : "AIFF", (unsigned int)xx, minimum_comm_size);
			}
			skip= (xx-minimum_comm_size)+(xx & 1U);

			/* number of channels */
			if(!read_big_endian_uint16(infile, &x, false, encoder_session.inbasefilename))
				return EncoderSession_finish_error(&encoder_session);
			else if(x==0U || x>FLAC__MAX_CHANNELS) {
				flac__utils_printf(stderr, 1, "%s: ERROR: unsupported number channels %u\n", encoder_session.inbasefilename, (unsigned int)x);
				return EncoderSession_finish_error(&encoder_session);
			}
			else if(options.common.sector_align && x!=2U) {
				flac__utils_printf(stderr, 1, "%s: ERROR: file has %u channels, must be 2 for --sector-align\n", encoder_session.inbasefilename, (unsigned int)x);
				return EncoderSession_finish_error(&encoder_session);
			}
			channels= x;

			/* number of sample frames */
			if(!read_big_endian_uint32(infile, &xx, false, encoder_session.inbasefilename))
				return EncoderSession_finish_error(&encoder_session);
			sample_frames= xx;

			/* bits per sample */
			if(!read_big_endian_uint16(infile, &x, false, encoder_session.inbasefilename))
				return EncoderSession_finish_error(&encoder_session);
			else if(x!=8U && x!=16U && x!=24U) {
				flac__utils_printf(stderr, 1, "%s: ERROR: unsupported bits per sample %u\n", encoder_session.inbasefilename, (unsigned int)x);
				return EncoderSession_finish_error(&encoder_session);
			}
			else if(options.common.sector_align && x!=16U) {
				flac__utils_printf(stderr, 1, "%s: ERROR: file has %u bits per sample, must be 16 for --sector-align\n", encoder_session.inbasefilename, (unsigned int)x);
				return EncoderSession_finish_error(&encoder_session);
			}
			bps= x;

			/* sample rate */
			if(!read_sane_extended(infile, &xx, false, encoder_session.inbasefilename))
				return EncoderSession_finish_error(&encoder_session);
			else if(!FLAC__format_sample_rate_is_valid(xx)) {
				flac__utils_printf(stderr, 1, "%s: ERROR: unsupported sample rate %u\n", encoder_session.inbasefilename, (unsigned int)xx);
				return EncoderSession_finish_error(&encoder_session);
			}
			else if(options.common.sector_align && xx!=44100U) {
				flac__utils_printf(stderr, 1, "%s: ERROR: file's sample rate is %u, must be 44100 for --sector-align\n", encoder_session.inbasefilename, (unsigned int)xx);
				return EncoderSession_finish_error(&encoder_session);
			}
			sample_rate= xx;

			/* check compression type for AIFF-C */
			if(is_aifc) {
				if(!read_big_endian_uint32(infile, &xx, false, encoder_session.inbasefilename))
					return EncoderSession_finish_error(&encoder_session);
				if(xx == 0x736F7774) /* "sowt" */
					is_big_endian_pcm = false;
				else if(xx == 0x4E4F4E45) /* "NONE" */
					; /* nothing to do, we already default to big-endian */
				else {
					flac__utils_printf(stderr, 1, "%s: ERROR: can't handle AIFF-C compression type \"%c%c%c%c\"\n", encoder_session.inbasefilename, (char)(xx>>24), (char)((xx>>16)&8), (char)((xx>>8)&8), (char)(xx&8));
					return EncoderSession_finish_error(&encoder_session);
				}
			}

			/* skip any extra data in the COMM chunk */
			if(!fskip_ahead(infile, skip)) {
				flac__utils_printf(stderr, 1, "%s: ERROR during read while skipping extra COMM data\n", encoder_session.inbasefilename);
				return EncoderSession_finish_error(&encoder_session);
			}

			/*
			 * now that we know the sample rate, canonicalize the
			 * --skip string to a number of samples:
			 */
			flac__utils_canonicalize_skip_until_specification(&options.common.skip_specification, sample_rate);
			FLAC__ASSERT(options.common.skip_specification.value.samples >= 0);
			encoder_session.skip = (FLAC__uint64)options.common.skip_specification.value.samples;
			FLAC__ASSERT(!options.common.sector_align || encoder_session.skip == 0);

			got_comm_chunk= true;
		}
		else if(got_ssnd_chunk==false && !memcmp(chunk_id, "SSND", 4)) { /* sound data chunk */
			unsigned int offset= 0U, block_size= 0U, align_remainder= 0U, data_bytes;
			size_t bytes_per_frame= channels*(bps>>3);
			FLAC__uint64 total_samples_in_input, trim = 0;
			FLAC__bool pad= false;

			if(got_comm_chunk==false) {
				flac__utils_printf(stderr, 1, "%s: ERROR: got 'SSND' chunk before 'COMM' chunk\n", encoder_session.inbasefilename);
				return EncoderSession_finish_error(&encoder_session);
			}

			/* SSND chunk size */
			if(!read_big_endian_uint32(infile, &xx, false, encoder_session.inbasefilename))
				return EncoderSession_finish_error(&encoder_session);
			data_bytes= xx;
			pad= (data_bytes & 1U) ? true : false;
			data_bytes-= 8U; /* discount the offset and block size fields */

			/* offset */
			if(!read_big_endian_uint32(infile, &xx, false, encoder_session.inbasefilename))
				return EncoderSession_finish_error(&encoder_session);
			offset= xx;
			data_bytes-= offset;

			/* block size */
			if(!read_big_endian_uint32(infile, &xx, false, encoder_session.inbasefilename))
				return EncoderSession_finish_error(&encoder_session);
			else if(xx!=0U) {
				flac__utils_printf(stderr, 1, "%s: ERROR: block size is %u; must be 0\n", encoder_session.inbasefilename, (unsigned int)xx);
				return EncoderSession_finish_error(&encoder_session);
			}
			block_size= xx;

			/* skip any SSND offset bytes */
			FLAC__ASSERT(offset<=LONG_MAX);
			if(!fskip_ahead(infile, offset)) {
				flac__utils_printf(stderr, 1, "%s: ERROR: skipping offset in SSND chunk\n", encoder_session.inbasefilename);
				return EncoderSession_finish_error(&encoder_session);
			}
			if(data_bytes!=(sample_frames*bytes_per_frame)) {
				flac__utils_printf(stderr, 1, "%s: ERROR: SSND chunk size inconsistent with sample frame count\n", encoder_session.inbasefilename);
				return EncoderSession_finish_error(&encoder_session);
			}

			/* *options.common.align_reservoir_samples will be 0 unless --sector-align is used */
			FLAC__ASSERT(options.common.sector_align || *options.common.align_reservoir_samples == 0);
			total_samples_in_input = data_bytes / bytes_per_frame + *options.common.align_reservoir_samples;

			/*
			 * now that we know the input size, canonicalize the
			 * --until string to an absolute sample number:
			 */
			if(!canonicalize_until_specification(&options.common.until_specification, encoder_session.inbasefilename, sample_rate, encoder_session.skip, total_samples_in_input))
				return EncoderSession_finish_error(&encoder_session);
			encoder_session.until = (FLAC__uint64)options.common.until_specification.value.samples;
			FLAC__ASSERT(!options.common.sector_align || encoder_session.until == 0);

			if(encoder_session.skip>0U) {
				if(!fskip_ahead(infile, encoder_session.skip*bytes_per_frame)) {
					flac__utils_printf(stderr, 1, "%s: ERROR during read while skipping samples\n", encoder_session.inbasefilename);
					return EncoderSession_finish_error(&encoder_session);
				}
			}

			data_bytes-= (unsigned int)encoder_session.skip*bytes_per_frame; /*@@@ WATCHOUT: 4GB limit */
			encoder_session.total_samples_to_encode= total_samples_in_input - encoder_session.skip;
			if(encoder_session.until > 0) {
				trim = total_samples_in_input - encoder_session.until;
				FLAC__ASSERT(total_samples_in_input > 0);
				FLAC__ASSERT(!options.common.sector_align);
				data_bytes-= (unsigned int)trim*bytes_per_frame;
				encoder_session.total_samples_to_encode-= trim;
			}
			if(options.common.sector_align) {
				align_remainder= (unsigned int)(encoder_session.total_samples_to_encode % 588U);
				if(options.common.is_last_file)
					encoder_session.total_samples_to_encode+= (588U-align_remainder); /* will pad with zeroes */
				else
					encoder_session.total_samples_to_encode-= align_remainder; /* will stop short and carry over to next file */
			}

			/* +54 for the size of the AIFF headers; this is just an estimate for the progress indicator and doesn't need to be exact */
			encoder_session.unencoded_size= encoder_session.total_samples_to_encode*bytes_per_frame+54;

			if(!EncoderSession_init_encoder(&encoder_session, options.common, channels, bps, sample_rate, /*flac_decoder_data=*/0))
				return EncoderSession_finish_error(&encoder_session);

			/* first do any samples in the reservoir */
			if(options.common.sector_align && *options.common.align_reservoir_samples>0U) {

				if(!EncoderSession_process(&encoder_session, (const FLAC__int32 *const *)options.common.align_reservoir, *options.common.align_reservoir_samples)) {
					print_error_with_state(&encoder_session, "ERROR during encoding");
					return EncoderSession_finish_error(&encoder_session);
				}
			}

			/* decrement the data_bytes counter if we need to align the file */
			if(options.common.sector_align) {
				if(options.common.is_last_file)
					*options.common.align_reservoir_samples= 0U;
				else {
					*options.common.align_reservoir_samples= align_remainder;
					data_bytes-= (*options.common.align_reservoir_samples)*bytes_per_frame;
				}
			}

			/* now do from the file */
			while(data_bytes>0) {
				size_t bytes_read= fread(ucbuffer_, 1U, min(data_bytes, CHUNK_OF_SAMPLES*bytes_per_frame), infile);

				if(bytes_read==0U) {
					if(ferror(infile)) {
						flac__utils_printf(stderr, 1, "%s: ERROR during read\n", encoder_session.inbasefilename);
						return EncoderSession_finish_error(&encoder_session);
					}
					else if(feof(infile)) {
						flac__utils_printf(stderr, 1, "%s: WARNING: unexpected EOF; expected %u samples, got %u samples\n", encoder_session.inbasefilename, (unsigned int)encoder_session.total_samples_to_encode, (unsigned int)encoder_session.samples_written);
						data_bytes= 0;
					}
				}
				else {
					if(bytes_read % bytes_per_frame != 0U) {
						flac__utils_printf(stderr, 1, "%s: ERROR: got partial sample\n", encoder_session.inbasefilename);
						return EncoderSession_finish_error(&encoder_session);
					}
					else {
						unsigned int frames= bytes_read/bytes_per_frame;
						format_input(input_, frames, is_big_endian_pcm, /*is_unsigned_samples=*/false, channels, bps);

						if(!EncoderSession_process(&encoder_session, (const FLAC__int32 *const *)input_, frames)) {
							print_error_with_state(&encoder_session, "ERROR during encoding");
							return EncoderSession_finish_error(&encoder_session);
						}
						else
							data_bytes-= bytes_read;
					}
				}
			}

			if(trim>0) {
				FLAC__ASSERT(!options.common.sector_align);
				if(!fskip_ahead(infile, trim*bytes_per_frame)) {
					flac__utils_printf(stderr, 1, "%s: ERROR during read while skipping samples\n", encoder_session.inbasefilename);
					return EncoderSession_finish_error(&encoder_session);
				}
			}

			/* now read unaligned samples into reservoir or pad with zeroes if necessary */
			if(options.common.sector_align) {
				if(options.common.is_last_file) {
					unsigned int pad_frames= 588U-align_remainder;

					if(pad_frames<588U) {
						unsigned int i;

						info_align_zero= pad_frames;
						for(i= 0U; i<channels; ++i)
							memset(input_[i], 0, sizeof(input_[0][0])*pad_frames);

						if(!EncoderSession_process(&encoder_session, (const FLAC__int32 *const *)input_, pad_frames)) {
							print_error_with_state(&encoder_session, "ERROR during encoding");
							return EncoderSession_finish_error(&encoder_session);
						}
					}
				}
				else {
					if(*options.common.align_reservoir_samples > 0) {
						size_t bytes_read= fread(ucbuffer_, 1U, (*options.common.align_reservoir_samples)*bytes_per_frame, infile);

						FLAC__ASSERT(CHUNK_OF_SAMPLES>=588U);
						if(bytes_read==0U && ferror(infile)) {
							flac__utils_printf(stderr, 1, "%s: ERROR during read\n", encoder_session.inbasefilename);
							return EncoderSession_finish_error(&encoder_session);
						}
						else if(bytes_read != (*options.common.align_reservoir_samples) * bytes_per_frame) {
							flac__utils_printf(stderr, 1, "%s: WARNING: unexpected EOF; read %u bytes; expected %u samples, got %u samples\n", encoder_session.inbasefilename, (unsigned int)bytes_read, (unsigned int)encoder_session.total_samples_to_encode, (unsigned int)encoder_session.samples_written);
						}
						else {
							info_align_carry= *options.common.align_reservoir_samples;
							format_input(options.common.align_reservoir, *options.common.align_reservoir_samples, is_big_endian_pcm, /*is_unsigned_samples=*/false, channels, bps);
						}
					}
				}
			}

			if(pad==true) {
				unsigned char tmp;

				if(fread(&tmp, 1U, 1U, infile)<1U) {
					flac__utils_printf(stderr, 1, "%s: ERROR during read of SSND pad byte\n", encoder_session.inbasefilename);
					return EncoderSession_finish_error(&encoder_session);
				}
			}

			got_ssnd_chunk= true;
		}
		else { /* other chunk */
			if(!memcmp(chunk_id, "COMM", 4)) {
				flac__utils_printf(stderr, 1, "%s: WARNING: skipping extra 'COMM' chunk\n", encoder_session.inbasefilename);
			}
			else if(!memcmp(chunk_id, "SSND", 4)) {
				flac__utils_printf(stderr, 1, "%s: WARNING: skipping extra 'SSND' chunk\n", encoder_session.inbasefilename);
			}
			else {
				flac__utils_printf(stderr, 1, "%s: WARNING: skipping unknown chunk '%s'\n", encoder_session.inbasefilename, chunk_id);
			}

			/* chunk size */
			if(!read_big_endian_uint32(infile, &xx, false, encoder_session.inbasefilename))
				return EncoderSession_finish_error(&encoder_session);
			else {
				unsigned long skip= xx+(xx & 1U);

				FLAC__ASSERT(skip<=LONG_MAX);
				if(!fskip_ahead(infile, skip)) {
					fprintf(stderr, "%s: ERROR during read while skipping unknown chunk\n", encoder_session.inbasefilename);
					return EncoderSession_finish_error(&encoder_session);
				}
			}
		}
	}

	if(got_ssnd_chunk==false && sample_frames!=0U) {
		flac__utils_printf(stderr, 1, "%s: ERROR: missing SSND chunk\n", encoder_session.inbasefilename);
		return EncoderSession_finish_error(&encoder_session);
	}

	return EncoderSession_finish_ok(&encoder_session, info_align_carry, info_align_zero);
}

int flac__encode_wav(FILE *infile, off_t infilesize, const char *infilename, const char *outfilename, const FLAC__byte *lookahead, unsigned lookahead_length, wav_encode_options_t options)
{
	EncoderSession encoder_session;
	FLAC__bool is_unsigned_samples = false;
	unsigned channels = 0, bps = 0, sample_rate = 0;
	size_t bytes_per_wide_sample, bytes_read;
	FLAC__uint16 x;
	FLAC__uint32 xx;
	FLAC__bool got_fmt_chunk = false, got_data_chunk = false;
	unsigned align_remainder = 0;
	int info_align_carry = -1, info_align_zero = -1;

	(void)infilesize;
	(void)lookahead;
	(void)lookahead_length;

	if(!
		EncoderSession_construct(
			&encoder_session,
#ifdef FLAC__HAS_OGG
			options.common.use_ogg,
#else
			/*use_ogg=*/false,
#endif
			options.common.verify,
			infile,
			infilename,
			outfilename
		)
	)
		return 1;

	/*
	 * lookahead[] already has "RIFFxxxxWAVE", do sub-chunks
	 */
	while(!feof(infile)) {
		if(!read_little_endian_uint32(infile, &xx, true, encoder_session.inbasefilename))
			return EncoderSession_finish_error(&encoder_session);
		if(feof(infile))
			break;
		if(xx == 0x20746d66 && !got_fmt_chunk) { /* "fmt " */
			unsigned block_align, data_bytes;

			/* fmt sub-chunk size */
			if(!read_little_endian_uint32(infile, &xx, false, encoder_session.inbasefilename))
				return EncoderSession_finish_error(&encoder_session);
			if(xx < 16) {
				flac__utils_printf(stderr, 1, "%s: ERROR: found non-standard 'fmt ' sub-chunk which has length = %u\n", encoder_session.inbasefilename, (unsigned)xx);
				return EncoderSession_finish_error(&encoder_session);
			}
			else if(xx != 16 && xx != 18) {
				flac__utils_printf(stderr, 1, "%s: WARNING: found non-standard 'fmt ' sub-chunk which has length = %u\n", encoder_session.inbasefilename, (unsigned)xx);
			}
			data_bytes = xx;
			/* compression code */
			if(!read_little_endian_uint16(infile, &x, false, encoder_session.inbasefilename))
				return EncoderSession_finish_error(&encoder_session);
			if(x != 1) {
				flac__utils_printf(stderr, 1, "%s: ERROR: unsupported compression type %u\n", encoder_session.inbasefilename, (unsigned)x);
				return EncoderSession_finish_error(&encoder_session);
			}
			/* number of channels */
			if(!read_little_endian_uint16(infile, &x, false, encoder_session.inbasefilename))
				return EncoderSession_finish_error(&encoder_session);
			if(x == 0 || x > FLAC__MAX_CHANNELS) {
				flac__utils_printf(stderr, 1, "%s: ERROR: unsupported number channels %u\n", encoder_session.inbasefilename, (unsigned)x);
				return EncoderSession_finish_error(&encoder_session);
			}
			else if(options.common.sector_align && x != 2) {
				flac__utils_printf(stderr, 1, "%s: ERROR: file has %u channels, must be 2 for --sector-align\n", encoder_session.inbasefilename, (unsigned)x);
				return EncoderSession_finish_error(&encoder_session);
			}
			channels = x;
			/* sample rate */
			if(!read_little_endian_uint32(infile, &xx, false, encoder_session.inbasefilename))
				return EncoderSession_finish_error(&encoder_session);
			if(!FLAC__format_sample_rate_is_valid(xx)) {
				flac__utils_printf(stderr, 1, "%s: ERROR: unsupported sample rate %u\n", encoder_session.inbasefilename, (unsigned)xx);
				return EncoderSession_finish_error(&encoder_session);
			}
			else if(options.common.sector_align && xx != 44100) {
				flac__utils_printf(stderr, 1, "%s: ERROR: file's sample rate is %u, must be 44100 for --sector-align\n", encoder_session.inbasefilename, (unsigned)xx);
				return EncoderSession_finish_error(&encoder_session);
			}
			sample_rate = xx;
			/* avg bytes per second (ignored) */
			if(!read_little_endian_uint32(infile, &xx, false, encoder_session.inbasefilename))
				return EncoderSession_finish_error(&encoder_session);
			/* block align */
			if(!read_little_endian_uint16(infile, &x, false, encoder_session.inbasefilename))
				return EncoderSession_finish_error(&encoder_session);
			block_align = x;
			/* bits per sample */
			if(!read_little_endian_uint16(infile, &x, false, encoder_session.inbasefilename))
				return EncoderSession_finish_error(&encoder_session);
			if(x != 8 && x != 16 && x != 24) {
				flac__utils_printf(stderr, 1, "%s: ERROR: unsupported bits-per-sample %u\n", encoder_session.inbasefilename, (unsigned)x);
				return EncoderSession_finish_error(&encoder_session);
			}
			else if(options.common.sector_align && x != 16) {
				flac__utils_printf(stderr, 1, "%s: ERROR: file has %u bits per sample, must be 16 for --sector-align\n", encoder_session.inbasefilename, (unsigned)x);
				return EncoderSession_finish_error(&encoder_session);
			}
			bps = x;
			if(bps * channels != block_align * 8) {
				flac__utils_printf(stderr, 1, "%s: ERROR: unsupported block alignment (%u), for bits-per-sample=%u, channels=%u\n", encoder_session.inbasefilename, block_align, bps, channels);
				return EncoderSession_finish_error(&encoder_session);
			}
			is_unsigned_samples = (x == 8);

			/* skip any extra data in the fmt sub-chunk */
			FLAC__ASSERT(data_bytes >= 16);
			data_bytes -= 16;
			if(!fskip_ahead(infile, data_bytes)) {
				flac__utils_printf(stderr, 1, "%s: ERROR during read while skipping extra 'fmt' data\n", encoder_session.inbasefilename);
				return EncoderSession_finish_error(&encoder_session);
			}

			/*
			 * now that we know the sample rate, canonicalize the
			 * --skip string to a number of samples:
			 */
			flac__utils_canonicalize_skip_until_specification(&options.common.skip_specification, sample_rate);
			FLAC__ASSERT(options.common.skip_specification.value.samples >= 0);
			encoder_session.skip = (FLAC__uint64)options.common.skip_specification.value.samples;
			FLAC__ASSERT(!options.common.sector_align || encoder_session.skip == 0);

			got_fmt_chunk = true;
		}
		else if(xx == 0x61746164 && !got_data_chunk && got_fmt_chunk) { /* "data" */
			FLAC__uint64 total_samples_in_input, trim = 0;
			FLAC__bool pad = false;
			unsigned data_bytes;

			/* data size */
			if(!read_little_endian_uint32(infile, &xx, false, encoder_session.inbasefilename))
				return EncoderSession_finish_error(&encoder_session);
			data_bytes = xx;
			pad = (data_bytes & 1U) ? true : false;

			bytes_per_wide_sample = channels * (bps >> 3);

			/* *options.common.align_reservoir_samples will be 0 unless --sector-align is used */
			FLAC__ASSERT(options.common.sector_align || *options.common.align_reservoir_samples == 0);
			total_samples_in_input = data_bytes / bytes_per_wide_sample + *options.common.align_reservoir_samples;

			/*
			 * now that we know the input size, canonicalize the
			 * --until string to an absolute sample number:
			 */
			if(!canonicalize_until_specification(&options.common.until_specification, encoder_session.inbasefilename, sample_rate, encoder_session.skip, total_samples_in_input))
				return EncoderSession_finish_error(&encoder_session);
			encoder_session.until = (FLAC__uint64)options.common.until_specification.value.samples;
			FLAC__ASSERT(!options.common.sector_align || encoder_session.until == 0);

			if(encoder_session.skip > 0) {
				if(!fskip_ahead(infile, encoder_session.skip * bytes_per_wide_sample)) {
					flac__utils_printf(stderr, 1, "%s: ERROR during read while skipping samples\n", encoder_session.inbasefilename);
					return EncoderSession_finish_error(&encoder_session);
				}
			}

			data_bytes -= (unsigned)encoder_session.skip * bytes_per_wide_sample; /*@@@ WATCHOUT: 4GB limit */
			encoder_session.total_samples_to_encode = total_samples_in_input - encoder_session.skip;
			if(encoder_session.until > 0) {
				trim = total_samples_in_input - encoder_session.until;
				FLAC__ASSERT(total_samples_in_input > 0);
				FLAC__ASSERT(!options.common.sector_align);
				data_bytes -= (unsigned int)trim * bytes_per_wide_sample;
				encoder_session.total_samples_to_encode -= trim;
			}
			if(options.common.sector_align) {
				align_remainder = (unsigned)(encoder_session.total_samples_to_encode % 588);
				if(options.common.is_last_file)
					encoder_session.total_samples_to_encode += (588-align_remainder); /* will pad with zeroes */
				else
					encoder_session.total_samples_to_encode -= align_remainder; /* will stop short and carry over to next file */
			}

			/* +44 for the size of the WAV headers; this is just an estimate for the progress indicator and doesn't need to be exact */
			encoder_session.unencoded_size = encoder_session.total_samples_to_encode * bytes_per_wide_sample + 44;

			if(!EncoderSession_init_encoder(&encoder_session, options.common, channels, bps, sample_rate, /*flac_decoder_data=*/0))
				return EncoderSession_finish_error(&encoder_session);

			/*
			 * first do any samples in the reservoir
			 */
			if(options.common.sector_align && *options.common.align_reservoir_samples > 0) {
				if(!EncoderSession_process(&encoder_session, (const FLAC__int32 * const *)options.common.align_reservoir, *options.common.align_reservoir_samples)) {
					print_error_with_state(&encoder_session, "ERROR during encoding");
					return EncoderSession_finish_error(&encoder_session);
				}
			}

			/*
			 * decrement the data_bytes counter if we need to align the file
			 */
			if(options.common.sector_align) {
				if(options.common.is_last_file) {
					*options.common.align_reservoir_samples = 0;
				}
				else {
					*options.common.align_reservoir_samples = align_remainder;
					data_bytes -= (*options.common.align_reservoir_samples) * bytes_per_wide_sample;
				}
			}

			/*
			 * now do from the file
			 */
			while(data_bytes > 0) {
				bytes_read = fread(ucbuffer_, sizeof(unsigned char), min(data_bytes, CHUNK_OF_SAMPLES * bytes_per_wide_sample), infile);
				if(bytes_read == 0) {
					if(ferror(infile)) {
						flac__utils_printf(stderr, 1, "%s: ERROR during read\n", encoder_session.inbasefilename);
						return EncoderSession_finish_error(&encoder_session);
					}
					else if(feof(infile)) {
						flac__utils_printf(stderr, 1, "%s: WARNING: unexpected EOF; expected %u samples, got %u samples\n", encoder_session.inbasefilename, (unsigned)encoder_session.total_samples_to_encode, (unsigned)encoder_session.samples_written);
						data_bytes = 0;
					}
				}
				else {
					if(bytes_read % bytes_per_wide_sample != 0) {
						flac__utils_printf(stderr, 1, "%s: ERROR: got partial sample\n", encoder_session.inbasefilename);
						return EncoderSession_finish_error(&encoder_session);
					}
					else {
						unsigned wide_samples = bytes_read / bytes_per_wide_sample;
						format_input(input_, wide_samples, /*is_big_endian=*/false, is_unsigned_samples, channels, bps);

						if(!EncoderSession_process(&encoder_session, (const FLAC__int32 * const *)input_, wide_samples)) {
							print_error_with_state(&encoder_session, "ERROR during encoding");
							return EncoderSession_finish_error(&encoder_session);
						}
						data_bytes -= bytes_read;
					}
				}
			}

			if(trim > 0) {
				FLAC__ASSERT(!options.common.sector_align);
				if(!fskip_ahead(infile, trim * bytes_per_wide_sample)) {
					flac__utils_printf(stderr, 1, "%s: ERROR during read while skipping samples\n", encoder_session.inbasefilename);
					return EncoderSession_finish_error(&encoder_session);
				}
			}

			/*
			 * now read unaligned samples into reservoir or pad with zeroes if necessary
			 */
			if(options.common.sector_align) {
				if(options.common.is_last_file) {
					unsigned wide_samples = 588 - align_remainder;
					if(wide_samples < 588) {
						unsigned channel;

						info_align_zero = wide_samples;
						for(channel = 0; channel < channels; channel++)
							memset(input_[channel], 0, sizeof(input_[0][0]) * wide_samples);

						if(!EncoderSession_process(&encoder_session, (const FLAC__int32 * const *)input_, wide_samples)) {
							print_error_with_state(&encoder_session, "ERROR during encoding");
							return EncoderSession_finish_error(&encoder_session);
						}
					}
				}
				else {
					if(*options.common.align_reservoir_samples > 0) {
						FLAC__ASSERT(CHUNK_OF_SAMPLES >= 588);
						bytes_read = fread(ucbuffer_, sizeof(unsigned char), (*options.common.align_reservoir_samples) * bytes_per_wide_sample, infile);
						if(bytes_read == 0 && ferror(infile)) {
							flac__utils_printf(stderr, 1, "%s: ERROR during read\n", encoder_session.inbasefilename);
							return EncoderSession_finish_error(&encoder_session);
						}
						else if(bytes_read != (*options.common.align_reservoir_samples) * bytes_per_wide_sample) {
							flac__utils_printf(stderr, 1, "%s: WARNING: unexpected EOF; read %u bytes; expected %u samples, got %u samples\n", encoder_session.inbasefilename, (unsigned)bytes_read, (unsigned)encoder_session.total_samples_to_encode, (unsigned)encoder_session.samples_written);
						}
						else {
							info_align_carry = *options.common.align_reservoir_samples;
							format_input(options.common.align_reservoir, *options.common.align_reservoir_samples, /*is_big_endian=*/false, is_unsigned_samples, channels, bps);
						}
					}
				}
			}

			if(pad == true) {
				unsigned char tmp;

				if(fread(&tmp, 1U, 1U, infile) < 1U) {
					flac__utils_printf(stderr, 1, "%s: ERROR during read of data pad byte\n", encoder_session.inbasefilename);
					return EncoderSession_finish_error(&encoder_session);
				}
			}

			got_data_chunk = true;
		}
		else {
			if(xx == 0x20746d66 && got_fmt_chunk) { /* "fmt " */
				flac__utils_printf(stderr, 1, "%s: WARNING: skipping extra 'fmt ' sub-chunk\n", encoder_session.inbasefilename);
			}
			else if(xx == 0x61746164) { /* "data" */
				if(got_data_chunk) {
					flac__utils_printf(stderr, 1, "%s: WARNING: skipping extra 'data' sub-chunk\n", encoder_session.inbasefilename);
				}
				else if(!got_fmt_chunk) {
					flac__utils_printf(stderr, 1, "%s: ERROR: got 'data' sub-chunk before 'fmt' sub-chunk\n", encoder_session.inbasefilename);
					return EncoderSession_finish_error(&encoder_session);
				}
				else {
					FLAC__ASSERT(0);
				}
			}
			else {
				flac__utils_printf(stderr, 1, "%s: WARNING: skipping unknown sub-chunk '%c%c%c%c'\n", encoder_session.inbasefilename, (char)(xx&255), (char)((xx>>8)&255), (char)((xx>>16)&255), (char)(xx>>24));
			}
			/* sub-chunk size */
			if(!read_little_endian_uint32(infile, &xx, false, encoder_session.inbasefilename))
				return EncoderSession_finish_error(&encoder_session);
			else {
				unsigned long skip = xx+(xx & 1U);

				FLAC__ASSERT(skip<=LONG_MAX);
				if(!fskip_ahead(infile, skip)) {
					flac__utils_printf(stderr, 1, "%s: ERROR during read while skipping unsupported sub-chunk\n", encoder_session.inbasefilename);
					return EncoderSession_finish_error(&encoder_session);
				}
			}
		}
	}

	return EncoderSession_finish_ok(&encoder_session, info_align_carry, info_align_zero);
}

int flac__encode_raw(FILE *infile, off_t infilesize, const char *infilename, const char *outfilename, const FLAC__byte *lookahead, unsigned lookahead_length, raw_encode_options_t options)
{
	EncoderSession encoder_session;
	size_t bytes_read;
	const size_t bytes_per_wide_sample = options.channels * (options.bps >> 3);
	unsigned align_remainder = 0;
	int info_align_carry = -1, info_align_zero = -1;
	FLAC__uint64 total_samples_in_input = 0;

	FLAC__ASSERT(!options.common.sector_align || options.channels == 2);
	FLAC__ASSERT(!options.common.sector_align || options.bps == 16);
	FLAC__ASSERT(!options.common.sector_align || options.sample_rate == 44100);
	FLAC__ASSERT(!options.common.sector_align || infilesize >= 0);
	FLAC__ASSERT(!options.common.replay_gain || options.channels <= 2);
	FLAC__ASSERT(!options.common.replay_gain || grabbag__replaygain_is_valid_sample_frequency(options.sample_rate));

	if(!
		EncoderSession_construct(
			&encoder_session,
#ifdef FLAC__HAS_OGG
			options.common.use_ogg,
#else
			/*use_ogg=*/false,
#endif
			options.common.verify,
			infile,
			infilename,
			outfilename
		)
	)
		return 1;

	/*
	 * now that we know the sample rate, canonicalize the
	 * --skip string to a number of samples:
	 */
	flac__utils_canonicalize_skip_until_specification(&options.common.skip_specification, options.sample_rate);
	FLAC__ASSERT(options.common.skip_specification.value.samples >= 0);
	encoder_session.skip = (FLAC__uint64)options.common.skip_specification.value.samples;
	FLAC__ASSERT(!options.common.sector_align || encoder_session.skip == 0);

	if(infilesize < 0)
		total_samples_in_input = 0;
	else {
		/* *options.common.align_reservoir_samples will be 0 unless --sector-align is used */
		FLAC__ASSERT(options.common.sector_align || *options.common.align_reservoir_samples == 0);
		total_samples_in_input = (FLAC__uint64)infilesize / bytes_per_wide_sample + *options.common.align_reservoir_samples;
	}

	/*
	 * now that we know the input size, canonicalize the
	 * --until strings to a number of samples:
	 */
	if(!canonicalize_until_specification(&options.common.until_specification, encoder_session.inbasefilename, options.sample_rate, encoder_session.skip, total_samples_in_input))
		return EncoderSession_finish_error(&encoder_session);
	encoder_session.until = (FLAC__uint64)options.common.until_specification.value.samples;
	FLAC__ASSERT(!options.common.sector_align || encoder_session.until == 0);

	infilesize -= (off_t)encoder_session.skip * bytes_per_wide_sample;
	encoder_session.total_samples_to_encode = total_samples_in_input - encoder_session.skip;
	if(encoder_session.until > 0) {
		const FLAC__uint64 trim = total_samples_in_input - encoder_session.until;
		FLAC__ASSERT(total_samples_in_input > 0);
		FLAC__ASSERT(!options.common.sector_align);
		infilesize -= (off_t)trim * bytes_per_wide_sample;
		encoder_session.total_samples_to_encode -= trim;
	}
	if(infilesize >= 0 && options.common.sector_align) {
		FLAC__ASSERT(encoder_session.skip == 0);
		align_remainder = (unsigned)(encoder_session.total_samples_to_encode % 588);
		if(options.common.is_last_file)
			encoder_session.total_samples_to_encode += (588-align_remainder); /* will pad with zeroes */
		else
			encoder_session.total_samples_to_encode -= align_remainder; /* will stop short and carry over to next file */
	}
	encoder_session.unencoded_size = encoder_session.total_samples_to_encode * bytes_per_wide_sample;

	if(encoder_session.total_samples_to_encode <= 0)
		flac__utils_printf(stderr, 2, "(No runtime statistics possible; please wait for encoding to finish...)\n");

	if(encoder_session.skip > 0) {
		unsigned skip_bytes = bytes_per_wide_sample * (unsigned)encoder_session.skip;
		if(skip_bytes > lookahead_length) {
			skip_bytes -= lookahead_length;
			lookahead_length = 0;
			if(!fskip_ahead(infile, skip_bytes)) {
				flac__utils_printf(stderr, 1, "%s: ERROR during read while skipping samples\n", encoder_session.inbasefilename);
				return EncoderSession_finish_error(&encoder_session);
			}
		}
		else {
			lookahead += skip_bytes;
			lookahead_length -= skip_bytes;
		}
	}

	if(!EncoderSession_init_encoder(&encoder_session, options.common, options.channels, options.bps, options.sample_rate, /*flac_decoder_data=*/0))
		return EncoderSession_finish_error(&encoder_session);

	/*
	 * first do any samples in the reservoir
	 */
	if(options.common.sector_align && *options.common.align_reservoir_samples > 0) {
		if(!EncoderSession_process(&encoder_session, (const FLAC__int32 * const *)options.common.align_reservoir, *options.common.align_reservoir_samples)) {
			print_error_with_state(&encoder_session, "ERROR during encoding");
			return EncoderSession_finish_error(&encoder_session);
		}
	}

	/*
	 * decrement infilesize if we need to align the file
	 */
	if(options.common.sector_align) {
		FLAC__ASSERT(infilesize >= 0);
		if(options.common.is_last_file) {
			*options.common.align_reservoir_samples = 0;
		}
		else {
			*options.common.align_reservoir_samples = align_remainder;
			infilesize -= (off_t)((*options.common.align_reservoir_samples) * bytes_per_wide_sample);
			FLAC__ASSERT(infilesize >= 0);
		}
	}

	/*
	 * now do from the file
	 */
	if(infilesize < 0) {
		while(!feof(infile)) {
			if(lookahead_length > 0) {
				FLAC__ASSERT(lookahead_length < CHUNK_OF_SAMPLES * bytes_per_wide_sample);
				memcpy(ucbuffer_, lookahead, lookahead_length);
				bytes_read = fread(ucbuffer_+lookahead_length, sizeof(unsigned char), CHUNK_OF_SAMPLES * bytes_per_wide_sample - lookahead_length, infile) + lookahead_length;
				if(ferror(infile)) {
					flac__utils_printf(stderr, 1, "%s: ERROR during read\n", encoder_session.inbasefilename);
					return EncoderSession_finish_error(&encoder_session);
				}
				lookahead_length = 0;
			}
			else
				bytes_read = fread(ucbuffer_, sizeof(unsigned char), CHUNK_OF_SAMPLES * bytes_per_wide_sample, infile);

			if(bytes_read == 0) {
				if(ferror(infile)) {
					flac__utils_printf(stderr, 1, "%s: ERROR during read\n", encoder_session.inbasefilename);
					return EncoderSession_finish_error(&encoder_session);
				}
			}
			else if(bytes_read % bytes_per_wide_sample != 0) {
				flac__utils_printf(stderr, 1, "%s: ERROR: got partial sample\n", encoder_session.inbasefilename);
				return EncoderSession_finish_error(&encoder_session);
			}
			else {
				unsigned wide_samples = bytes_read / bytes_per_wide_sample;
				format_input(input_, wide_samples, options.is_big_endian, options.is_unsigned_samples, options.channels, options.bps);

				if(!EncoderSession_process(&encoder_session, (const FLAC__int32 * const *)input_, wide_samples)) {
					print_error_with_state(&encoder_session, "ERROR during encoding");
					return EncoderSession_finish_error(&encoder_session);
				}
			}
		}
	}
	else {
		const FLAC__uint64 max_input_bytes = infilesize;
		FLAC__uint64 total_input_bytes_read = 0;
		while(total_input_bytes_read < max_input_bytes) {
			{
				size_t wanted = (CHUNK_OF_SAMPLES * bytes_per_wide_sample);
				wanted = (size_t) min((FLAC__uint64)wanted, max_input_bytes - total_input_bytes_read);

				if(lookahead_length > 0) {
					FLAC__ASSERT(lookahead_length <= wanted);
					memcpy(ucbuffer_, lookahead, lookahead_length);
					wanted -= lookahead_length;
					bytes_read = lookahead_length;
					if(wanted > 0) {
						bytes_read += fread(ucbuffer_+lookahead_length, sizeof(unsigned char), wanted, infile);
						if(ferror(infile)) {
							flac__utils_printf(stderr, 1, "%s: ERROR during read\n", encoder_session.inbasefilename);
							return EncoderSession_finish_error(&encoder_session);
						}
					}
					lookahead_length = 0;
				}
				else
					bytes_read = fread(ucbuffer_, sizeof(unsigned char), wanted, infile);
			}

			if(bytes_read == 0) {
				if(ferror(infile)) {
					flac__utils_printf(stderr, 1, "%s: ERROR during read\n", encoder_session.inbasefilename);
					return EncoderSession_finish_error(&encoder_session);
				}
				else if(feof(infile)) {
					flac__utils_printf(stderr, 1, "%s: WARNING: unexpected EOF; expected %u samples, got %u samples\n", encoder_session.inbasefilename, (unsigned)encoder_session.total_samples_to_encode, (unsigned)encoder_session.samples_written);
					total_input_bytes_read = max_input_bytes;
				}
			}
			else {
				if(bytes_read % bytes_per_wide_sample != 0) {
					flac__utils_printf(stderr, 1, "%s: ERROR: got partial sample\n", encoder_session.inbasefilename);
					return EncoderSession_finish_error(&encoder_session);
				}
				else {
					unsigned wide_samples = bytes_read / bytes_per_wide_sample;
					format_input(input_, wide_samples, options.is_big_endian, options.is_unsigned_samples, options.channels, options.bps);

					if(!EncoderSession_process(&encoder_session, (const FLAC__int32 * const *)input_, wide_samples)) {
						print_error_with_state(&encoder_session, "ERROR during encoding");
						return EncoderSession_finish_error(&encoder_session);
					}
					total_input_bytes_read += bytes_read;
				}
			}
		}
	}

	/*
	 * now read unaligned samples into reservoir or pad with zeroes if necessary
	 */
	if(options.common.sector_align) {
		if(options.common.is_last_file) {
			unsigned wide_samples = 588 - align_remainder;
			if(wide_samples < 588) {
				unsigned channel;

				info_align_zero = wide_samples;
				for(channel = 0; channel < options.channels; channel++)
					memset(input_[channel], 0, sizeof(input_[0][0]) * wide_samples);

				if(!EncoderSession_process(&encoder_session, (const FLAC__int32 * const *)input_, wide_samples)) {
					print_error_with_state(&encoder_session, "ERROR during encoding");
					return EncoderSession_finish_error(&encoder_session);
				}
			}
		}
		else {
			if(*options.common.align_reservoir_samples > 0) {
				FLAC__ASSERT(CHUNK_OF_SAMPLES >= 588);
				bytes_read = fread(ucbuffer_, sizeof(unsigned char), (*options.common.align_reservoir_samples) * bytes_per_wide_sample, infile);
				if(bytes_read == 0 && ferror(infile)) {
					flac__utils_printf(stderr, 1, "%s: ERROR during read\n", encoder_session.inbasefilename);
					return EncoderSession_finish_error(&encoder_session);
				}
				else if(bytes_read != (*options.common.align_reservoir_samples) * bytes_per_wide_sample) {
					flac__utils_printf(stderr, 1, "%s: WARNING: unexpected EOF; read %u bytes; expected %u samples, got %u samples\n", encoder_session.inbasefilename, (unsigned)bytes_read, (unsigned)encoder_session.total_samples_to_encode, (unsigned)encoder_session.samples_written);
				}
				else {
					info_align_carry = *options.common.align_reservoir_samples;
					format_input(options.common.align_reservoir, *options.common.align_reservoir_samples, options.is_big_endian, options.is_unsigned_samples, options.channels, options.bps);
				}
			}
		}
	}

	return EncoderSession_finish_ok(&encoder_session, info_align_carry, info_align_zero);
}

int flac__encode_flac(FILE *infile, off_t infilesize, const char *infilename, const char *outfilename, const FLAC__byte *lookahead, unsigned lookahead_length, flac_encode_options_t options)
{
	EncoderSession encoder_session;
	FLAC__SeekableStreamDecoder *decoder = 0;
	FLACDecoderData decoder_data;
	size_t i;
	int retval;

	if(!
		EncoderSession_construct(
			&encoder_session,
#ifdef FLAC__HAS_OGG
			options.common.use_ogg,
#else
			/*use_ogg=*/false,
#endif
			options.common.verify,
			infile,
			infilename,
			outfilename
		)
	)
		return 1;

	decoder_data.encoder_session = &encoder_session;
	decoder_data.filesize = (infilesize == (off_t)(-1)? 0 : infilesize);
	decoder_data.lookahead = lookahead;
	decoder_data.lookahead_length = lookahead_length;
	decoder_data.num_metadata_blocks = 0;
	decoder_data.samples_left_to_process = 0;
	decoder_data.fatal_error = false;

	/*
	 * set up FLAC decoder for the input
	 */
	if (0 == (decoder = FLAC__seekable_stream_decoder_new())) {
		flac__utils_printf(stderr, 1, "%s: ERROR: creating decoder for FLAC input\n", encoder_session.inbasefilename);
		return EncoderSession_finish_error(&encoder_session);
	}
	if (!(
		FLAC__seekable_stream_decoder_set_md5_checking(decoder, false) &&
		FLAC__seekable_stream_decoder_set_read_callback(decoder, flac_decoder_read_callback) &&
		FLAC__seekable_stream_decoder_set_seek_callback(decoder, flac_decoder_seek_callback) &&
		FLAC__seekable_stream_decoder_set_tell_callback(decoder, flac_decoder_tell_callback) &&
		FLAC__seekable_stream_decoder_set_length_callback(decoder, flac_decoder_length_callback) &&
		FLAC__seekable_stream_decoder_set_eof_callback(decoder, flac_decoder_eof_callback) &&
		FLAC__seekable_stream_decoder_set_write_callback(decoder, flac_decoder_write_callback) &&
		FLAC__seekable_stream_decoder_set_metadata_callback(decoder, flac_decoder_metadata_callback) &&
		FLAC__seekable_stream_decoder_set_error_callback(decoder, flac_decoder_error_callback) &&
		FLAC__seekable_stream_decoder_set_client_data(decoder, &decoder_data) &&
		FLAC__seekable_stream_decoder_set_metadata_respond_all(decoder)
	)) {
		flac__utils_printf(stderr, 1, "%s: ERROR: setting up decoder for FLAC input\n", encoder_session.inbasefilename);
		goto fubar1; /*@@@ yuck */
	}

	if (FLAC__seekable_stream_decoder_init(decoder) != FLAC__SEEKABLE_STREAM_DECODER_OK) {
		flac__utils_printf(stderr, 1, "%s: ERROR: initializing decoder for FLAC input, state = %s\n", encoder_session.inbasefilename, FLAC__seekable_stream_decoder_get_resolved_state_string(decoder));
		goto fubar1; /*@@@ yuck */
	}

	if (!FLAC__seekable_stream_decoder_process_until_end_of_metadata(decoder) || decoder_data.fatal_error) {
		if (decoder_data.fatal_error)
			flac__utils_printf(stderr, 1, "%s: ERROR: out of memory or too many metadata blocks while reading metadata in FLAC input\n", encoder_session.inbasefilename);
		else
			flac__utils_printf(stderr, 1, "%s: ERROR: reading metadata in FLAC input, state = %s\n", encoder_session.inbasefilename, FLAC__seekable_stream_decoder_get_resolved_state_string(decoder));
		goto fubar1; /*@@@ yuck */
	}

	if (decoder_data.num_metadata_blocks == 0) {
		flac__utils_printf(stderr, 1, "%s: ERROR: reading metadata in FLAC input, got no metadata blocks\n", encoder_session.inbasefilename);
		goto fubar2; /*@@@ yuck */
	}
	else if (decoder_data.metadata_blocks[0]->type != FLAC__METADATA_TYPE_STREAMINFO) {
		flac__utils_printf(stderr, 1, "%s: ERROR: reading metadata in FLAC input, first metadata block is not STREAMINFO\n", encoder_session.inbasefilename);
		goto fubar2; /*@@@ yuck */
	}
	else if (decoder_data.metadata_blocks[0]->data.stream_info.total_samples == 0) {
		flac__utils_printf(stderr, 1, "%s: ERROR: FLAC input has STREAMINFO with unknown total samples which is not supported\n", encoder_session.inbasefilename);
		goto fubar2; /*@@@ yuck */
	}

	/*
	 * now that we have the STREAMINFO and know the sample rate,
	 * canonicalize the --skip string to a number of samples:
	 */
	flac__utils_canonicalize_skip_until_specification(&options.common.skip_specification, decoder_data.metadata_blocks[0]->data.stream_info.sample_rate);
	FLAC__ASSERT(options.common.skip_specification.value.samples >= 0);
	encoder_session.skip = (FLAC__uint64)options.common.skip_specification.value.samples;
	FLAC__ASSERT(!options.common.sector_align); /* --sector-align with FLAC input is not supported */

	{
		FLAC__uint64 total_samples_in_input, trim = 0;

		total_samples_in_input = decoder_data.metadata_blocks[0]->data.stream_info.total_samples;

		/*
		 * now that we know the input size, canonicalize the
		 * --until string to an absolute sample number:
		 */
		if(!canonicalize_until_specification(&options.common.until_specification, encoder_session.inbasefilename, decoder_data.metadata_blocks[0]->data.stream_info.sample_rate, encoder_session.skip, total_samples_in_input))
			goto fubar2; /*@@@ yuck */
		encoder_session.until = (FLAC__uint64)options.common.until_specification.value.samples;

		encoder_session.total_samples_to_encode = total_samples_in_input - encoder_session.skip;
		if(encoder_session.until > 0) {
			trim = total_samples_in_input - encoder_session.until;
			FLAC__ASSERT(total_samples_in_input > 0);
			encoder_session.total_samples_to_encode -= trim;
		}

		encoder_session.unencoded_size = decoder_data.filesize;

		if(!EncoderSession_init_encoder(&encoder_session, options.common, decoder_data.metadata_blocks[0]->data.stream_info.channels, decoder_data.metadata_blocks[0]->data.stream_info.bits_per_sample, decoder_data.metadata_blocks[0]->data.stream_info.sample_rate, &decoder_data))
			return EncoderSession_finish_error(&encoder_session);

		/*
		 * have to wait until the FLAC encoder is set up for writing
		 * before any seeking in the input FLAC file, because the seek
		 * itself will usually call the decoder's write callback, and
		 * our decoder's write callback passes samples to our FLAC
		 * encoder
		 */
		decoder_data.samples_left_to_process = encoder_session.total_samples_to_encode;
		if(encoder_session.skip > 0) {
			if(!FLAC__seekable_stream_decoder_seek_absolute(decoder, encoder_session.skip)) {
				flac__utils_printf(stderr, 1, "%s: ERROR while skipping samples, FLAC decoder state = %s\n", encoder_session.inbasefilename, FLAC__seekable_stream_decoder_get_resolved_state_string(decoder));
				goto fubar2; /*@@@ yuck */
			}
		}

		/*
		 * now do samples from the file
		 */
		while(!decoder_data.fatal_error && decoder_data.samples_left_to_process > 0) {
			if(!FLAC__seekable_stream_decoder_process_single(decoder)) {
				flac__utils_printf(stderr, 1, "%s: ERROR: while decoding FLAC input, state = %s\n", encoder_session.inbasefilename, FLAC__seekable_stream_decoder_get_resolved_state_string(decoder));
				goto fubar2; /*@@@ yuck */
			}
		}
	}

	FLAC__seekable_stream_decoder_delete(decoder);
	retval = EncoderSession_finish_ok(&encoder_session, -1, -1);
	/* have to wail until encoder is completely finished before deleting because of the final step of writing the seekpoint offsets */
	for(i = 0; i < decoder_data.num_metadata_blocks; i++)
		free(decoder_data.metadata_blocks[i]);
	return retval;

fubar2:
	for(i = 0; i < decoder_data.num_metadata_blocks; i++)
		free(decoder_data.metadata_blocks[i]);
fubar1:
	FLAC__seekable_stream_decoder_delete(decoder);
	return EncoderSession_finish_error(&encoder_session);
}

FLAC__bool EncoderSession_construct(EncoderSession *e, FLAC__bool use_ogg, FLAC__bool verify, FILE *infile, const char *infilename, const char *outfilename)
{
	unsigned i;
	FLAC__uint32 test = 1;

	/*
	 * initialize globals
	 */

	is_big_endian_host_ = (*((FLAC__byte*)(&test)))? false : true;

	for(i = 0; i < FLAC__MAX_CHANNELS; i++)
		input_[i] = &(in_[i][0]);


	/*
	 * initialize instance
	 */

#ifdef FLAC__HAS_OGG
	e->use_ogg = use_ogg;
#else
	(void)use_ogg;
#endif
	e->verify = verify;

	e->is_stdout = (0 == strcmp(outfilename, "-"));

	e->inbasefilename = grabbag__file_get_basename(infilename);
	e->outfilename = outfilename;

	e->skip = 0; /* filled in later after the sample_rate is known */
	e->unencoded_size = 0;
	e->total_samples_to_encode = 0;
	e->bytes_written = 0;
	e->samples_written = 0;
	e->blocksize = 0;
	e->stats_mask = 0;

	e->encoder.flac.stream = 0;
	e->encoder.flac.file = 0;
#ifdef FLAC__HAS_OGG
	e->encoder.ogg.stream = 0;
	e->encoder.ogg.file = 0;
#endif

	e->fin = infile;
	e->fout = 0;
	e->seek_table_template = 0;

	if(e->is_stdout) {
		e->fout = grabbag__file_get_binary_stdout();
	}

	if(0 == (e->seek_table_template = FLAC__metadata_object_new(FLAC__METADATA_TYPE_SEEKTABLE))) {
		flac__utils_printf(stderr, 1, "%s: ERROR allocating memory for seek table\n", e->inbasefilename);
		return false;
	}

#ifdef FLAC__HAS_OGG
	if(e->use_ogg) {
		if(e->is_stdout) {
			e->encoder.ogg.stream = OggFLAC__stream_encoder_new();
			if(0 == e->encoder.ogg.stream) {
				flac__utils_printf(stderr, 1, "%s: ERROR creating the encoder instance\n", e->inbasefilename);
				EncoderSession_destroy(e);
				return false;
			}
		}
		else {
			e->encoder.ogg.file = OggFLAC__file_encoder_new();
			if(0 == e->encoder.ogg.file) {
				flac__utils_printf(stderr, 1, "%s: ERROR creating the encoder instance\n", e->inbasefilename);
				EncoderSession_destroy(e);
				return false;
			}
		}
	}
	else
#endif
	if(e->is_stdout) {
		e->encoder.flac.stream = FLAC__stream_encoder_new();
		if(0 == e->encoder.flac.stream) {
			flac__utils_printf(stderr, 1, "%s: ERROR creating the encoder instance\n", e->inbasefilename);
			EncoderSession_destroy(e);
			return false;
		}
	}
	else {
		e->encoder.flac.file = FLAC__file_encoder_new();
		if(0 == e->encoder.flac.file) {
			flac__utils_printf(stderr, 1, "%s: ERROR creating the encoder instance\n", e->inbasefilename);
			EncoderSession_destroy(e);
			return false;
		}
	}

	return true;
}

void EncoderSession_destroy(EncoderSession *e)
{
	if(e->fin != stdin)
		fclose(e->fin);
	if(0 != e->fout && e->fout != stdout)
		fclose(e->fout);

#ifdef FLAC__HAS_OGG
	if(e->use_ogg) {
		if(e->is_stdout) {
			if(0 != e->encoder.ogg.stream) {
				OggFLAC__stream_encoder_delete(e->encoder.ogg.stream);
				e->encoder.ogg.stream = 0;
			}
		}
		else {
			if(0 != e->encoder.ogg.file) {
				OggFLAC__file_encoder_delete(e->encoder.ogg.file);
				e->encoder.ogg.file = 0;
			}
		}
	}
	else
#endif
	if(e->is_stdout) {
		if(0 != e->encoder.flac.stream) {
			FLAC__stream_encoder_delete(e->encoder.flac.stream);
			e->encoder.flac.stream = 0;
		}
	}
	else {
		if(0 != e->encoder.flac.file) {
			FLAC__file_encoder_delete(e->encoder.flac.file);
			e->encoder.flac.file = 0;
		}
	}

	if(0 != e->seek_table_template) {
		FLAC__metadata_object_delete(e->seek_table_template);
		e->seek_table_template = 0;
	}
}

int EncoderSession_finish_ok(EncoderSession *e, int info_align_carry, int info_align_zero)
{
	FLAC__StreamEncoderState fse_state = FLAC__STREAM_ENCODER_OK;
	int ret = 0;

#ifdef FLAC__HAS_OGG
	if(e->use_ogg) {
		if(e->is_stdout) {
			if(e->encoder.ogg.stream) {
				fse_state = OggFLAC__stream_encoder_get_FLAC_stream_encoder_state(e->encoder.ogg.stream);
				OggFLAC__stream_encoder_finish(e->encoder.ogg.stream);
			}
		}
		else {
			if(e->encoder.ogg.file) {
				fse_state = OggFLAC__file_encoder_get_FLAC_stream_encoder_state(e->encoder.ogg.file);
				OggFLAC__file_encoder_finish(e->encoder.ogg.file);
			}
		}
	}
	else
#endif
	if(e->is_stdout) {
		if(e->encoder.flac.stream) {
			fse_state = FLAC__stream_encoder_get_state(e->encoder.flac.stream);
			FLAC__stream_encoder_finish(e->encoder.flac.stream);
		}
	}
	else {
		if(e->encoder.flac.file) {
			fse_state = FLAC__file_encoder_get_stream_encoder_state(e->encoder.flac.file);
			FLAC__file_encoder_finish(e->encoder.flac.file);
		}
	}

	if(e->total_samples_to_encode > 0) {
		print_stats(e);
		flac__utils_printf(stderr, 2, "\n");
	}

	if(fse_state == FLAC__STREAM_ENCODER_VERIFY_MISMATCH_IN_AUDIO_DATA) {
		print_verify_error(e);
		ret = 1;
	}
	else {
		if(info_align_carry >= 0) {
			flac__utils_printf(stderr, 1, "%s: INFO: sector alignment causing %d samples to be carried over\n", e->inbasefilename, info_align_carry);
		}
		if(info_align_zero >= 0) {
			flac__utils_printf(stderr, 1, "%s: INFO: sector alignment causing %d zero samples to be appended\n", e->inbasefilename, info_align_zero);
		}
	}

	EncoderSession_destroy(e);

	return ret;
}

int EncoderSession_finish_error(EncoderSession *e)
{
	FLAC__StreamEncoderState fse_state;

	if(e->total_samples_to_encode > 0)
		flac__utils_printf(stderr, 2, "\n");

#ifdef FLAC__HAS_OGG
	if(e->use_ogg) {
		if(e->is_stdout) {
			fse_state = OggFLAC__stream_encoder_get_FLAC_stream_encoder_state(e->encoder.ogg.stream);
		}
		else {
			fse_state = OggFLAC__file_encoder_get_FLAC_stream_encoder_state(e->encoder.ogg.file);
		}
	}
	else
#endif
	if(e->is_stdout) {
		fse_state = FLAC__stream_encoder_get_state(e->encoder.flac.stream);
	}
	else {
		fse_state = FLAC__file_encoder_get_stream_encoder_state(e->encoder.flac.file);
	}

	if(fse_state == FLAC__STREAM_ENCODER_VERIFY_MISMATCH_IN_AUDIO_DATA)
		print_verify_error(e);
	else
		/*@@@@@@@@@ BUG: if error was caused because the output file already exists but the file encoder could not write on top of it (i.e. it's not writable), this will delete the pre-existing file, which is not what we want */
		unlink(e->outfilename);

	EncoderSession_destroy(e);

	return 1;
}

FLAC__bool EncoderSession_init_encoder(EncoderSession *e, encode_options_t options, unsigned channels, unsigned bps, unsigned sample_rate, FLACDecoderData *flac_decoder_data)
{
	unsigned num_metadata;
	FLAC__StreamMetadata padding, *cuesheet = 0;
	FLAC__StreamMetadata *static_metadata[4];
	FLAC__StreamMetadata **metadata = static_metadata;
	const FLAC__bool is_cdda = (channels == 1 || channels == 2) && (bps == 16) && (sample_rate == 44100);

	e->replay_gain = options.replay_gain;
	e->channels = channels;
	e->bits_per_sample = bps;
	e->sample_rate = sample_rate;

	if(e->replay_gain) {
		if(channels != 1 && channels != 2) {
			flac__utils_printf(stderr, 1, "%s: ERROR, number of channels (%u) must be 1 or 2 for --replay-gain\n", e->inbasefilename, channels);
			return false;
		}
		if(!grabbag__replaygain_is_valid_sample_frequency(sample_rate)) {
			flac__utils_printf(stderr, 1, "%s: ERROR, invalid sample rate (%u) for --replay-gain\n", e->inbasefilename, sample_rate);
			return false;
		}
		if(options.is_first_file) {
			if(!grabbag__replaygain_init(sample_rate)) {
				flac__utils_printf(stderr, 1, "%s: ERROR initializing ReplayGain stage\n", e->inbasefilename);
				return false;
			}
		}
	}

	if(channels != 2)
		options.do_mid_side = options.loose_mid_side = false;

	if(!parse_cuesheet(&cuesheet, options.cuesheet_filename, e->inbasefilename, is_cdda, e->total_samples_to_encode))
		return false;

	if(!convert_to_seek_table_template(options.requested_seek_points, options.num_requested_seek_points, options.cued_seekpoints? cuesheet : 0, e)) {
		flac__utils_printf(stderr, 1, "%s: ERROR allocating memory for seek table\n", e->inbasefilename);
		if(0 != cuesheet)
			FLAC__metadata_object_delete(cuesheet);
		return false;
	}

	if(flac_decoder_data) {
		/*
		 * we're encoding from FLAC so we will use the FLAC file's
		 * metadata as the basic for the encoded file
		 */
		{
			/*
			 * first handle padding: if --no-padding was specified,
			 * then delete all padding; else if -P was specified,
			 * use that instead of existing padding (if any); else
			 * if existing file has padding, move all existing
			 * padding blocks to one padding block at the end; else
			 * use default padding.
			 */
			int p = -1;
			size_t i, j;
			for(i = 0, j = 0; i < flac_decoder_data->num_metadata_blocks; i++) {
				if(flac_decoder_data->metadata_blocks[i]->type == FLAC__METADATA_TYPE_PADDING) {
					if(p < 0)
						p = 0;
					p += flac_decoder_data->metadata_blocks[i]->length;
					FLAC__metadata_object_delete(flac_decoder_data->metadata_blocks[i]);
					flac_decoder_data->metadata_blocks[i] = 0;
				}
				else
					flac_decoder_data->metadata_blocks[j++] = flac_decoder_data->metadata_blocks[i];
			}
			flac_decoder_data->num_metadata_blocks = j;
			if(options.padding > 0)
				p = options.padding;
			if(p < 0)
				p = FLAC_ENCODE__DEFAULT_PADDING;
			if(options.padding != 0) {
				if(p > 0 && flac_decoder_data->num_metadata_blocks < sizeof(flac_decoder_data->metadata_blocks)/sizeof(flac_decoder_data->metadata_blocks[0])) {
					flac_decoder_data->metadata_blocks[flac_decoder_data->num_metadata_blocks] = FLAC__metadata_object_new(FLAC__METADATA_TYPE_PADDING);
					if(0 == flac_decoder_data->metadata_blocks[flac_decoder_data->num_metadata_blocks]) {
						flac__utils_printf(stderr, 1, "%s: ERROR allocating memory for PADDING block\n", e->inbasefilename);
						if(0 != cuesheet)
							FLAC__metadata_object_delete(cuesheet);
						return false;
					}
					flac_decoder_data->metadata_blocks[flac_decoder_data->num_metadata_blocks]->is_last = false; /* the encoder will set this for us */
					flac_decoder_data->metadata_blocks[flac_decoder_data->num_metadata_blocks]->length = p;
					flac_decoder_data->num_metadata_blocks++;
				}
			}
		}
		{
			/*
			 * next handle vorbis comment: if any tags were specified
			 * or there is no existing vorbis comment, we create a
			 * new vorbis comment (discarding any existing one); else
			 * we keep the existing one
			 */
			size_t i, j;
			FLAC__bool vc_found = false;
			for(i = 0, j = 0; i < flac_decoder_data->num_metadata_blocks; i++) {
				if(flac_decoder_data->metadata_blocks[i]->type == FLAC__METADATA_TYPE_VORBIS_COMMENT)
					vc_found = true;
				if(flac_decoder_data->metadata_blocks[i]->type == FLAC__METADATA_TYPE_VORBIS_COMMENT && options.vorbis_comment->data.vorbis_comment.num_comments > 0) {
					if(options.vorbis_comment->data.vorbis_comment.num_comments > 0)
						flac__utils_printf(stderr, 1, "%s: WARNING, replacing tags from input FLAC file with those given on the command-line\n", e->inbasefilename);
					FLAC__metadata_object_delete(flac_decoder_data->metadata_blocks[i]);
					flac_decoder_data->metadata_blocks[i] = 0;
				}
				else
					flac_decoder_data->metadata_blocks[j++] = flac_decoder_data->metadata_blocks[i];
			}
			flac_decoder_data->num_metadata_blocks = j;
			if((!vc_found || options.vorbis_comment->data.vorbis_comment.num_comments > 0) && flac_decoder_data->num_metadata_blocks < sizeof(flac_decoder_data->metadata_blocks)/sizeof(flac_decoder_data->metadata_blocks[0])) {
				/* prepend ours */
				FLAC__StreamMetadata *vc = FLAC__metadata_object_clone(options.vorbis_comment);
				if(0 == vc) {
					flac__utils_printf(stderr, 1, "%s: ERROR allocating memory for VORBIS_COMMENT block\n", e->inbasefilename);
					if(0 != cuesheet)
						FLAC__metadata_object_delete(cuesheet);
					return false;
				}
				for(i = flac_decoder_data->num_metadata_blocks; i > 1; i--)
					flac_decoder_data->metadata_blocks[i] = flac_decoder_data->metadata_blocks[i-1];
				flac_decoder_data->metadata_blocks[1] = vc;
				flac_decoder_data->num_metadata_blocks++;
			}
		}
		{
			/*
			 * next handle cuesheet: if --cuesheet was specified, use
			 * it; else if file has existing CUESHEET and cuesheet's
			 * lead-out offset is correct, keep it; else no CUESHEET
			 */
			size_t i, j;
			for(i = 0, j = 0; i < flac_decoder_data->num_metadata_blocks; i++) {
				FLAC__bool existing_cuesheet_is_bad = false;
				/* check if existing cuesheet matches the input audio */
				if(flac_decoder_data->metadata_blocks[i]->type == FLAC__METADATA_TYPE_CUESHEET && 0 == cuesheet) {
					const FLAC__StreamMetadata_CueSheet *cs = &flac_decoder_data->metadata_blocks[i]->data.cue_sheet;
					if(e->total_samples_to_encode == 0) {
						flac__utils_printf(stderr, 1, "%s: WARNING, cuesheet in input FLAC file cannot be kept if input size is not known, dropping it...\n", e->inbasefilename);
						existing_cuesheet_is_bad = true;
					}
					else if(e->total_samples_to_encode != cs->tracks[cs->num_tracks-1].offset) {
						flac__utils_printf(stderr, 1, "%s: WARNING, lead-out offset of cuesheet in input FLAC file does not match input length, dropping existing cuesheet...\n", e->inbasefilename);
						existing_cuesheet_is_bad = true;
					}
				}
				if(flac_decoder_data->metadata_blocks[i]->type == FLAC__METADATA_TYPE_CUESHEET && (existing_cuesheet_is_bad || 0 != cuesheet)) {
					if(0 != cuesheet)
						flac__utils_printf(stderr, 1, "%s: WARNING, replacing cuesheet in input FLAC file with the one given on the command-line\n", e->inbasefilename);
					FLAC__metadata_object_delete(flac_decoder_data->metadata_blocks[i]);
					flac_decoder_data->metadata_blocks[i] = 0;
				}
				else
					flac_decoder_data->metadata_blocks[j++] = flac_decoder_data->metadata_blocks[i];
			}
			flac_decoder_data->num_metadata_blocks = j;
			if(0 != cuesheet && flac_decoder_data->num_metadata_blocks < sizeof(flac_decoder_data->metadata_blocks)/sizeof(flac_decoder_data->metadata_blocks[0])) {
				/* prepend ours */
				FLAC__StreamMetadata *cs = FLAC__metadata_object_clone(cuesheet);
				if(0 == cs) {
					flac__utils_printf(stderr, 1, "%s: ERROR allocating memory for CUESHEET block\n", e->inbasefilename);
					if(0 != cuesheet)
						FLAC__metadata_object_delete(cuesheet);
					return false;
				}
				for(i = flac_decoder_data->num_metadata_blocks; i > 1; i--)
					flac_decoder_data->metadata_blocks[i] = flac_decoder_data->metadata_blocks[i-1];
				flac_decoder_data->metadata_blocks[1] = cs;
				flac_decoder_data->num_metadata_blocks++;
			}
		}
		{
			/*
			 * finally handle seektable: if -S- was specified, no
			 * SEEKTABLE; else if -S was specified, use it/them;
			 * else if file has existing SEEKTABLE and input size is
			 * preserved (no --skip/--until/etc specified), keep it;
			 * else use default seektable options
			 *
			 * note: meanings of num_requested_seek_points:
			 *  -1 : no -S option given, default to some value
			 *   0 : -S- given (no seektable)
			 *  >0 : one or more -S options given
			 */
			size_t i, j;
			FLAC__bool existing_seektable = false;
			for(i = 0, j = 0; i < flac_decoder_data->num_metadata_blocks; i++) {
				if(flac_decoder_data->metadata_blocks[i]->type == FLAC__METADATA_TYPE_SEEKTABLE)
					existing_seektable = true;
				if(flac_decoder_data->metadata_blocks[i]->type == FLAC__METADATA_TYPE_SEEKTABLE && (e->total_samples_to_encode != flac_decoder_data->metadata_blocks[0]->data.stream_info.total_samples || options.num_requested_seek_points >= 0)) {
					if(options.num_requested_seek_points > 0)
						flac__utils_printf(stderr, 1, "%s: WARNING, replacing seektable in input FLAC file with the one given on the command-line\n", e->inbasefilename);
					else if(options.num_requested_seek_points == 0)
						; /* no warning, silently delete existing SEEKTABLE since user specified --no-seektable (-S-) */
					else
						flac__utils_printf(stderr, 1, "%s: WARNING, can't use existing seektable in input FLAC since the input size is changing or unknown, dropping existing SEEKTABLE block...\n", e->inbasefilename);
					FLAC__metadata_object_delete(flac_decoder_data->metadata_blocks[i]);
					flac_decoder_data->metadata_blocks[i] = 0;
					existing_seektable = false;
				}
				else
					flac_decoder_data->metadata_blocks[j++] = flac_decoder_data->metadata_blocks[i];
			}
			flac_decoder_data->num_metadata_blocks = j;
			if((options.num_requested_seek_points > 0 || (options.num_requested_seek_points < 0 && !existing_seektable)) && flac_decoder_data->num_metadata_blocks < sizeof(flac_decoder_data->metadata_blocks)/sizeof(flac_decoder_data->metadata_blocks[0])) {
				/* prepend ours */
				FLAC__StreamMetadata *st = FLAC__metadata_object_clone(e->seek_table_template);
				if(0 == st) {
					flac__utils_printf(stderr, 1, "%s: ERROR allocating memory for SEEKTABLE block\n", e->inbasefilename);
					if(0 != cuesheet)
						FLAC__metadata_object_delete(cuesheet);
					return false;
				}
				for(i = flac_decoder_data->num_metadata_blocks; i > 1; i--)
					flac_decoder_data->metadata_blocks[i] = flac_decoder_data->metadata_blocks[i-1];
				flac_decoder_data->metadata_blocks[1] = st;
				flac_decoder_data->num_metadata_blocks++;
			}
		}
		metadata = &flac_decoder_data->metadata_blocks[1]; /* don't include STREAMINFO */
		num_metadata = flac_decoder_data->num_metadata_blocks - 1;
	}
	else {
		/*
		 * we're not encoding from FLAC so we will build the metadata
		 * from scratch
		 */
		num_metadata = 0;
		if(e->seek_table_template->data.seek_table.num_points > 0) {
			e->seek_table_template->is_last = false; /* the encoder will set this for us */
			metadata[num_metadata++] = e->seek_table_template;
		}
		if(0 != cuesheet)
			metadata[num_metadata++] = cuesheet;
		metadata[num_metadata++] = options.vorbis_comment;
		if(options.padding != 0) {
			padding.is_last = false; /* the encoder will set this for us */
			padding.type = FLAC__METADATA_TYPE_PADDING;
			padding.length = (unsigned)(options.padding>0? options.padding : FLAC_ENCODE__DEFAULT_PADDING);
			metadata[num_metadata++] = &padding;
		}
	}

	e->blocksize = options.blocksize;
	e->stats_mask = (options.do_exhaustive_model_search || options.do_qlp_coeff_prec_search)? 0x0f : 0x3f;

#ifdef FLAC__HAS_OGG
	if(e->use_ogg) {
		if(e->is_stdout) {
			OggFLAC__stream_encoder_set_serial_number(e->encoder.ogg.stream, options.serial_number);
			OggFLAC__stream_encoder_set_verify(e->encoder.ogg.stream, options.verify);
			OggFLAC__stream_encoder_set_streamable_subset(e->encoder.ogg.stream, !options.lax);
			OggFLAC__stream_encoder_set_do_mid_side_stereo(e->encoder.ogg.stream, options.do_mid_side);
			OggFLAC__stream_encoder_set_loose_mid_side_stereo(e->encoder.ogg.stream, options.loose_mid_side);
			OggFLAC__stream_encoder_set_channels(e->encoder.ogg.stream, channels);
			OggFLAC__stream_encoder_set_bits_per_sample(e->encoder.ogg.stream, bps);
			OggFLAC__stream_encoder_set_sample_rate(e->encoder.ogg.stream, sample_rate);
			OggFLAC__stream_encoder_set_blocksize(e->encoder.ogg.stream, options.blocksize);
			OggFLAC__stream_encoder_set_apodization(e->encoder.ogg.stream, options.apodizations);
			OggFLAC__stream_encoder_set_max_lpc_order(e->encoder.ogg.stream, options.max_lpc_order);
			OggFLAC__stream_encoder_set_qlp_coeff_precision(e->encoder.ogg.stream, options.qlp_coeff_precision);
			OggFLAC__stream_encoder_set_do_qlp_coeff_prec_search(e->encoder.ogg.stream, options.do_qlp_coeff_prec_search);
			OggFLAC__stream_encoder_set_do_escape_coding(e->encoder.ogg.stream, options.do_escape_coding);
			OggFLAC__stream_encoder_set_do_exhaustive_model_search(e->encoder.ogg.stream, options.do_exhaustive_model_search);
			OggFLAC__stream_encoder_set_min_residual_partition_order(e->encoder.ogg.stream, options.min_residual_partition_order);
			OggFLAC__stream_encoder_set_max_residual_partition_order(e->encoder.ogg.stream, options.max_residual_partition_order);
			OggFLAC__stream_encoder_set_rice_parameter_search_dist(e->encoder.ogg.stream, options.rice_parameter_search_dist);
			OggFLAC__stream_encoder_set_total_samples_estimate(e->encoder.ogg.stream, e->total_samples_to_encode);
			OggFLAC__stream_encoder_set_metadata(e->encoder.ogg.stream, (num_metadata > 0)? metadata : 0, num_metadata);
			OggFLAC__stream_encoder_set_write_callback(e->encoder.ogg.stream, ogg_stream_encoder_write_callback);
			OggFLAC__stream_encoder_set_metadata_callback(e->encoder.ogg.stream, ogg_stream_encoder_metadata_callback);
			OggFLAC__stream_encoder_set_client_data(e->encoder.ogg.stream, e);

			OggFLAC__stream_encoder_disable_constant_subframes(e->encoder.ogg.stream, options.debug.disable_constant_subframes);
			OggFLAC__stream_encoder_disable_fixed_subframes(e->encoder.ogg.stream, options.debug.disable_fixed_subframes);
			OggFLAC__stream_encoder_disable_verbatim_subframes(e->encoder.ogg.stream, options.debug.disable_verbatim_subframes);

			if(OggFLAC__stream_encoder_init(e->encoder.ogg.stream) != FLAC__STREAM_ENCODER_OK) {
				print_error_with_state(e, "ERROR initializing encoder");
				if(0 != cuesheet)
					FLAC__metadata_object_delete(cuesheet);
				return false;
			}
		}
		else {
			OggFLAC__file_encoder_set_serial_number(e->encoder.ogg.file, options.serial_number);
			OggFLAC__file_encoder_set_filename(e->encoder.ogg.file, e->outfilename);
			OggFLAC__file_encoder_set_verify(e->encoder.ogg.file, options.verify);
			OggFLAC__file_encoder_set_streamable_subset(e->encoder.ogg.file, !options.lax);
			OggFLAC__file_encoder_set_do_mid_side_stereo(e->encoder.ogg.file, options.do_mid_side);
			OggFLAC__file_encoder_set_loose_mid_side_stereo(e->encoder.ogg.file, options.loose_mid_side);
			OggFLAC__file_encoder_set_channels(e->encoder.ogg.file, channels);
			OggFLAC__file_encoder_set_bits_per_sample(e->encoder.ogg.file, bps);
			OggFLAC__file_encoder_set_sample_rate(e->encoder.ogg.file, sample_rate);
			OggFLAC__file_encoder_set_blocksize(e->encoder.ogg.file, options.blocksize);
			OggFLAC__file_encoder_set_apodization(e->encoder.ogg.file, options.apodizations);
			OggFLAC__file_encoder_set_max_lpc_order(e->encoder.ogg.file, options.max_lpc_order);
			OggFLAC__file_encoder_set_qlp_coeff_precision(e->encoder.ogg.file, options.qlp_coeff_precision);
			OggFLAC__file_encoder_set_do_qlp_coeff_prec_search(e->encoder.ogg.file, options.do_qlp_coeff_prec_search);
			OggFLAC__file_encoder_set_do_escape_coding(e->encoder.ogg.file, options.do_escape_coding);
			OggFLAC__file_encoder_set_do_exhaustive_model_search(e->encoder.ogg.file, options.do_exhaustive_model_search);
			OggFLAC__file_encoder_set_min_residual_partition_order(e->encoder.ogg.file, options.min_residual_partition_order);
			OggFLAC__file_encoder_set_max_residual_partition_order(e->encoder.ogg.file, options.max_residual_partition_order);
			OggFLAC__file_encoder_set_rice_parameter_search_dist(e->encoder.ogg.file, options.rice_parameter_search_dist);
			OggFLAC__file_encoder_set_total_samples_estimate(e->encoder.ogg.file, e->total_samples_to_encode);
			OggFLAC__file_encoder_set_metadata(e->encoder.ogg.file, (num_metadata > 0)? metadata : 0, num_metadata);
			OggFLAC__file_encoder_set_progress_callback(e->encoder.ogg.file, ogg_file_encoder_progress_callback);
			OggFLAC__file_encoder_set_client_data(e->encoder.ogg.file, e);

			OggFLAC__file_encoder_disable_constant_subframes(e->encoder.ogg.file, options.debug.disable_constant_subframes);
			OggFLAC__file_encoder_disable_fixed_subframes(e->encoder.ogg.file, options.debug.disable_fixed_subframes);
			OggFLAC__file_encoder_disable_verbatim_subframes(e->encoder.ogg.file, options.debug.disable_verbatim_subframes);

			if(OggFLAC__file_encoder_init(e->encoder.ogg.file) != OggFLAC__FILE_ENCODER_OK) {
				print_error_with_state(e, "ERROR initializing encoder");
				if(0 != cuesheet)
					FLAC__metadata_object_delete(cuesheet);
				return false;
			}
		}
	}
	else
#endif
	if(e->is_stdout) {
		FLAC__stream_encoder_set_verify(e->encoder.flac.stream, options.verify);
		FLAC__stream_encoder_set_streamable_subset(e->encoder.flac.stream, !options.lax);
		FLAC__stream_encoder_set_do_mid_side_stereo(e->encoder.flac.stream, options.do_mid_side);
		FLAC__stream_encoder_set_loose_mid_side_stereo(e->encoder.flac.stream, options.loose_mid_side);
		FLAC__stream_encoder_set_channels(e->encoder.flac.stream, channels);
		FLAC__stream_encoder_set_bits_per_sample(e->encoder.flac.stream, bps);
		FLAC__stream_encoder_set_sample_rate(e->encoder.flac.stream, sample_rate);
		FLAC__stream_encoder_set_blocksize(e->encoder.flac.stream, options.blocksize);
		FLAC__stream_encoder_set_apodization(e->encoder.flac.stream, options.apodizations);
		FLAC__stream_encoder_set_max_lpc_order(e->encoder.flac.stream, options.max_lpc_order);
		FLAC__stream_encoder_set_qlp_coeff_precision(e->encoder.flac.stream, options.qlp_coeff_precision);
		FLAC__stream_encoder_set_do_qlp_coeff_prec_search(e->encoder.flac.stream, options.do_qlp_coeff_prec_search);
		FLAC__stream_encoder_set_do_escape_coding(e->encoder.flac.stream, options.do_escape_coding);
		FLAC__stream_encoder_set_do_exhaustive_model_search(e->encoder.flac.stream, options.do_exhaustive_model_search);
		FLAC__stream_encoder_set_min_residual_partition_order(e->encoder.flac.stream, options.min_residual_partition_order);
		FLAC__stream_encoder_set_max_residual_partition_order(e->encoder.flac.stream, options.max_residual_partition_order);
		FLAC__stream_encoder_set_rice_parameter_search_dist(e->encoder.flac.stream, options.rice_parameter_search_dist);
		FLAC__stream_encoder_set_total_samples_estimate(e->encoder.flac.stream, e->total_samples_to_encode);
		FLAC__stream_encoder_set_metadata(e->encoder.flac.stream, (num_metadata > 0)? metadata : 0, num_metadata);
		FLAC__stream_encoder_set_write_callback(e->encoder.flac.stream, flac_stream_encoder_write_callback);
		FLAC__stream_encoder_set_metadata_callback(e->encoder.flac.stream, flac_stream_encoder_metadata_callback);
		FLAC__stream_encoder_set_client_data(e->encoder.flac.stream, e);

		FLAC__stream_encoder_disable_constant_subframes(e->encoder.flac.stream, options.debug.disable_constant_subframes);
		FLAC__stream_encoder_disable_fixed_subframes(e->encoder.flac.stream, options.debug.disable_fixed_subframes);
		FLAC__stream_encoder_disable_verbatim_subframes(e->encoder.flac.stream, options.debug.disable_verbatim_subframes);

		if(FLAC__stream_encoder_init(e->encoder.flac.stream) != FLAC__STREAM_ENCODER_OK) {
			print_error_with_state(e, "ERROR initializing encoder");
			if(0 != cuesheet)
				FLAC__metadata_object_delete(cuesheet);
			return false;
		}
	}
	else {
		FLAC__file_encoder_set_filename(e->encoder.flac.file, e->outfilename);
		FLAC__file_encoder_set_verify(e->encoder.flac.file, options.verify);
		FLAC__file_encoder_set_streamable_subset(e->encoder.flac.file, !options.lax);
		FLAC__file_encoder_set_do_mid_side_stereo(e->encoder.flac.file, options.do_mid_side);
		FLAC__file_encoder_set_loose_mid_side_stereo(e->encoder.flac.file, options.loose_mid_side);
		FLAC__file_encoder_set_channels(e->encoder.flac.file, channels);
		FLAC__file_encoder_set_bits_per_sample(e->encoder.flac.file, bps);
		FLAC__file_encoder_set_sample_rate(e->encoder.flac.file, sample_rate);
		FLAC__file_encoder_set_blocksize(e->encoder.flac.file, options.blocksize);
		FLAC__file_encoder_set_apodization(e->encoder.flac.file, options.apodizations);
		FLAC__file_encoder_set_max_lpc_order(e->encoder.flac.file, options.max_lpc_order);
		FLAC__file_encoder_set_qlp_coeff_precision(e->encoder.flac.file, options.qlp_coeff_precision);
		FLAC__file_encoder_set_do_qlp_coeff_prec_search(e->encoder.flac.file, options.do_qlp_coeff_prec_search);
		FLAC__file_encoder_set_do_escape_coding(e->encoder.flac.file, options.do_escape_coding);
		FLAC__file_encoder_set_do_exhaustive_model_search(e->encoder.flac.file, options.do_exhaustive_model_search);
		FLAC__file_encoder_set_min_residual_partition_order(e->encoder.flac.file, options.min_residual_partition_order);
		FLAC__file_encoder_set_max_residual_partition_order(e->encoder.flac.file, options.max_residual_partition_order);
		FLAC__file_encoder_set_rice_parameter_search_dist(e->encoder.flac.file, options.rice_parameter_search_dist);
		FLAC__file_encoder_set_total_samples_estimate(e->encoder.flac.file, e->total_samples_to_encode);
		FLAC__file_encoder_set_metadata(e->encoder.flac.file, (num_metadata > 0)? metadata : 0, num_metadata);
		FLAC__file_encoder_set_progress_callback(e->encoder.flac.file, flac_file_encoder_progress_callback);
		FLAC__file_encoder_set_client_data(e->encoder.flac.file, e);

		FLAC__file_encoder_disable_constant_subframes(e->encoder.flac.file, options.debug.disable_constant_subframes);
		FLAC__file_encoder_disable_fixed_subframes(e->encoder.flac.file, options.debug.disable_fixed_subframes);
		FLAC__file_encoder_disable_verbatim_subframes(e->encoder.flac.file, options.debug.disable_verbatim_subframes);

		if(FLAC__file_encoder_init(e->encoder.flac.file) != FLAC__FILE_ENCODER_OK) {
			print_error_with_state(e, "ERROR initializing encoder");
			if(0 != cuesheet)
				FLAC__metadata_object_delete(cuesheet);
			return false;
		}
	}

	if(0 != cuesheet)
		FLAC__metadata_object_delete(cuesheet);

	return true;
}

FLAC__bool EncoderSession_process(EncoderSession *e, const FLAC__int32 * const buffer[], unsigned samples)
{
	if(e->replay_gain) {
		if(!grabbag__replaygain_analyze(buffer, e->channels==2, e->bits_per_sample, samples)) {
			flac__utils_printf(stderr, 1, "%s: WARNING, error while calculating ReplayGain\n", e->inbasefilename);
		}
	}

#ifdef FLAC__HAS_OGG
	if(e->use_ogg) {
		if(e->is_stdout) {
			return OggFLAC__stream_encoder_process(e->encoder.ogg.stream, buffer, samples);
		}
		else {
			return OggFLAC__file_encoder_process(e->encoder.ogg.file, buffer, samples);
		}
	}
	else
#endif
	if(e->is_stdout) {
		return FLAC__stream_encoder_process(e->encoder.flac.stream, buffer, samples);
	}
	else {
		return FLAC__file_encoder_process(e->encoder.flac.file, buffer, samples);
	}
}

FLAC__bool convert_to_seek_table_template(const char *requested_seek_points, int num_requested_seek_points, FLAC__StreamMetadata *cuesheet, EncoderSession *e)
{
	const FLAC__bool only_placeholders = e->is_stdout;
	FLAC__bool has_real_points;

	if(num_requested_seek_points == 0 && 0 == cuesheet)
		return true;

	if(num_requested_seek_points < 0) {
		requested_seek_points = "10s;";
		num_requested_seek_points = 1;
	}

	if(num_requested_seek_points > 0) {
		if(!grabbag__seektable_convert_specification_to_template(requested_seek_points, only_placeholders, e->total_samples_to_encode, e->sample_rate, e->seek_table_template, &has_real_points))
			return false;
	}

	if(0 != cuesheet) {
		unsigned i, j;
		const FLAC__StreamMetadata_CueSheet *cs = &cuesheet->data.cue_sheet;
		for(i = 0; i < cs->num_tracks; i++) {
			const FLAC__StreamMetadata_CueSheet_Track *tr = cs->tracks+i;
			for(j = 0; j < tr->num_indices; j++) {
				if(!FLAC__metadata_object_seektable_template_append_point(e->seek_table_template, tr->offset + tr->indices[j].offset))
					return false;
				has_real_points = true;
			}
		}
		if(has_real_points)
			if(!FLAC__metadata_object_seektable_template_sort(e->seek_table_template, /*compact=*/true))
				return false;
	}

	if(has_real_points) {
		if(e->is_stdout) {
			flac__utils_printf(stderr, 1, "%s: WARNING, cannot write back seekpoints when encoding to stdout\n", e->inbasefilename);
		}
	}

	return true;
}

FLAC__bool canonicalize_until_specification(utils__SkipUntilSpecification *spec, const char *inbasefilename, unsigned sample_rate, FLAC__uint64 skip, FLAC__uint64 total_samples_in_input)
{
	/* convert from mm:ss.sss to sample number if necessary */
	flac__utils_canonicalize_skip_until_specification(spec, sample_rate);

	/* special case: if "--until=-0", use the special value '0' to mean "end-of-stream" */
	if(spec->is_relative && spec->value.samples == 0) {
		spec->is_relative = false;
		return true;
	}

	/* in any other case the total samples in the input must be known */
	if(total_samples_in_input == 0) {
		flac__utils_printf(stderr, 1, "%s: ERROR, cannot use --until when input length is unknown\n", inbasefilename);
		return false;
	}

	FLAC__ASSERT(spec->value_is_samples);

	/* convert relative specifications to absolute */
	if(spec->is_relative) {
		if(spec->value.samples <= 0)
			spec->value.samples += (FLAC__int64)total_samples_in_input;
		else
			spec->value.samples += skip;
		spec->is_relative = false;
	}

	/* error check */
	if(spec->value.samples < 0) {
		flac__utils_printf(stderr, 1, "%s: ERROR, --until value is before beginning of input\n", inbasefilename);
		return false;
	}
	if((FLAC__uint64)spec->value.samples <= skip) {
		flac__utils_printf(stderr, 1, "%s: ERROR, --until value is before --skip point\n", inbasefilename);
		return false;
	}
	if((FLAC__uint64)spec->value.samples > total_samples_in_input) {
		flac__utils_printf(stderr, 1, "%s: ERROR, --until value is after end of input\n", inbasefilename);
		return false;
	}

	return true;
}

void format_input(FLAC__int32 *dest[], unsigned wide_samples, FLAC__bool is_big_endian, FLAC__bool is_unsigned_samples, unsigned channels, unsigned bps)
{
	unsigned wide_sample, sample, channel, byte;

	if(bps == 8) {
		if(is_unsigned_samples) {
			for(sample = wide_sample = 0; wide_sample < wide_samples; wide_sample++)
				for(channel = 0; channel < channels; channel++, sample++)
					dest[channel][wide_sample] = (FLAC__int32)ucbuffer_[sample] - 0x80;
		}
		else {
			for(sample = wide_sample = 0; wide_sample < wide_samples; wide_sample++)
				for(channel = 0; channel < channels; channel++, sample++)
					dest[channel][wide_sample] = (FLAC__int32)scbuffer_[sample];
		}
	}
	else if(bps == 16) {
		if(is_big_endian != is_big_endian_host_) {
			unsigned char tmp;
			const unsigned bytes = wide_samples * channels * (bps >> 3);
			for(byte = 0; byte < bytes; byte += 2) {
				tmp = ucbuffer_[byte];
				ucbuffer_[byte] = ucbuffer_[byte+1];
				ucbuffer_[byte+1] = tmp;
			}
		}
		if(is_unsigned_samples) {
			for(sample = wide_sample = 0; wide_sample < wide_samples; wide_sample++)
				for(channel = 0; channel < channels; channel++, sample++)
					dest[channel][wide_sample] = (FLAC__int32)usbuffer_[sample] - 0x8000;
		}
		else {
			for(sample = wide_sample = 0; wide_sample < wide_samples; wide_sample++)
				for(channel = 0; channel < channels; channel++, sample++)
					dest[channel][wide_sample] = (FLAC__int32)ssbuffer_[sample];
		}
	}
	else if(bps == 24) {
		if(!is_big_endian) {
			unsigned char tmp;
			const unsigned bytes = wide_samples * channels * (bps >> 3);
			for(byte = 0; byte < bytes; byte += 3) {
				tmp = ucbuffer_[byte];
				ucbuffer_[byte] = ucbuffer_[byte+2];
				ucbuffer_[byte+2] = tmp;
			}
		}
		if(is_unsigned_samples) {
			for(byte = sample = wide_sample = 0; wide_sample < wide_samples; wide_sample++)
				for(channel = 0; channel < channels; channel++, sample++) {
					dest[channel][wide_sample]  = ucbuffer_[byte++]; dest[channel][wide_sample] <<= 8;
					dest[channel][wide_sample] |= ucbuffer_[byte++]; dest[channel][wide_sample] <<= 8;
					dest[channel][wide_sample] |= ucbuffer_[byte++];
					dest[channel][wide_sample] -= 0x800000;
				}
		}
		else {
			for(byte = sample = wide_sample = 0; wide_sample < wide_samples; wide_sample++)
				for(channel = 0; channel < channels; channel++, sample++) {
					dest[channel][wide_sample]  = scbuffer_[byte++]; dest[channel][wide_sample] <<= 8;
					dest[channel][wide_sample] |= ucbuffer_[byte++]; dest[channel][wide_sample] <<= 8;
					dest[channel][wide_sample] |= ucbuffer_[byte++];
				}
		}
	}
	else {
		FLAC__ASSERT(0);
	}
}

#ifdef FLAC__HAS_OGG
FLAC__StreamEncoderWriteStatus ogg_stream_encoder_write_callback(const OggFLAC__StreamEncoder *encoder, const FLAC__byte buffer[], unsigned bytes, unsigned samples, unsigned current_frame, void *client_data)
{
	EncoderSession *encoder_session = (EncoderSession*)client_data;

	(void)encoder;

	encoder_session->bytes_written += bytes;
	/*
	 * With Ogg FLAC we don't get one write callback per frame and
	 * we don't have a good number for 'samples', so we estimate based
	 * on the frame number and the knowledge that all blocks (except
	 * the last) are the same size.
	 */
	(void)samples;
	encoder_session->samples_written = (current_frame+1) * encoder_session->blocksize;

	if(encoder_session->total_samples_to_encode > 0 && !(current_frame & encoder_session->stats_mask))
		print_stats(encoder_session);

	if(flac__utils_fwrite(buffer, sizeof(FLAC__byte), bytes, encoder_session->fout) == bytes)
		return FLAC__STREAM_ENCODER_WRITE_STATUS_OK;
	else
		return FLAC__STREAM_ENCODER_WRITE_STATUS_FATAL_ERROR;
}

void ogg_stream_encoder_metadata_callback(const OggFLAC__StreamEncoder *encoder, const FLAC__StreamMetadata *metadata, void *client_data)
{
	// do nothing, for compatibilty.  soon we will be using the ogg file encoder anyway.
	(void)encoder, (void)metadata, (void)client_data;
}

void ogg_file_encoder_progress_callback(const OggFLAC__FileEncoder *encoder, FLAC__uint64 bytes_written, FLAC__uint64 samples_written, unsigned frames_written, unsigned total_frames_estimate, void *client_data)
{
	EncoderSession *encoder_session = (EncoderSession*)client_data;

	(void)encoder;

	/*
	 * With Ogg FLAC we don't get a value for 'samples_written', so we
	 * estimate based on the frames written and the knowledge that all
	 * blocks (except the last) are the same size.
	 */
	samples_written = frames_written * encoder_session->blocksize;
	flac_file_encoder_progress_callback(0, bytes_written, samples_written, frames_written, total_frames_estimate, client_data);
}

#endif

FLAC__StreamEncoderWriteStatus flac_stream_encoder_write_callback(const FLAC__StreamEncoder *encoder, const FLAC__byte buffer[], unsigned bytes, unsigned samples, unsigned current_frame, void *client_data)
{
	EncoderSession *encoder_session = (EncoderSession*)client_data;

	(void)encoder;

	encoder_session->bytes_written += bytes;
	encoder_session->samples_written += samples;

	if(samples && encoder_session->total_samples_to_encode > 0 && !(current_frame & encoder_session->stats_mask))
		print_stats(encoder_session);

	if(flac__utils_fwrite(buffer, sizeof(FLAC__byte), bytes, encoder_session->fout) == bytes)
		return FLAC__STREAM_ENCODER_WRITE_STATUS_OK;
	else
		return FLAC__STREAM_ENCODER_WRITE_STATUS_FATAL_ERROR;
}

void flac_stream_encoder_metadata_callback(const FLAC__StreamEncoder *encoder, const FLAC__StreamMetadata *metadata, void *client_data)
{
	/*
	 * Nothing to do; if we get here, we're decoding to stdout, in
	 * which case we can't seek backwards to write new metadata.
	 */
	(void)encoder, (void)metadata, (void)client_data;
}

void flac_file_encoder_progress_callback(const FLAC__FileEncoder *encoder, FLAC__uint64 bytes_written, FLAC__uint64 samples_written, unsigned frames_written, unsigned total_frames_estimate, void *client_data)
{
	EncoderSession *encoder_session = (EncoderSession*)client_data;

	(void)encoder, (void)total_frames_estimate;

	encoder_session->bytes_written = bytes_written;
	encoder_session->samples_written = samples_written;

	if(encoder_session->total_samples_to_encode > 0 && !((frames_written-1) & encoder_session->stats_mask))
		print_stats(encoder_session);
}

FLAC__SeekableStreamDecoderReadStatus flac_decoder_read_callback(const FLAC__SeekableStreamDecoder *decoder, FLAC__byte buffer[], unsigned *bytes, void *client_data)
{
	size_t n = 0;
	FLACDecoderData *data = (FLACDecoderData*)client_data;
	(void)decoder;

	if (data->fatal_error)
		return FLAC__SEEKABLE_STREAM_DECODER_READ_STATUS_ERROR;

	/* use up lookahead first */
	if (data->lookahead_length) {
		n = min(data->lookahead_length, *bytes);
		memcpy(buffer, data->lookahead, n);
		buffer += n;
		data->lookahead += n;
		data->lookahead_length -= n;
	}

	/* get the rest from file */
	if (*bytes > n) {
		*bytes = n + fread(buffer, 1, *bytes-n, data->encoder_session->fin);
		return ferror(data->encoder_session->fin)? FLAC__SEEKABLE_STREAM_DECODER_READ_STATUS_ERROR : FLAC__SEEKABLE_STREAM_DECODER_READ_STATUS_OK;
	}
	else
		return FLAC__SEEKABLE_STREAM_DECODER_READ_STATUS_OK;
}

FLAC__SeekableStreamDecoderSeekStatus flac_decoder_seek_callback(const FLAC__SeekableStreamDecoder *decoder, FLAC__uint64 absolute_byte_offset, void *client_data)
{
	FLACDecoderData *data = (FLACDecoderData*)client_data;
	(void)decoder;

	if(fseeko(data->encoder_session->fin, (off_t)absolute_byte_offset, SEEK_SET) < 0)
		return FLAC__SEEKABLE_STREAM_DECODER_SEEK_STATUS_ERROR;
	else
		return FLAC__SEEKABLE_STREAM_DECODER_SEEK_STATUS_OK;
}

FLAC__SeekableStreamDecoderTellStatus flac_decoder_tell_callback(const FLAC__SeekableStreamDecoder *decoder, FLAC__uint64 *absolute_byte_offset, void *client_data)
{
	FLACDecoderData *data = (FLACDecoderData*)client_data;
	off_t pos;
	(void)decoder;

	if((pos = ftello(data->encoder_session->fin)) < 0)
		return FLAC__SEEKABLE_STREAM_DECODER_TELL_STATUS_ERROR;
	else {
		*absolute_byte_offset = (FLAC__uint64)pos;
		return FLAC__SEEKABLE_STREAM_DECODER_TELL_STATUS_OK;
	}
}

FLAC__SeekableStreamDecoderLengthStatus flac_decoder_length_callback(const FLAC__SeekableStreamDecoder *decoder, FLAC__uint64 *stream_length, void *client_data)
{
	FLACDecoderData *data = (FLACDecoderData*)client_data;
	(void)decoder;

	if(0 == data->filesize)
		return FLAC__SEEKABLE_STREAM_DECODER_LENGTH_STATUS_ERROR;
	else {
		*stream_length = (FLAC__uint64)data->filesize;
		return FLAC__SEEKABLE_STREAM_DECODER_LENGTH_STATUS_OK;
	}
}

FLAC__bool flac_decoder_eof_callback(const FLAC__SeekableStreamDecoder *decoder, void *client_data)
{
	FLACDecoderData *data = (FLACDecoderData*)client_data;
	(void)decoder;

	return feof(data->encoder_session->fin)? true : false;
}

FLAC__StreamDecoderWriteStatus flac_decoder_write_callback(const FLAC__SeekableStreamDecoder *decoder, const FLAC__Frame *frame, const FLAC__int32 * const buffer[], void *client_data)
{
	FLACDecoderData *data = (FLACDecoderData*)client_data;
	FLAC__uint64 n = min(data->samples_left_to_process, frame->header.blocksize);
	(void)decoder;

	if(!EncoderSession_process(data->encoder_session, buffer, n)) {
		print_error_with_state(data->encoder_session, "ERROR during encoding");
		data->fatal_error = true;
		return FLAC__STREAM_DECODER_WRITE_STATUS_ABORT;
	}

	data->samples_left_to_process -= n;
	return FLAC__STREAM_DECODER_WRITE_STATUS_CONTINUE;
}

void flac_decoder_metadata_callback(const FLAC__SeekableStreamDecoder *decoder, const FLAC__StreamMetadata *metadata, void *client_data)
{
	FLACDecoderData *data = (FLACDecoderData*)client_data;
	(void)decoder;

	if (data->fatal_error)
		return;

	if (
		data->num_metadata_blocks == sizeof(data->metadata_blocks)/sizeof(data->metadata_blocks[0]) ||
		0 == (data->metadata_blocks[data->num_metadata_blocks] = FLAC__metadata_object_clone(metadata))
	)
		data->fatal_error = true;
	else
		data->num_metadata_blocks++;
}

void flac_decoder_error_callback(const FLAC__SeekableStreamDecoder *decoder, FLAC__StreamDecoderErrorStatus status, void *client_data)
{
	FLACDecoderData *data = (FLACDecoderData*)client_data;
	(void)decoder;

	flac__utils_printf(stderr, 1, "%s: ERROR got %s while decoding FLAC input\n", data->encoder_session->inbasefilename, FLAC__StreamDecoderErrorStatusString[status]);
	data->fatal_error = true;
}

FLAC__bool parse_cuesheet(FLAC__StreamMetadata **cuesheet, const char *cuesheet_filename, const char *inbasefilename, FLAC__bool is_cdda, FLAC__uint64 lead_out_offset)
{
	FILE *f;
	unsigned last_line_read;
	const char *error_message;

	if(0 == cuesheet_filename)
		return true;

	if(lead_out_offset == 0) {
		flac__utils_printf(stderr, 1, "%s: ERROR cannot import cuesheet when the number of input samples to encode is unknown\n", inbasefilename);
		return false;
	}

	if(0 == (f = fopen(cuesheet_filename, "r"))) {
		flac__utils_printf(stderr, 1, "%s: ERROR opening cuesheet \"%s\" for reading: %s\n", inbasefilename, cuesheet_filename, strerror(errno));
		return false;
	}

	*cuesheet = grabbag__cuesheet_parse(f, &error_message, &last_line_read, is_cdda, lead_out_offset);

	fclose(f);

	if(0 == *cuesheet) {
		flac__utils_printf(stderr, 1, "%s: ERROR parsing cuesheet \"%s\" on line %u: %s\n", inbasefilename, cuesheet_filename, last_line_read, error_message);
		return false;
	}

	if(!FLAC__format_cuesheet_is_legal(&(*cuesheet)->data.cue_sheet, /*check_cd_da_subset=*/false, &error_message)) {
		flac__utils_printf(stderr, 1, "%s: ERROR parsing cuesheet \"%s\": %s\n", inbasefilename, cuesheet_filename, error_message);
		return false;
	}

	/* if we're expecting CDDA, warn about non-compliance */
	if(is_cdda && !FLAC__format_cuesheet_is_legal(&(*cuesheet)->data.cue_sheet, /*check_cd_da_subset=*/true, &error_message)) {
		flac__utils_printf(stderr, 1, "%s: WARNING cuesheet \"%s\" is not audio CD compliant: %s\n", inbasefilename, cuesheet_filename, error_message);
		(*cuesheet)->data.cue_sheet.is_cd = false;
	}

	return true;
}

void print_stats(const EncoderSession *encoder_session)
{
	const FLAC__uint64 samples_written = min(encoder_session->total_samples_to_encode, encoder_session->samples_written);
#if defined _MSC_VER || defined __MINGW32__
	/* with MSVC you have to spoon feed it the casting */
	const double progress = (double)(FLAC__int64)samples_written / (double)(FLAC__int64)encoder_session->total_samples_to_encode;
	const double ratio = (double)(FLAC__int64)encoder_session->bytes_written / ((double)(FLAC__int64)encoder_session->unencoded_size * min(1.0, progress));
#else
	const double progress = (double)samples_written / (double)encoder_session->total_samples_to_encode;
	const double ratio = (double)encoder_session->bytes_written / ((double)encoder_session->unencoded_size * min(1.0, progress));
#endif


	if(samples_written == encoder_session->total_samples_to_encode) {
		flac__utils_printf(stderr, 2, "\r%s:%s wrote %u bytes, ratio=%0.3f",
			encoder_session->inbasefilename,
			encoder_session->verify? " Verify OK," : "",
			(unsigned)encoder_session->bytes_written,
			ratio
		);
	}
	else {
		flac__utils_printf(stderr, 2, "\r%s: %u%% complete, ratio=%0.3f", encoder_session->inbasefilename, (unsigned)floor(progress * 100.0 + 0.5), ratio);
	}
}

void print_error_with_state(const EncoderSession *e, const char *message)
{
	const int ilen = strlen(e->inbasefilename) + 1;
	const char *state_string;

	flac__utils_printf(stderr, 1, "\n%s: %s\n", e->inbasefilename, message);

#ifdef FLAC__HAS_OGG
	if(e->use_ogg) {
		if(e->is_stdout) {
			state_string = OggFLAC__stream_encoder_get_resolved_state_string(e->encoder.ogg.stream);
		}
		else {
			state_string = OggFLAC__file_encoder_get_resolved_state_string(e->encoder.ogg.file);
		}
	}
	else
#endif
	if(e->is_stdout) {
		state_string = FLAC__stream_encoder_get_resolved_state_string(e->encoder.flac.stream);
	}
	else {
		state_string = FLAC__file_encoder_get_resolved_state_string(e->encoder.flac.file);
	}

	flac__utils_printf(stderr, 1, "%*s state = %s\n", ilen, "", state_string);

	/* print out some more info for some errors: */
	if(0 == strcmp(state_string, FLAC__StreamEncoderStateString[FLAC__STREAM_ENCODER_NOT_STREAMABLE])) {
		flac__utils_printf(stderr, 1,
			"\n"
			"The encoding parameters specified do not conform to the FLAC Subset and may not\n"
			"be streamable or playable in hardware devices.  Add --lax to the command-line\n"
			"options to encode with these parameters anyway.\n"
		);
	}
	else if(
		0 == strcmp(state_string, FLAC__FileEncoderStateString[FLAC__FILE_ENCODER_FATAL_ERROR_WHILE_WRITING])
#ifdef FLAC__HAS_OGG
		|| 0 == strcmp(state_string, OggFLAC__FileEncoderStateString[OggFLAC__FILE_ENCODER_FATAL_ERROR_WHILE_WRITING])
#endif
	) {
		flac__utils_printf(stderr, 1,
			"\n"
			"An error occurred while writing; the most common cause is that the disk is full.\n"
		);
	}
	else if(
		0 == strcmp(state_string, FLAC__FileEncoderStateString[FLAC__FILE_ENCODER_ERROR_OPENING_FILE])
#ifdef FLAC__HAS_OGG
		|| 0 == strcmp(state_string, OggFLAC__FileEncoderStateString[OggFLAC__FILE_ENCODER_ERROR_OPENING_FILE])
#endif
	) {
		flac__utils_printf(stderr, 1,
			"\n"
			"An error occurred opening the output file; it is likely that the output\n"
			"directory does not exist or is not writable, the output file already exists and\n"
			"is not writable, or the disk is full.\n"
		);
	}
}

void print_verify_error(EncoderSession *e)
{
	FLAC__uint64 absolute_sample;
	unsigned frame_number;
	unsigned channel;
	unsigned sample;
	FLAC__int32 expected;
	FLAC__int32 got;

#ifdef FLAC__HAS_OGG
	if(e->use_ogg) {
		if(e->is_stdout) {
			OggFLAC__stream_encoder_get_verify_decoder_error_stats(e->encoder.ogg.stream, &absolute_sample, &frame_number, &channel, &sample, &expected, &got);
		}
		else {
			OggFLAC__file_encoder_get_verify_decoder_error_stats(e->encoder.ogg.file, &absolute_sample, &frame_number, &channel, &sample, &expected, &got);
		}
	}
	else
#endif
	if(e->is_stdout) {
		FLAC__stream_encoder_get_verify_decoder_error_stats(e->encoder.flac.stream, &absolute_sample, &frame_number, &channel, &sample, &expected, &got);
	}
	else {
		FLAC__file_encoder_get_verify_decoder_error_stats(e->encoder.flac.file, &absolute_sample, &frame_number, &channel, &sample, &expected, &got);
	}

	flac__utils_printf(stderr, 1, "%s: ERROR: mismatch in decoded data, verify FAILED!\n", e->inbasefilename);
	flac__utils_printf(stderr, 1, "       Absolute sample=%u, frame=%u, channel=%u, sample=%u, expected %d, got %d\n", (unsigned)absolute_sample, frame_number, channel, sample, expected, got);
	flac__utils_printf(stderr, 1, "       In all known cases, verify errors are caused by hardware problems,\n");
	flac__utils_printf(stderr, 1, "       usually overclocking or bad RAM.  Delete %s\n", e->outfilename);
	flac__utils_printf(stderr, 1, "       and repeat the flac command exactly as before.  If it does not give a\n");
	flac__utils_printf(stderr, 1, "       verify error in the exact same place each time you try it, then there is\n");
	flac__utils_printf(stderr, 1, "       a problem with your hardware; please see the FAQ:\n");
	flac__utils_printf(stderr, 1, "           http://flac.sourceforge.net/faq.html#tools__hardware_prob\n");
	flac__utils_printf(stderr, 1, "       If it does fail in the exact same place every time, keep\n");
	flac__utils_printf(stderr, 1, "       %s and submit a bug report to:\n", e->outfilename);
	flac__utils_printf(stderr, 1, "           https://sourceforge.net/bugs/?func=addbug&group_id=13478\n");
	flac__utils_printf(stderr, 1, "       Make sure to upload the FLAC file and use the \"Monitor\" feature to\n");
	flac__utils_printf(stderr, 1, "       monitor the bug status.\n");
	flac__utils_printf(stderr, 1, "Verify FAILED!  Do not trust %s\n", e->outfilename);
}

FLAC__bool read_little_endian_uint16(FILE *f, FLAC__uint16 *val, FLAC__bool eof_ok, const char *fn)
{
	size_t bytes_read = fread(val, 1, 2, f);

	if(bytes_read == 0) {
		if(!eof_ok) {
			flac__utils_printf(stderr, 1, "%s: ERROR: unexpected EOF\n", fn);
			return false;
		}
		else
			return true;
	}
	else if(bytes_read < 2) {
		flac__utils_printf(stderr, 1, "%s: ERROR: unexpected EOF\n", fn);
		return false;
	}
	else {
		if(is_big_endian_host_) {
			FLAC__byte tmp, *b = (FLAC__byte*)val;
			tmp = b[1]; b[1] = b[0]; b[0] = tmp;
		}
		return true;
	}
}

FLAC__bool read_little_endian_uint32(FILE *f, FLAC__uint32 *val, FLAC__bool eof_ok, const char *fn)
{
	size_t bytes_read = fread(val, 1, 4, f);

	if(bytes_read == 0) {
		if(!eof_ok) {
			flac__utils_printf(stderr, 1, "%s: ERROR: unexpected EOF\n", fn);
			return false;
		}
		else
			return true;
	}
	else if(bytes_read < 4) {
		flac__utils_printf(stderr, 1, "%s: ERROR: unexpected EOF\n", fn);
		return false;
	}
	else {
		if(is_big_endian_host_) {
			FLAC__byte tmp, *b = (FLAC__byte*)val;
			tmp = b[3]; b[3] = b[0]; b[0] = tmp;
			tmp = b[2]; b[2] = b[1]; b[1] = tmp;
		}
		return true;
	}
}

FLAC__bool read_big_endian_uint16(FILE *f, FLAC__uint16 *val, FLAC__bool eof_ok, const char *fn)
{
	unsigned char buf[4];
	size_t bytes_read= fread(buf, 1, 2, f);

	if(bytes_read==0U && eof_ok)
		return true;
	else if(bytes_read<2U) {
		flac__utils_printf(stderr, 1, "%s: ERROR: unexpected EOF\n", fn);
		return false;
	}

	/* this is independent of host endianness */
	*val= (FLAC__uint16)(buf[0])<<8 | buf[1];

	return true;
}

FLAC__bool read_big_endian_uint32(FILE *f, FLAC__uint32 *val, FLAC__bool eof_ok, const char *fn)
{
	unsigned char buf[4];
	size_t bytes_read= fread(buf, 1, 4, f);

	if(bytes_read==0U && eof_ok)
		return true;
	else if(bytes_read<4U) {
		flac__utils_printf(stderr, 1, "%s: ERROR: unexpected EOF\n", fn);
		return false;
	}

	/* this is independent of host endianness */
	*val= (FLAC__uint32)(buf[0])<<24 | (FLAC__uint32)(buf[1])<<16 |
		(FLAC__uint32)(buf[2])<<8 | buf[3];

	return true;
}

FLAC__bool read_sane_extended(FILE *f, FLAC__uint32 *val, FLAC__bool eof_ok, const char *fn)
	/* Read an IEEE 754 80-bit (aka SANE) extended floating point value from 'f',
	 * convert it into an integral value and store in 'val'.  Return false if only
	 * between 1 and 9 bytes remain in 'f', if 0 bytes remain in 'f' and 'eof_ok' is
	 * false, or if the value is negative, between zero and one, or too large to be
	 * represented by 'val'; return true otherwise.
	 */
{
	unsigned int i;
	unsigned char buf[10];
	size_t bytes_read= fread(buf, 1U, 10U, f);
	FLAC__int16 e= ((FLAC__uint16)(buf[0])<<8 | (FLAC__uint16)(buf[1]))-0x3FFF;
	FLAC__int16 shift= 63-e;
	FLAC__uint64 p= 0U;

	if(bytes_read==0U && eof_ok)
		return true;
	else if(bytes_read<10U) {
		flac__utils_printf(stderr, 1, "%s: ERROR: unexpected EOF\n", fn);
		return false;
	}
	else if((buf[0]>>7)==1U || e<0 || e>63) {
		flac__utils_printf(stderr, 1, "%s: ERROR: invalid floating-point value\n", fn);
		return false;
	}

	for(i= 0U; i<8U; ++i)
		p|= (FLAC__uint64)(buf[i+2])<<(56U-i*8);
	*val= (FLAC__uint32)((p>>shift)+(p>>(shift-1) & 0x1));

	return true;
}

FLAC__bool fskip_ahead(FILE *f, FLAC__uint64 offset)
{
	static unsigned char dump[8192];

	while(offset > 0) {
		long need = (long)min(offset, LONG_MAX);
	   	if(fseeko(f, need, SEEK_CUR) < 0) {
			need = (long)min(offset, sizeof(dump));
			if((long)fread(dump, 1, need, f) < need)
				return false;
		}
		offset -= need;
	}
#if 0 /* pure non-fseek() version */
	while(offset > 0) {
		const long need = (long)min(offset, sizeof(dump));
		if(fread(dump, 1, need, f) < need)
			return false;
		offset -= need;
	}
#endif
	return true;
}
