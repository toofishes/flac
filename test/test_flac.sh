#!/bin/sh

#  FLAC - Free Lossless Audio Codec
#  Copyright (C) 2001,2002  Josh Coalson
#
#  This program is part of FLAC; you can redistribute it and/or
#  modify it under the terms of the GNU General Public License
#  as published by the Free Software Foundation; either version 2
#  of the License, or (at your option) any later version.
#
#  This program is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#  GNU General Public License for more details.
#
#  You should have received a copy of the GNU General Public License
#  along with this program; if not, write to the Free Software
#  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.

die ()
{
	echo $* 1>&2
	exit 1
}

LD_LIBRARY_PATH=../src/libFLAC/.libs:../obj/release/lib:../obj/debug/lib:$LD_LIBRARY_PATH
export LD_LIBRARY_PATH
PATH=../src/flac:../src/test_streams:../obj/release/bin:../obj/debug/bin:$PATH

flac --help 1>/dev/null 2>/dev/null || die "ERROR can't find flac executable"

run_flac ()
{
	if [ "$FLAC__VALGRIND" = yes ] ; then
		valgrind --leak-check=yes --show-reachable=yes --num-callers=10 --logfile-fd=4 flac $* 4>>valgrind.log
	else
		flac $*
	fi
}

echo "Checking for --ogg support in flac..."
if flac --ogg --silent --force-raw-format --endian=little --sign=signed --channels=1 --bps=8 --sample-rate=44100 -c $0 1>/dev/null 2>&1 ; then
	has_ogg=yes;
	echo "flac --ogg works"
else
	has_ogg=no;
	echo "flac --ogg doesn't work"
fi

############################################################################
# test --skip and --until
############################################################################

#
# first make some chopped-up files
#
echo "abcdefghijklmnopqrstuvwxyz1234567890ABCDEFGHIJKLMN" > master.raw
dddie="die ERROR: creating files for --skip/--until tests"
dd if=master.raw ibs=1 count=50 of=50c.raw 2>/dev/null || $dddie
dd if=master.raw ibs=1 skip=10 count=40 of=50c.skip10.raw 2>/dev/null || $dddie
dd if=master.raw ibs=1 skip=11 count=39 of=50c.skip11.raw 2>/dev/null || $dddie
dd if=master.raw ibs=1 count=40 of=50c.until40.raw 2>/dev/null || $dddie
dd if=master.raw ibs=1 count=39 of=50c.until39.raw 2>/dev/null || $dddie
dd if=master.raw ibs=1 skip=10 count=30 of=50c.skip10.until40.raw 2>/dev/null || $dddie
dd if=master.raw ibs=1 skip=10 count=29 of=50c.skip10.until39.raw 2>/dev/null || $dddie

eopt="--silent --verify --lax --force-raw-format --endian=big --sign=signed --sample-rate=10 --bps=8 --channels=1"
dopt="--silent --decode --force-raw-format --endian=big --sign=signed"

#
# test --skip when encoding
#

echo -n "testing --skip=# (encode)... "
run_flac $eopt --skip=10 -o z50c.skip10.flac 50c.raw || die "ERROR generating FLAC file"
run_flac $dopt -o z50c.skip10.raw z50c.skip10.flac || die "ERROR decoding FLAC file"
cmp 50c.skip10.raw z50c.skip10.raw || die "ERROR: file mismatch for --skip=10 (encode)"
rm -f z50c.skip10.flac z50c.skip10.raw
echo OK

echo -n "testing --skip=mm:ss (encode)... "
run_flac $eopt --skip=0:01 -o z50c.skip0:01.flac 50c.raw || die "ERROR generating FLAC file"
run_flac $dopt -o z50c.skip0:01.raw z50c.skip0:01.flac || die "ERROR decoding FLAC file"
cmp 50c.skip10.raw z50c.skip0:01.raw || die "ERROR: file mismatch for --skip=0:01 (encode)"
rm -f z50c.skip0:01.flac z50c.skip0:01.raw
echo OK

echo -n "testing --skip=mm:ss.sss (encode)... "
run_flac $eopt --skip=0:01.1001 -o z50c.skip0:01.1001.flac 50c.raw || die "ERROR generating FLAC file"
run_flac $dopt -o z50c.skip0:01.1001.raw z50c.skip0:01.1001.flac || die "ERROR decoding FLAC file"
cmp 50c.skip11.raw z50c.skip0:01.1001.raw || die "ERROR: file mismatch for --skip=0:01.1001 (encode)"
rm -f z50c.skip0:01.1001.flac z50c.skip0:01.1001.raw
echo OK

#
# test --skip when decoding
#

echo -n "testing --skip=# (decode)... "
run_flac $eopt -o z50c.flac 50c.raw || die "ERROR generating FLAC file"
run_flac $dopt --skip=10 -o z50c.skip10.raw z50c.flac || die "ERROR decoding FLAC file"
cmp 50c.skip10.raw z50c.skip10.raw || die "ERROR: file mismatch for --skip=10 (decode)"
rm -f z50c.skip10.raw
echo OK

echo -n "testing --skip=mm:ss (decode)... "
run_flac $dopt --skip=0:01 -o z50c.skip0:01.raw z50c.flac || die "ERROR decoding FLAC file"
cmp 50c.skip10.raw z50c.skip0:01.raw || die "ERROR: file mismatch for --skip=0:01 (decode)"
rm -f z50c.skip0:01.raw
echo OK

echo -n "testing --skip=mm:ss.sss (decode)... "
run_flac $dopt --skip=0:01.1001 -o z50c.skip0:01.1001.raw z50c.flac || die "ERROR decoding FLAC file"
cmp 50c.skip11.raw z50c.skip0:01.1001.raw || die "ERROR: file mismatch for --skip=0:01.1001 (decode)"
rm -f z50c.skip0:01.1001.raw
echo OK

rm -f z50c.flac

#
# test --until when encoding
#

echo -n "testing --until=# (encode)... "
run_flac $eopt --until=40 -o z50c.until40.flac 50c.raw || die "ERROR generating FLAC file"
run_flac $dopt -o z50c.until40.raw z50c.until40.flac || die "ERROR decoding FLAC file"
cmp 50c.until40.raw z50c.until40.raw || die "ERROR: file mismatch for --until=40 (encode)"
rm -f z50c.until40.flac z50c.until40.raw
echo OK

echo -n "testing --until=mm:ss (encode)... "
run_flac $eopt --until=0:04 -o z50c.until0:04.flac 50c.raw || die "ERROR generating FLAC file"
run_flac $dopt -o z50c.until0:04.raw z50c.until0:04.flac || die "ERROR decoding FLAC file"
cmp 50c.until40.raw z50c.until0:04.raw || die "ERROR: file mismatch for --until=0:04 (encode)"
rm -f z50c.until0:04.flac z50c.until0:04.raw
echo OK

echo -n "testing --until=mm:ss.sss (encode)... "
run_flac $eopt --until=0:03.9001 -o z50c.until0:03.9001.flac 50c.raw || die "ERROR generating FLAC file"
run_flac $dopt -o z50c.until0:03.9001.raw z50c.until0:03.9001.flac || die "ERROR decoding FLAC file"
cmp 50c.until39.raw z50c.until0:03.9001.raw || die "ERROR: file mismatch for --until=0:03.9001 (encode)"
rm -f z50c.until0:03.9001.flac z50c.until0:03.9001.raw
echo OK

echo -n "testing --until=-# (encode)... "
run_flac $eopt --until=-10 -o z50c.until-10.flac 50c.raw || die "ERROR generating FLAC file"
run_flac $dopt -o z50c.until-10.raw z50c.until-10.flac || die "ERROR decoding FLAC file"
cmp 50c.until40.raw z50c.until-10.raw || die "ERROR: file mismatch for --until=-10 (encode)"
rm -f z50c.until-10.flac z50c.until-10.raw
echo OK

echo -n "testing --until=-mm:ss (encode)... "
run_flac $eopt --until=-0:01 -o z50c.until-0:01.flac 50c.raw || die "ERROR generating FLAC file"
run_flac $dopt -o z50c.until-0:01.raw z50c.until-0:01.flac || die "ERROR decoding FLAC file"
cmp 50c.until40.raw z50c.until-0:01.raw || die "ERROR: file mismatch for --until=-0:01 (encode)"
rm -f z50c.until-0:01.flac z50c.until-0:01.raw
echo OK

echo -n "testing --until=-mm:ss.sss (encode)... "
run_flac $eopt --until=-0:01.1001 -o z50c.until-0:01.1001.flac 50c.raw || die "ERROR generating FLAC file"
run_flac $dopt -o z50c.until-0:01.1001.raw z50c.until-0:01.1001.flac || die "ERROR decoding FLAC file"
cmp 50c.until39.raw z50c.until-0:01.1001.raw || die "ERROR: file mismatch for --until=-0:01.1001 (encode)"
rm -f z50c.until-0:01.1001.flac z50c.until-0:01.1001.raw
echo OK

#
# test --until when decoding
#

run_flac $eopt -o z50c.flac 50c.raw || die "ERROR generating FLAC file"

echo -n "testing --until=# (decode)... "
run_flac $dopt --until=40 -o z50c.until40.raw z50c.flac || die "ERROR decoding FLAC file"
cmp 50c.until40.raw z50c.until40.raw || die "ERROR: file mismatch for --until=40 (decode)"
rm -f z50c.until40.raw
echo OK

echo -n "testing --until=mm:ss (decode)... "
run_flac $dopt --until=0:04 -o z50c.until0:04.raw z50c.flac || die "ERROR decoding FLAC file"
cmp 50c.until40.raw z50c.until0:04.raw || die "ERROR: file mismatch for --until=0:04 (decode)"
rm -f z50c.until0:04.raw
echo OK

echo -n "testing --until=mm:ss.sss (decode)... "
run_flac $dopt --until=0:03.9001 -o z50c.until0:03.9001.raw z50c.flac || die "ERROR decoding FLAC file"
cmp 50c.until39.raw z50c.until0:03.9001.raw || die "ERROR: file mismatch for --until=0:03.9001 (decode)"
rm -f z50c.until0:03.9001.raw
echo OK

echo -n "testing --until=-# (decode)... "
run_flac $dopt --until=-10 -o z50c.until-10.raw z50c.flac || die "ERROR decoding FLAC file"
cmp 50c.until40.raw z50c.until-10.raw || die "ERROR: file mismatch for --until=-10 (decode)"
rm -f z50c.until-10.raw
echo OK

echo -n "testing --until=-mm:ss (decode)... "
run_flac $dopt --until=-0:01 -o z50c.until-0:01.raw z50c.flac || die "ERROR decoding FLAC file"
cmp 50c.until40.raw z50c.until-0:01.raw || die "ERROR: file mismatch for --until=-0:01 (decode)"
rm -f z50c.until-0:01.raw
echo OK

echo -n "testing --until=-mm:ss.sss (decode)... "
run_flac $dopt --until=-0:01.1001 -o z50c.until-0:01.1001.raw z50c.flac || die "ERROR decoding FLAC file"
cmp 50c.until39.raw z50c.until-0:01.1001.raw || die "ERROR: file mismatch for --until=-0:01.1001 (decode)"
rm -f z50c.until-0:01.1001.raw
echo OK

rm -f z50c.flac

#
# test --skip and --until when encoding
#

echo -n "testing --skip=10 --until=# (encode)... "
run_flac $eopt --skip=10 --until=40 -o z50c.skip10.until40.flac 50c.raw || die "ERROR generating FLAC file"
run_flac $dopt -o z50c.skip10.until40.raw z50c.skip10.until40.flac || die "ERROR decoding FLAC file"
cmp 50c.skip10.until40.raw z50c.skip10.until40.raw || die "ERROR: file mismatch for --skip=10 --until=40 (encode)"
rm -f z50c.skip10.until40.flac z50c.skip10.until40.raw
echo OK

echo -n "testing --skip=10 --until=mm:ss (encode)... "
run_flac $eopt --skip=10 --until=0:04 -o z50c.skip10.until0:04.flac 50c.raw || die "ERROR generating FLAC file"
run_flac $dopt -o z50c.skip10.until0:04.raw z50c.skip10.until0:04.flac || die "ERROR decoding FLAC file"
cmp 50c.skip10.until40.raw z50c.skip10.until0:04.raw || die "ERROR: file mismatch for --skip=10 --until=0:04 (encode)"
rm -f z50c.skip10.until0:04.flac z50c.skip10.until0:04.raw
echo OK

echo -n "testing --skip=10 --until=mm:ss.sss (encode)... "
run_flac $eopt --skip=10 --until=0:03.9001 -o z50c.skip10.until0:03.9001.flac 50c.raw || die "ERROR generating FLAC file"
run_flac $dopt -o z50c.skip10.until0:03.9001.raw z50c.skip10.until0:03.9001.flac || die "ERROR decoding FLAC file"
cmp 50c.skip10.until39.raw z50c.skip10.until0:03.9001.raw || die "ERROR: file mismatch for --skip=10 --until=0:03.9001 (encode)"
rm -f z50c.skip10.until0:03.9001.flac z50c.skip10.until0:03.9001.raw
echo OK

echo -n "testing --skip=10 --until=+# (encode)... "
run_flac $eopt --skip=10 --until=+30 -o z50c.skip10.until+30.flac 50c.raw || die "ERROR generating FLAC file"
run_flac $dopt -o z50c.skip10.until+30.raw z50c.skip10.until+30.flac || die "ERROR decoding FLAC file"
cmp 50c.skip10.until40.raw z50c.skip10.until+30.raw || die "ERROR: file mismatch for --skip=10 --until=+30 (encode)"
rm -f z50c.skip10.until+30.flac z50c.skip10.until+30.raw
echo OK

echo -n "testing --skip=10 --until=+mm:ss (encode)... "
run_flac $eopt --skip=10 --until=+0:03 -o z50c.skip10.until+0:03.flac 50c.raw || die "ERROR generating FLAC file"
run_flac $dopt -o z50c.skip10.until+0:03.raw z50c.skip10.until+0:03.flac || die "ERROR decoding FLAC file"
cmp 50c.skip10.until40.raw z50c.skip10.until+0:03.raw || die "ERROR: file mismatch for --skip=10 --until=+0:03 (encode)"
rm -f z50c.skip10.until+0:03.flac z50c.skip10.until+0:03.raw
echo OK

echo -n "testing --skip=10 --until=+mm:ss.sss (encode)... "
run_flac $eopt --skip=10 --until=+0:02.9001 -o z50c.skip10.until+0:02.9001.flac 50c.raw || die "ERROR generating FLAC file"
run_flac $dopt -o z50c.skip10.until+0:02.9001.raw z50c.skip10.until+0:02.9001.flac || die "ERROR decoding FLAC file"
cmp 50c.skip10.until39.raw z50c.skip10.until+0:02.9001.raw || die "ERROR: file mismatch for --skip=10 --until=+0:02.9001 (encode)"
rm -f z50c.skip10.until+0:02.9001.flac z50c.skip10.until+0:02.9001.raw
echo OK

echo -n "testing --skip=10 --until=-# (encode)... "
run_flac $eopt --skip=10 --until=-10 -o z50c.skip10.until-10.flac 50c.raw || die "ERROR generating FLAC file"
run_flac $dopt -o z50c.skip10.until-10.raw z50c.skip10.until-10.flac || die "ERROR decoding FLAC file"
cmp 50c.skip10.until40.raw z50c.skip10.until-10.raw || die "ERROR: file mismatch for --skip=10 --until=-10 (encode)"
rm -f z50c.skip10.until-10.flac z50c.skip10.until-10.raw
echo OK

echo -n "testing --skip=10 --until=-mm:ss (encode)... "
run_flac $eopt --skip=10 --until=-0:01 -o z50c.skip10.until-0:01.flac 50c.raw || die "ERROR generating FLAC file"
run_flac $dopt -o z50c.skip10.until-0:01.raw z50c.skip10.until-0:01.flac || die "ERROR decoding FLAC file"
cmp 50c.skip10.until40.raw z50c.skip10.until-0:01.raw || die "ERROR: file mismatch for --skip=10 --until=-0:01 (encode)"
rm -f z50c.skip10.until-0:01.flac z50c.skip10.until-0:01.raw
echo OK

echo -n "testing --skip=10 --until=-mm:ss.sss (encode)... "
run_flac $eopt --skip=10 --until=-0:01.1001 -o z50c.skip10.until-0:01.1001.flac 50c.raw || die "ERROR generating FLAC file"
run_flac $dopt -o z50c.skip10.until-0:01.1001.raw z50c.skip10.until-0:01.1001.flac || die "ERROR decoding FLAC file"
cmp 50c.skip10.until39.raw z50c.skip10.until-0:01.1001.raw || die "ERROR: file mismatch for --skip=10 --until=-0:01.1001 (encode)"
rm -f z50c.skip10.until-0:01.1001.flac z50c.skip10.until-0:01.1001.raw
echo OK

#
# test --skip and --until when decoding
#

run_flac $eopt -o z50c.flac 50c.raw || die "ERROR generating FLAC file"

echo -n "testing --skip=10 --until=# (decode)... "
run_flac $dopt --skip=10 --until=40 -o z50c.skip10.until40.raw z50c.flac || die "ERROR decoding FLAC file"
cmp 50c.skip10.until40.raw z50c.skip10.until40.raw || die "ERROR: file mismatch for --skip=10 --until=40 (decode)"
rm -f z50c.skip10.until40.raw
echo OK

echo -n "testing --skip=10 --until=mm:ss (decode)... "
run_flac $dopt --skip=10 --until=0:04 -o z50c.skip10.until0:04.raw z50c.flac || die "ERROR decoding FLAC file"
cmp 50c.skip10.until40.raw z50c.skip10.until0:04.raw || die "ERROR: file mismatch for --skip=10 --until=0:04 (decode)"
rm -f z50c.skip10.until0:04.raw
echo OK

echo -n "testing --skip=10 --until=mm:ss.sss (decode)... "
run_flac $dopt --skip=10 --until=0:03.9001 -o z50c.skip10.until0:03.9001.raw z50c.flac || die "ERROR decoding FLAC file"
cmp 50c.skip10.until39.raw z50c.skip10.until0:03.9001.raw || die "ERROR: file mismatch for --skip=10 --until=0:03.9001 (decode)"
rm -f z50c.skip10.until0:03.9001.raw
echo OK

echo -n "testing --skip=10 --until=-# (decode)... "
run_flac $dopt --skip=10 --until=-10 -o z50c.skip10.until-10.raw z50c.flac || die "ERROR decoding FLAC file"
cmp 50c.skip10.until40.raw z50c.skip10.until-10.raw || die "ERROR: file mismatch for --skip=10 --until=-10 (decode)"
rm -f z50c.skip10.until-10.raw
echo OK

echo -n "testing --skip=10 --until=-mm:ss (decode)... "
run_flac $dopt --skip=10 --until=-0:01 -o z50c.skip10.until-0:01.raw z50c.flac || die "ERROR decoding FLAC file"
cmp 50c.skip10.until40.raw z50c.skip10.until-0:01.raw || die "ERROR: file mismatch for --skip=10 --until=-0:01 (decode)"
rm -f z50c.skip10.until-0:01.raw
echo OK

echo -n "testing --skip=10 --until=-mm:ss.sss (decode)... "
run_flac $dopt --skip=10 --until=-0:01.1001 -o z50c.skip10.until-0:01.1001.raw z50c.flac || die "ERROR decoding FLAC file"
cmp 50c.skip10.until39.raw z50c.skip10.until-0:01.1001.raw || die "ERROR: file mismatch for --skip=10 --until=-0:01.1001 (decode)"
rm -f z50c.skip10.until-0:01.1001.raw
echo OK

rm -f z50c.flac

#@@@@@@
exit 123

#
# multi-file tests
#

echo "Generating streams..."
if [ ! -f wacky1.wav ] ; then
	test_streams || die "ERROR during test_streams"
fi

echo "Generating multiple input files from noise..."
run_flac --verify --silent --force-raw-format --endian=big --sign=signed --sample-rate=44100 --bps=16 --channels=2 noise.raw || die "ERROR generating FLAC file"
run_flac --decode --silent noise.flac || die "ERROR generating WAVE file"
rm -f noise.flac
mv noise.wav file0.wav
cp file0.wav file1.wav
cp file1.wav file2.wav

test_multifile ()
{
	streamtype=$1
	sector_align=$2
	encode_options="$3"

	if [ $streamtype = ogg ] ; then
		suffix=ogg
		encode_options="$encode_options --ogg"
	else
		suffix=flac
	fi

	if [ $sector_align = sector_align ] ; then
		encode_options="$encode_options --sector-align"
	fi

	run_flac $encode_options file0.wav file1.wav file2.wav || die "ERROR"
	for n in 0 1 2 ; do
		mv file$n.$suffix file${n}x.$suffix
	done
	run_flac --decode file0x.$suffix file1x.$suffix file2x.$suffix || die "ERROR"
	if [ $sector_align != sector_align ] ; then
		for n in 0 1 2 ; do
			cmp file$n.wav file${n}x.wav || die "ERROR: file mismatch on file #$n"
		done
	fi
	for n in 0 1 2 ; do
		rm -f file${n}x.$suffix file${n}x.wav
	done
}

echo "Testing multiple files without verify..."
test_multifile flac no_sector_align ""

echo "Testing multiple files with verify..."
test_multifile flac no_sector_align "--verify"

echo "Testing multiple files with --sector-align, without verify..."
test_multifile flac sector_align ""

echo "Testing multiple files with --sector-align, with verify..."
test_multifile flac sector_align "--verify"

if [ $has_ogg = "yes" ] ; then
	echo "Testing multiple files with --ogg, without verify..."
	test_multifile ogg no_sector_align ""

	echo "Testing multiple files with --ogg, with verify..."
	test_multifile ogg no_sector_align "--verify"

	echo "Testing multiple files with --ogg and --sector-align, without verify..."
	test_multifile ogg sector_align ""

	echo "Testing multiple files with --ogg and --sector-align, with verify..."
	test_multifile sector_align ogg "--verify"

	echo "Testing multiple files with --ogg and --serial-number, with verify..."
	test_multifile ogg no_sector_align "--serial-number=321 --verify"
fi
