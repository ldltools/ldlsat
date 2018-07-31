#! /bin/bash
# $Id: ldlsat.sh,v 1.1 2018/02/05 21:06:17 sato Exp sato $
#
# (C) Copyright IBM Corp. 2018.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

usage ()
{
    echo "usage: `basename $0` [<infile>]"
    echo
    echo "`basename $0` is a SAT solver for LDL"
    echo "`basename $0` reads a LDL formula φ from <infile>,"
    echo "examines if φ is satisfiable or not, and then returns"
    echo "either \"valid\" (¬φ is unsatisfiable), \"satisfiable\", or \"unsatisfiable\""
    echo
    exit 0
}

BINDIR=$(readlink -f `dirname $0`)
LDL2MSO=$BINDIR/ldl2mso
test -x $LDL2MSO || { echo "$LDL2MSO not found" > /dev/stderr; exit 1; } 

MONA=mona
MONAOPTS=

infile=/dev/stdin
verbose=0

while test $# -gt 0
do
    case $1 in
	-h | --help)
	    usage
	    ;;
	-v | --verbose)
	    verbose=1
	    ;;
	-[wntsidqefmu] | -o[012] | -g[wscd])
	    MONAOPTS="$MONAOPTS $1"
	    ;;
	-*)
	    echo "** unknown option \"$1\" detected"
	    exit 1
	    ;;
	*) infile=$1
    esac
    shift
done

test -e $infile || { echo "$infile not found" > /dev/stderr; exit 1; } 

# --------------------
# RUN LDL2MSO
# --------------------
msofile=`tempfile -s .mso`
test -f $msofile && rm -f $msofile
#test $verbose -eq 1 && echo -e ";; LDL2MSO:\t$infile -> $msofile"
${LDL2MSO} $infile > $msofile || { echo ";; ${LDL2MSO} crashed" > /dev/stderr; rm -f $msofile; exit 1; }

# --------------------
# RUN MONA
# --------------------

# case: just run mona and terminate
test $verbose -eq 0 -a ."$MONAOPTS" = . || { $MONA $MONAOPTS $msofile; rm -f $msofile; exit 0; }

outfile=`tempfile -s .out`
#test $verbose -eq 1 && echo -e ";; MONA:\t$msofile -> $outfile"
$MONA -w $msofile > $outfile || { rm -f $outfile; exit 1; }
rm -f $msofile

# case: unsatisfiable
egrep -q '^Formula is unsatisfiable' $outfile && { echo unsatisfiable; rm -f $outfile; exit 0; }

# case: valid (true)
# ** note: "validity" in LDL_f is slightly different from what people would ususaly suppose.
cat <<EOF | gawk -v verbose=$verbose -f /dev/stdin $outfile && { echo valid; rm -f $outfile; exit 0; }
/^Initial state:/ { if (\$NF != 0) exit (1); }
/^Accepting states:/ { if (\$NF != 2) exit (1); }
/^Rejecting states:/ { if (\$NF != 1) exit (1); }
/^Don't-care states:/ { if (\$NF != 0) exit (1); }
/^State 0: X* *-> state 1/ { next; }
/^State 1: X* *-> state 2/ { next; }
/^State 2: X* *-> state 2/ { next; }
/^State [0-9]+:.*-> state [0-9]+/ { exit (1); }
/^ANALYSIS/ { exit (0); }
EOF

# case: satisfiable
echo satisfiable

rm -f $outfile
exit 0
