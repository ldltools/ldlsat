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

set -eu -o pipefail
export LC_ALL=C

BINDIR=$(readlink -f `dirname $0`)
LDL2MSO=$BINDIR/ldl2mso
test -x $LDL2MSO || { echo "$LDL2MSO not found" > /dev/stderr; exit 1; } 
VERSION=$($LDL2MSO --version)

usage ()
{
cat <<EOF
ldlsat (v$VERSION): BDD-based SAT solver for Linear Dynamic Logic
usage: $(basename $0) <option>* <infile>?
options:
  --validity		check validity (without formula negation)
  -d			dump BDD
  -w			generate DFA
  -o <file>		output to <file>
EOF
exit 0
}

MONA=mona
MONAOPTS=

infile=/dev/stdin
outfile=/dev/stdout
verbose=0
opt_validity=0

while test $# -gt 0
do
    case $1 in
	-)  infile=/dev/stdin
	    ;;
	--val*)
	    opt_validity=1 ;;
	-[wntsidqefmu] | -o[012] | -g[wscd])
	    MONAOPTS="$MONAOPTS $1"
	    ;;

	-o | --output)
	    outfile=$2
	    shift ;;

	-h | --help)
	    usage
	    ;;
	-V | --version)
	    echo $VERSION
	    exit 0
	    ;;
	-v | --verbose)
	    verbose=1
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
#test -f "$outfile" && { echo "\"$outfile\" exists" > /dev/stderr; exit 1; }
test -f "$outfile" >&- 2>&- && { echo "\"$outfile\" exists" > /dev/stderr; exit 1; }
# note: without ">&-", rediction like: "ldlsat /dev/stdout > file" fails.
# cf. to: https://stackoverflow.com/questions/55203566

# --------------------
# RUN LDL2MSO
# --------------------
msofile=`tempfile -p ldlsat -s .mso`
test -f $msofile && rm -f $msofile
#test $verbose -eq 1 && echo -e ";; LDL2MSO:\t$infile -> $msofile"
${LDL2MSO} $infile -o $msofile || { echo ";; ${LDL2MSO} crashed" > /dev/stderr; rm -f $msofile; exit 1; }

# --------------------
# RUN MONA
# --------------------

# case: running mona with options specified
test ."$MONAOPTS" = . || { $MONA $MONAOPTS $msofile > $outfile; rm -f $msofile; exit 0; }

#
rsltfile=`tempfile -p ldlsat -s .out`
# dfa generation is needed only for checking validity
test ${opt_validity} -eq 0 && MONAOPTS="" || MONAOPTS="-w"
$MONA $MONAOPTS $msofile >| $rsltfile || { rm -f $rsltfile $msofile; exit 1; }
rm -f $msofile

# case: unsatisfiable
egrep -q '^Formula is unsatisfiable' $rsltfile \
    && { echo unsatisfiable > $outfile; rm -f $rsltfile; exit 0; }

# case satisfiable
test ${opt_validity} -eq 0 \
    && { echo satisfiable > $outfile; rm -f $rsltfile; exit 0; }

# case: valid (true)
# ** note: "validity" in LDL_f is slightly different from what people would ususaly suppose.
cat <<EOF | gawk -v verbose=$verbose -f /dev/stdin $rsltfile && { echo valid; rm -f $rsltfile; exit 0; }
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
echo satisfiable > $outfile

rm -f $rsltfile
exit 0
