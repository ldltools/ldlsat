#! /bin/bash
# $Id: ldlmc.sh,v 1.1 2018/02/05 21:06:17 sato Exp sato $
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
    echo "usage: `basename $0` -m <model_file> [<infile>]"
    echo
    echo "`basename $0` is a model-checker for LDL"
    echo "`basename $0` reads a LDL model M (from <model_file>) and a LDL formula φ (from <infile>),"
    echo "examines if M ⊨ φ (i.e., ⊨ M → φ) holds or not, and then returns"
    echo "either \"claim holds\" (M ⊨ φ holds) or \"claim does not hold\""
    echo
    exit 0
}

LDL2MSO=ldl2mso
BINDIR=$(readlink -f `dirname $0`)
LDLSAT=$BINDIR/ldlsat
LDLSATOPTS=
test -x $LDLSAT || { echo "$LDLSAT not found" > /dev/stderr; exit 1; } 

modelfile=
infile=/dev/stdin
reachability=0
verbose=0

silent=0
while test $# -gt 0
do
    case $1 in
	-m | --model)
	    modelfile=$2
	    shift ;;
	-r | --reachability)
	    reachability=1
	    ;;
	-h | --help)
	    usage
	    exit 0
	    ;;
	-v | --verbose)
	    verbose=1
	    ;;
	--silent)
	    silent=1
	    ;;
	-*)
	    LDLSATOPTS="$LDLSATOPTS $1"
	    ;;
	*) infile=$1
    esac
    shift
done

test .$modelfile = . && { usage; exit 0; }
test -e $modelfile || { echo "$modelfile does not exit" > /dev/stderr; exit 1; }
test -e $infile || { echo "$infile does not exit" > /dev/stderr; exit 1; }

# --------------------------------------------------------------------------------
# mc (modelfile, infile)
# --------------------------------------------------------------------------------
mc ()
{

local modelfile=$1
local infile=$2
test -e $modelfile -a -e $infile || { echo "** error in mc"; exit 1; }

# LDLGEN (model, input)
# returns: model ⊨ input (as a single LDL formula)
ldlfile=`tempfile -s .ldl`
cat <<EOF > ${ldlfile} || { echo ";; LDLGEN failed" > /dev/stderr; rm -f $ldlfile; exit 1; }
(`cat $modelfile | ${LDL2MSO} --parse-only -t ldl`)
->
(`cat $infile | ${LDL2MSO} --parse-only -t ldl`)
EOF

# LDLSAT
satoutfile=`tempfile -s .out`
$LDLSAT $LDLSATOPTS $ldlfile > $satoutfile || { echo "** $LDLSAT crashed" > /dev/stderr; rm -f $ldlfile $satoutfile; exit 1; }

success=0
test "`head -c 5 $satoutfile`" = "valid" && success=1
rm -f $ldlfile $satoutfile

# silent
if test $silent -eq 1; then test $success -eq 1 && exit 0 || exit 1; fi

test $success -eq 1 && echo "claim holds" || echo "claim does not hold"
exit 0

}

# --------------------------------------------------------------------------------
# ra (modelfile, infile)
# --------------------------------------------------------------------------------
ra ()
{
local modelfile=$1
local infile=$2
test -e $modelfile -a -e $infile || { echo "** error in ra"; exit 1; }

# LDLSAT
satoutfile=`tempfile -s .out`
cat <<EOF | $LDLSAT $LDLSATOPTS > $satoutfile || { echo "** $LDLSAT crashed" > /dev/stderr; rm -f $satoutfile; exit 1; }
(`cat $modelfile`)
&
(`cat $infile`)
EOF

success=0
test "`head -c 11 $satoutfile`" = "satisfiable" && success=1
rm -f $satoutfile

test $success -eq 1 && echo reachable || echo unreachable
exit 0
}

# --------------------------------------------------------------------------------
# main
# --------------------------------------------------------------------------------

if test $reachability -eq 1
then ra $modelfile $infile
else mc $modelfile $infile
fi

true
