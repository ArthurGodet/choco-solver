#!/bin/sh

NB_NODES=1
TIME_LIMIT=500
MEM_LIMIT=500
DIR=./
TDIR=./
SEED=0
JAR_NAME=choco-parsers.jar
CHOCO_JAR=${DIR}/${JAR_NAME}
usage="\

Usage: json_choco.sh [<options>] [<file>]

    Parse and solve <file> using Choco.

OPTIONS:

    -h, --help
        Display this message.

    -dir <s>
        Stands for the directory where the uploaded files reside.
        The default is ${DIR}.

    -tl <n>
        Stands for the maximum CPU time given to solver (in seconds).
        The default is ${TIME_LIMIT}.

    -p  <n>
        Stands for the number of processing units allocated to the solver.
        The default is ${NB_NODES}.

    -jar <j>
        Override the jar file.  (The default is $CHOCO_JAR.)

    --jargs <args>
		Override default java argument (\"-Xss64m -Xms64m -Xmx4096m -server\")

EXAMPLES:

	Basic command to solve a fzn model with choco:
	$> ./json-exec.sh alpha.json


	Additionnal arguments:
	$> json_choco.sh --jargs \"-Xmx128m\" -tl 100 ./choco-parsers.jar ./alpha.json

"

if test $# -eq 0
then
    echo "%% No JSON file found"
    exit 1
fi

while test $# -gt 0
do
    case "$1" in

        -h|--help)
            echo "$usage"
            exit 0
        ;;

        -dir)
            DIR="$2"
            shift
        ;;

        -tl)
            TIME_LIMIT="$2"
            shift
        ;;

        -p)
            NB_NODES="$2"
            shift
        ;;

        -jar)
            CHOCO_JAR="$2"
            shift
        ;;

    	--jargs)
            JAVA_ARGS="$2"
            shift
        ;;

        -*)
            echo "$0: unknown option \`$1'" 1>&2
            echo "$usage" 1>&2
            exit 2
        ;;

        *)
           break
        ;;

    esac
    shift
done

FILE="$1"
ARGS=" -tl '${TIME_LIMIT}s' -p $NB_NODES"

CMD="java -server -cp .:${CHOCO_JAR} org.chocosolver.parser.json.ChocoJSON \"${FILE}\" ${ARGS}"

echo "c $CMD"
eval ${CMD}

