#!/usr/bin/env bash

set -o errexit -o noclobber -o nounset -o pipefail

base=$(dirname "$0")
base=$(realpath "$base")
AUTOGRADER_EXE="${AUTOGRADER_EXE:-$base/../.lake/build/bin/autograder}"

usage() {
  printf "Usage: %s --assignment PATH_TO_ASSIGNMENT_PROJECT --submission PATH_TO_SUBMISSION_FILE\n\nSee README.md for instructions.\n" $0 >&2
  exit 2
}

opts=$(getopt \
  --longoptions assignment:,submission:,help \
  --name grade.sh \
  --options "" \
  -- "$@"
)
if [ "$?" != "0" ]; then
  usage
fi

eval set -- "$opts"

assignment=
submission=

while :
do
  case "$1" in
    --assignment)
      assignment=$2
      shift 2
      ;;

    --submission)
      submission=$2
      shift 2
      ;;

    --help)
      usage
      shift
      ;;

    # -- means the end of the arguments; drop this, and break out of the while loop
    --) shift; break ;;

    *)
      echo "Unexpected option: $1 - this should not happen."
      usage
      ;;
  esac
done

if [[ "$assignment" == "" || "$submission" == "" ]]; then
  echo "missing --assignment or --submission" >&2
  exit 2
fi

TMPDIR=$(mktemp -d -t autograder-XXXXXXXXXX)

echo "Copying $assignment to $TMPDIR"
cp -r "$assignment/." "$TMPDIR"

echo "Copying $submission to $TMPDIR/Submission.lean"
cp "$submission" "$TMPDIR/Submission.lean"

echo "Appending $TMPDIR/lakefile.toml"
cat <<'EOF' >> $TMPDIR/lakefile.toml


[[lean_lib]]
name = "Submission"
EOF

pushd "$TMPDIR"

echo "Running 'lake build'"
lake build

echo "Running 'lake build Submission'"
lake build Submission

echo "Running 'lake env "$AUTOGRADER_EXE" LF.Basics Submission'"
lake env "$AUTOGRADER_EXE" LF.Basics Submission
