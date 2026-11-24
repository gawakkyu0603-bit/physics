#!/usr/bin/env bash
# Run in this archive from any current directory. All outputs stay beside the source.
set -eu
cd "$(dirname "$0")"
for job in "$@"; do
    case "$job" in main|supplement) ;; *) echo "Use main or supplement" >&2; exit 2;; esac
done
if [ "$#" -eq 0 ]; then set -- main supplement; fi
export SOURCE_DATE_EPOCH=1795564800
export FORCE_SOURCE_DATE=1
export TZ=UTC
for job in "$@"; do
    for pass in 1 2 3; do
        pdflatex -interaction=batchmode -halt-on-error -file-line-error "$job.tex" > /dev/null || { tail -45 "$job.log" >&2; exit 1; }
    done
    if grep -Eq 'undefined references|Citation .* undefined|Reference .* undefined|multiply defined' "$job.log"; then
        echo "Unresolved reference in $job.log" >&2; exit 1
    fi
    pdfinfo "$job.pdf" | grep -E 'Pages:|Page size:'
done

