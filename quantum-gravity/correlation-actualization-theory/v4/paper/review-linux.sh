#!/usr/bin/env bash
set -eu
cd "$(dirname "$0")"
cache=${CAT_LINUX_CACHE:-"$PWD/.review-cache/linux-runtime"}
python3 -B review_linux_env.py "$cache"
export PYTHONPATH="$cache/site" PYTHONNOUSERSITE=1 PYTHONDONTWRITEBYTECODE=1
export MPLCONFIGDIR="$cache/mpl" XDG_CACHE_HOME="$cache/xdg"
python3 -B review.py "$@"

