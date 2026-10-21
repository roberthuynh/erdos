#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p receipts
rm -f receipts/final-receipt.json
case "${1:-}" in
  prepare|hygiene|finalize)
    phase="--final-$1"
    ;;
  build|kernel)
    if [ "$#" -ne 2 ]; then echo "usage: check.sh $1 N" >&2; exit 2; fi
    phase="--final-$1-$2"
    ;;
  *)
    echo 'usage: check.sh prepare|build N|hygiene|kernel N|finalize' >&2
    exit 2
    ;;
esac
PYTHONDONTWRITEBYTECODE=1 exec python3 -B tools/verify_final_phased.py "$phase"
