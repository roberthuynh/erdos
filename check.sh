#!/bin/bash
# Compatibility entrypoint: original #585 file/declaration arguments remain valid.
set -eu
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
exec bash "$ROOT/problems/585/check.sh" "$@"
