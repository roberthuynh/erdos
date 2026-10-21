#!/bin/bash
# Optional: materialize the pinned dependencies of lake-manifest.json with shallow fetches (one short network call per
# package) instead of letting Lake clone the full histories. Lake then finds each package at its pinned revision and
# uses it as is. Run from this directory: ./prefetch.sh. Needs git, python3,
# and GNU timeout on PATH (coreutils gnubin on macOS); no absolute paths.
set -eu -o pipefail
cd "$(dirname "$0")"
python3 - <<'PY' > .prefetch-list
import json
for p in json.load(open('lake-manifest.json'))['packages']:
    print(p['name'], p['url'], p['rev'])
PY
mkdir -p .lake/packages
while read -r name url rev; do
  d=".lake/packages/$name"
  if [ -d "$d/.git" ] && [ "$(git -C "$d" rev-parse HEAD 2>/dev/null)" = "$rev" ]; then echo "$name: already at $rev"; continue; fi
  rm -rf "$d"; mkdir -p "$d"
  git -C "$d" init -q
  git -C "$d" remote add origin "$url"
  timeout 240 git -C "$d" fetch -q --depth 1 origin "$rev"
  git -C "$d" checkout -q FETCH_HEAD
  [ "$(git -C "$d" rev-parse HEAD)" = "$rev" ] || { echo "$name: revision mismatch"; exit 1; }
  echo "$name: fetched $rev"
done < .prefetch-list
rm -f .prefetch-list
