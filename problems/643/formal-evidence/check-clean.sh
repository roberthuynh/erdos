#!/bin/bash
# Hardened checker. Usage: ./check-clean.sh Openmath/Erdos643R3/File.lean Decl [Decl...]
# Same PASS criteria as check.sh (every compile exit 0, axiom probe exit 0, no sorry, axioms within
# {propext, Classical.choice, Quot.sound}, non-empty axiom report), plus:
#   pins     toolchain pin and Lean commit; every file of the toolchain's bin/ and lib/lean/ equal to
#            pins/toolchain.sha256 (made from the official release asset, see TRUST-BASE.md);
#            each package of standalone/lake-manifest.json at its pinned git revision
#            with clean tracked files; every module data file of those packages equal to pins/package-oleans.sha256
#            (made from a fresh official Mathlib cache download, see TRUST-BASE.md) with no extra file;
#   path     LEAN_PATH built from that explicit package list (no glob) and printed; no two entries provide the same
#            top-level module and none but the build directory provides Openmath;
#   fresh    a new empty build directory for every run (never .verified-build);
#   srcscan  nested-comment-safe scan of every source file of the closure (tools/srcscan.py);
#   hygiene  environment-based scan (tools/Hygiene.lean): no axiom/opaque/unsafe/partial/implemented_by/extern
#            constant in any Openmath module except three named Lean-generated recursion helpers from safe
#            PwCheck definitions; axioms collected by walking terms, and each Decl's own axiom set;
#   replay   leanchecker (kernel replay) of every closure module built in this run;
#   agree    the probe's axiom list equals the hygiene walk's for each Decl.
# Receipts: receipts-clean/<Module>_<decl>.log; source_sha256 is that of the file defining the Decl.
# check.sh is not modified. Every Lean command runs under timeout 240.
set -u -o pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
TC_PIN="leanprover/lean4:v4.33.1"
LEAN_COMMIT="819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
LEANBIN="${LEAN_TOOLCHAIN_BIN:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.1/bin}"
PKROOT="${PKROOT:-$HERE/standalone/.lake/packages}"
SRCROOT="${SRCROOT:-$HERE/source}"   # negative controls: SRCROOT=$HERE/controls
ALLOW='^(propext|Classical\.choice|Quot\.sound)$'
FILE="${1:?module file}"; shift
[ $# -ge 1 ] || { echo "usage: $0 FILE DECL [DECL...]"; exit 2; }
DECLS=("$@")
export PATH="$LEANBIN:$PATH"
unset LEAN_SRC_PATH
cd "$SRCROOT" || exit 2
LOGDIR="$(mktemp -d)"; FRESH="$(mktemp -d)"
trap 'rm -rf "$FRESH" "$LOGDIR"' EXIT
REC="${REC:-$HERE/receipts-clean}"; mkdir -p "$REC"
L="$LOGDIR/run.log"; : > "$L"
say() { echo "$*" | tee -a "$L"; }
say "== check-clean.sh $(date -u +%Y-%m-%dT%H:%M:%SZ) file=$FILE decls=${DECLS[*]}"

# ---- pins
PINS=ok
[ "$(cat "$HERE/source/lean-toolchain")" = "$TC_PIN" ] || { say "pin: source/lean-toolchain differs"; PINS=fail; }
[ "$(cat "$HERE/standalone/lean-toolchain")" = "$TC_PIN" ] || { say "pin: standalone/lean-toolchain differs"; PINS=fail; }
VER="$("$LEANBIN/lean" --version 2>&1)"; say "lean: $VER"
echo "$VER" | grep -q "commit $LEAN_COMMIT" || { say "pin: lean commit is not $LEAN_COMMIT"; PINS=fail; }
TP="$(timeout 240 python3 -I "$HERE/tools/toolchain_pins.py" verify "$LEANBIN/.." "$HERE/pins/toolchain.sha256" 2>&1)" || PINS=fail
say "$TP"
PKGS=$(python3 -I -c 'import json,sys; [print(p["name"], p["rev"]) for p in json.load(open(sys.argv[1]))["packages"]]' \
  "$HERE/standalone/lake-manifest.json")
LP="$FRESH"
while read -r name rev; do
  d="$PKROOT/$name"
  head="$(git -C "$d" rev-parse HEAD 2>/dev/null)"
  dirty="$(git -C "$d" status --porcelain --untracked-files=no 2>/dev/null | wc -l | tr -d ' ')"
  say "package $name rev=$head pinned=$rev dirty_tracked=$dirty"
  [ "$head" = "$rev" ] && [ "$dirty" = 0 ] || PINS=fail
  LP="$LP:$d/.lake/build/lib/lean"
done <<< "$PKGS"
OP="$(timeout 240 python3 -I "$HERE/tools/olean_pins.py" verify "$PKROOT" "$HERE/pins/package-oleans.sha256" 2>&1)" || PINS=fail
say "$OP"
export LEAN_PATH="$LP"
say "LEAN_PATH=$LEAN_PATH"
# no shadowing: top-level module names provided by each entry are disjoint; only the build dir provides Openmath
SHADOW=$(for e in ${LEAN_PATH//:/ }; do [ -d "$e" ] && ls "$e" | sed 's/\..*$//' | sort -u | sed "s|^|$e |"; done | \
  awk '{c[$2]++; w[$2]=w[$2]" "$1} END {for (k in c) if (c[k]>1) print k": "w[k]}')
[ -z "$SHADOW" ] || { say "pin: shadowed top-level modules: $SHADOW"; PINS=fail; }
ls "$PKROOT"/*/.lake/build/lib/lean 2>/dev/null | grep -qx 'Openmath' && { say "pin: a package provides Openmath"; PINS=fail; }
[ -z "$(ls -A "$FRESH")" ] || { say "fresh build dir not empty"; PINS=fail; }
say "pins=$PINS"

# ---- import closure (Openmath.* only, comments stripped), topological order
SEEN=" "; ORDER=""
visit() { local mod="$1"; case "$SEEN" in *" $mod "*) return;; esac; SEEN="$SEEN$mod "
  local src="${mod//.//}.lean"; [ -f "$src" ] || { say "missing source for $mod"; exit 2; }
  local dep; for dep in $(python3 -I "$HERE/tools/imports.py" "$src"); do visit "$dep"; done
  ORDER="$ORDER $mod"; }
MODNAME="${FILE%.lean}"; MODNAME="${MODNAME//\//.}"; visit "$MODNAME"
say "closure:$ORDER"
for mod in $ORDER; do say "source ${mod//.//}.lean sha256=$(shasum -a 256 "${mod//.//}.lean" | cut -c1-64)"; done

# ---- fresh build
BUILD=ok
for mod in $ORDER; do
  src="${mod//.//}.lean"; out="$FRESH/${mod//.//}.olean"; mkdir -p "$(dirname "$out")"
  t0=$(date +%s)
  if ! timeout 240 "$LEANBIN/lean" -o "$out" "$src" > "$LOGDIR/build.txt" 2>&1; then
    BUILD=fail; say "build FAIL $mod (rc, see log)"; tail -n 20 "$LOGDIR/build.txt" | tee -a "$L"; break; fi
  say "build ok $mod $(( $(date +%s) - t0 ))s warnings=$(grep -c 'warning' "$LOGDIR/build.txt")"
done

# ---- source scan of the closure
SRC=ok
FILES=""; for mod in $ORDER; do FILES="$FILES ${mod//.//}.lean"; done
python3 -I "$HERE/tools/srcscan.py" $FILES > "$LOGDIR/scan.txt" 2>&1 || SRC=fail
cat "$LOGDIR/scan.txt" >> "$L"
SORRIES=$(grep -o "'sorry': [0-9]*" "$LOGDIR/scan.txt" | awk -F': ' '{s+=$2} END {print s+0}')
say "srcscan=$SRC sorry_tokens=$SORRIES"

# ---- hygiene, replay, probe (only after a good build)
HYG=not_run; REPLAY=not_run
if [ "$BUILD" = ok ]; then
  OURS="$(echo $ORDER | tr ' ' ',')"
  if OURS="$OURS" timeout 240 "$LEANBIN/lean" --run "$HERE/tools/Hygiene.lean" "$MODNAME" "${DECLS[@]}" > "$LOGDIR/hyg.txt" 2>&1; then HYG=ok; else HYG=fail; fi
  cat "$LOGDIR/hyg.txt" >> "$L"
  if timeout 240 leanchecker $ORDER > "$LOGDIR/replay.txt" 2>&1; then REPLAY=ok; else REPLAY=fail; fi
  NREP=$(find "$FRESH" -name '*.olean' | wc -l | tr -d ' ')
  say "replay=$REPLAY modules_in_build=$NREP"; cat "$LOGDIR/replay.txt" | head -n 20 >> "$L"
fi

# ---- per declaration
FINAL=0
for DECL in "${DECLS[@]}"; do
  R="$LOGDIR/decl.log"; cp "$L" "$R"
  AXIOMS="n/a"; BAD=""; PROBE=not_run; AGREE=n/a
  if [ "$BUILD" = ok ]; then
    if OUT=$(printf 'import %s\n#print axioms %s\n' "$MODNAME" "$DECL" | timeout 240 "$LEANBIN/lean" --stdin 2>&1); then PROBE=ok; else PROBE=fail; fi
    echo "== axioms (probe)" >> "$R"; echo "$OUT" >> "$R"
    FLAT=$(echo "$OUT" | tr '\n' ' ')
    AXIOMS=$(echo "$FLAT" | sed -n 's/.*depends on axioms: \[\([^]]*\)\].*/\1/p' | tr -d ' ')
    if [ -z "$AXIOMS" ] && echo "$FLAT" | grep -q "does not depend on any axioms"; then AXIOMS="none"; fi
    for a in $(echo "$AXIOMS" | tr ',' ' '); do [ "$a" = none ] && continue; echo "$a" | grep -qE "$ALLOW" || BAD="$BAD $a"; done
    HL=$(grep "^DECL $DECL " "$LOGDIR/hyg.txt" | head -1)
    HAX=$(echo "$HL" | sed -n 's/.*axioms=\[\([^]]*\)\].*/\1/p')
    PS=$(echo "$AXIOMS" | tr ',' '\n' | grep -v '^none$' | sort | tr '\n' ',')
    HS=$(echo "$HAX" | tr ',' '\n' | grep -v '^$' | sort | tr '\n' ',')
    if [ -n "$HL" ] && [ "$PS" = "$HS" ]; then AGREE=ok; else AGREE=fail; fi
    DMOD=$(echo "$HL" | sed -n 's/.* module=\([^ ]*\) .*/\1/p')
  fi
  DSRC="${DMOD:-$MODNAME}"; DSRC="${DSRC//.//}.lean"
  DSHA=$( [ -f "$DSRC" ] && shasum -a 256 "$DSRC" | cut -c1-64 || echo n/a)
  VERDICT=FAIL
  if [ "$BUILD" = ok ] && [ "$PROBE" = ok ] && [ "$SORRIES" = 0 ] && [ -z "$BAD" ] && [ "$AXIOMS" != "n/a" ] && \
     [ -n "$AXIOMS" ] && [ "$PINS" = ok ] && [ "$SRC" = ok ] && [ "$HYG" = ok ] && [ "$REPLAY" = ok ] && \
     [ "$AGREE" = ok ]; then VERDICT=PASS; fi
  [ "$VERDICT" = PASS ] || FINAL=1
  LINE="RESULT: $VERDICT build=$BUILD probe=$PROBE sorry=$SORRIES axioms=[${AXIOMS}] disallowed=[${BAD# }] pins=$PINS srcscan=$SRC hygiene=$HYG replay=$REPLAY agree=$AGREE decl_module=${DMOD:-n/a} source_sha256=$DSHA target_sha256=$(shasum -a 256 "$FILE" | cut -c1-64)"
  echo "$LINE" >> "$R"; echo "$LINE"
  M="${MODNAME##*.}"; cp "$R" "$REC/${M}_${DECL##*.}.log"
done
exit $FINAL
