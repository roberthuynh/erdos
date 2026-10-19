# Pinned Lean trust base

The standalone project pins Lean 4.33.1 and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. Its `lake-manifest.json` pins the transitive packages. `pins/package-oleans.sha256` records the 26,080 module-data files in those packages; `pins/toolchain.sha256` records 14,928 files under the Lean release's `bin/` and `lib/lean/`. `check-clean.sh` checks these pins, a fresh local build, source hygiene, allowed axioms, and kernel replay of the local modules before reporting PASS.

The package cache pins were prepared by comparing 43,470 package build files with a fresh official Mathlib cache download; the comparison found no differences. The toolchain pins were prepared from the official Lean 4.33.1 `darwin_aarch64` release archive, whose SHA-256 was recorded as `88c45aad985b5d2a8d925fe10bd1296bd35f66f408480ab182d3facccd065a9d`; all 17,466 release files matched the local installed toolchain in that audit. These provenance claims describe the recorded preparation. A recipient can independently fetch the pinned dependencies and release, reproduce the hashes, and rerun the checker.

The checker does not replay all of Mathlib in one fresh kernel process. It verifies the pinned official package bytes and replays the local modules. The Lean release and Mathlib's official build remain part of the trust base.
