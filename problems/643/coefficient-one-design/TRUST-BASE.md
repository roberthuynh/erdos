# Binary identities and reproduction scope

`lean-toolchain` pins Lean 4.33.1. The supplied toolchain manifest was recorded
from the official `lean-4.33.1-darwin_aarch64.tar.zst` release asset, whose recorded
SHA-256 is `88c45aad985b5d2a8d925fe10bd1296bd35f66f408480ab182d3facccd065a9d`.
Its verifier covers every file or symbolic link under `bin/` and `lib/lean/`.

The supplied dependency manifest records all `.olean`, `.olean.server` and
`.olean.private` files in the official Mathlib cache used in the original
verification environment, for the revisions in `lake-manifest.json`.
The checker also verifies every dependency's Git HEAD and tracked cleanliness.
The root and `standalone/` package manifests must match exactly.

These manifests preserve previously recorded binary identities; copying them
is not a new provenance audit or a successful fresh installation. The setup
command fetches dependencies according to the pinned Lake manifest. A cache
download can have a different inventory or platform identity and fail strict
pin verification. Such a failure must be resolved through an independently
reviewed dependency/trust-base change, never by treating freshly generated pins
as proof of their own provenance or skipping the strict pin gate.

The verifier performs kernel replay independently of ordinary compilation.
A receipt applies only to the exact sources, checker inputs, dependency
identities, build products and logs it hashes. The portable path resolution
does not broaden a receipt's platform or source scope.
