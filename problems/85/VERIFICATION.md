# Verification boundary

This package is written mathematics. There is no Lean declaration or applicable theorem-oracle RESULT: PASS for its main theorem. Older Lean checks do not apply. No human mathematician has reviewed this theorem.

The frozen research proof received a separate AI adversarial audit on 16 October 2026. That audit reported no mandatory correction; its original SHA256 is `8ef8bb0af8a1d6c69cb77857864dffd97c16b8fd833cf07a9dbe52fccc655ed3`. A separate utility/source review assessed scope. Those records are historical AI evidence, not formal proof or human endorsement. Private release reviews record their own exact bytes and limits separately.

## Reproduce package checks

From the collection root, run the two commands in [README.md](README.md#verification). Both modes validate this package's frozen document hashes and local links. Full mode also runs negative controls for altered documents, broken or escaping links, unlisted files, symlinks and unsafe manifest paths in temporary copies. Fragment-only links, repeated headings and headings inside code fences have regression coverage. No mathematics is executed. Python 3.10 or later and its standard library suffice; no network access, solver, CAS or Lean environment is required.

`DOCUMENTS: PASS` means those checks passed. It does not mean the theorem is proved by a machine. The checker validates document identities against `document-hashes.json`; a changed document requires deliberate review and a new hash manifest. The collection's metadata, protected prose and explicit export allowlist are checked separately by its existing tools.

Written correctness, statement fidelity, formal verification, priority and human mathematical review remain distinct judgments. Any timeout is UNKNOWN. The private release packet retains exact commands, output and candidate digest.
