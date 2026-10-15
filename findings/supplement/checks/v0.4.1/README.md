# v0.4.1 verification

The machine-readable `verification.json` binds the configured source closure, dependency pins and checking tools to this correction release. It records actual build, type/axiom, oracle, replay and tooling outcomes. Dependency caches were reused. No complete census or full finite-certificate stream replay is claimed.

Run the commands in the root README to reproduce the formal checks. `scripts/replay_modules.py` defaults to every configured module and stops on any failure.
