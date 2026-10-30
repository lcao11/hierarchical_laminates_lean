# Setup and reproduction

Run the commands below from the repository root. The project uses **Lean 4.36.0-rc1** and **mathlib 36a503d4c77bc214db328ed80a0f865d9ee359ba**. [dependency-lock.json](dependency-lock.json) and `lake-manifest.json` specify the dependency revisions and archive checksums.

## macOS arm64

Requirements: Python 3.12 or newer, Git, curl and a tar implementation that reads `.tar.zst` archives.

```sh
python3 scripts/bootstrap.py --cache
python3 verify.py --clean
```

Bootstrap installs the compiler in `.tools/` and dependency sources in `.lake/`. The `--cache` option downloads compiled mathlib imports. The initial installation requires network access.

For an existing cached installation, use the offline check:

```sh
python3 scripts/bootstrap.py --offline
python3 verify.py
```

## Other platforms with elan and Lake

Install elan and put its tools on `PATH`. Python 3.12 or newer, Git and curl are also required. For a fresh installation:

```sh
elan toolchain install leanprover/lean4:v4.36.0-rc1
mkdir -p .lake/packages
git clone https://github.com/leanprover-community/mathlib4 .lake/packages/mathlib
git -C .lake/packages/mathlib checkout 36a503d4c77bc214db328ed80a0f865d9ee359ba
python3 scripts/fetch_dependencies.py
python3 scripts/materialize_dependencies.py
bin/lake exe cache get
python3 verify.py --clean
```

The source helpers install the locked supporting packages. The environment checker verifies the compiler version and dependency sources against the lock.

## Build and verification commands

`bin/lake` uses the isolated runtime when installed and otherwise uses Lake on `PATH`. Build the public library with:

```sh
bin/lake build HierarchicalLaminates
```

Run `python3 verify.py` to build every proof module and check axioms, required proof dependencies and snapshot approvals. Add `--clean` to rebuild project proofs while reusing the installed dependencies.

For individual tooling checks:

```sh
python3 scripts/check_setup.py
python3 tests/test_verification_gate.py
```

Build and audit logs are written under `verification/logs/`. See [Verification](docs/Verification.md) for output records and exit codes.
