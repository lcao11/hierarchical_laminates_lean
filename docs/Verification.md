# Verification

After [setup](../SETUP.md), run:

```sh
python3 verify.py
```

Use `python3 verify.py --clean` to rebuild project proofs while reusing the installed dependencies.

## Checks

A successful run checks that:

1. Imports resolve within the project and the pinned Lean/mathlib environment.
2. The verification tests pass, and the compiler and dependency sources match the lock.
3. The public aggregate and every proof module compile.
4. The transitive axioms of every project theorem belong to `propext`, `Classical.choice` and `Quot.sound`. This audit includes private helpers and declarations outside the main namespace.
5. The principal and supporting declarations use the required proof dependencies.
6. Source and configuration hashes stay stable during the run.
7. The mathematical, statement and code review receipts approve the same snapshot.

[verification_gate.py](../scripts/verification_gate.py) lists the required declarations and dependencies. [Statements](Statements.md) describes their mathematical content and assumptions.

## Output records

| Record | Contents |
| --- | --- |
| [result.json](../verification/result.json) | Check outcomes, environment, audited theorem counts and axioms, required declarations, and file hashes. |
| [certificate.json](../verification/certificate.json) | The accepted snapshot, checked declarations, axioms and review status. |
| [diagnostics.json](../verification/diagnostics.json) | Findings from the run and certificate status. |
| [Review receipts](../verification/reviews/) | Agent-assisted assessments of the mathematics, formal statements and verification tools. |

The certificate is an unsigned JSON verification record. Its `source_sha256` and `configuration_sha256` maps identify the checked files, and `dependency_lock_sha256` identifies the dependency lock. `clean_rebuild` records whether the run used `--clean`. `issued_utc` is the run's recorded start time.

The verifier writes a certificate when every check passes. Failed or unfinished runs remove it. Build logs, the generated Lean audit and proof-dependency graphs are available under `verification/logs/`.

## Snapshot approvals

Each review receipt records `approved: true` and the same five snapshot fields as the verification result: `main_targets`, `supporting_targets`, `source_sha256`, `configuration_sha256` and `dependency_lock_sha256`. Configuration covers the public aggregate, documentation, setup and verification tools. Changing a covered file requires approval of the resulting snapshot.

## Exit codes

| Code | Meaning |
| --- | --- |
| `0` | All checks passed and a certificate was issued. |
| `2` | Proof checks passed; matching review approvals are needed. |
| `1` | A source, environment, test, import, build, axiom, dependency or stability check failed. |

For a failed run, inspect `diagnostics.json` and the corresponding log in `verification/logs/`.
