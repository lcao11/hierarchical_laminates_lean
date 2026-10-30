# Hierarchical laminates in Lean

Formal proofs in Lean 4 for periodic composites and energy relaxation in two spatial dimensions.

## Results

- **[Composite counterexample](HierarchicalLaminates/Statements/Composite.lean):** For every number $m\ge16$ of potential components, one pair of positive-definite constituents admits, at each prescribed phase fraction $0<\theta<1$, a periodic two-phase effective tensor outside the closure of all finite hierarchical laminates.
- **[Two-well energy gap](HierarchicalLaminates/Statements/TwoWell.lean):** The minimum of two positive-definite homogeneous quadratic forms on $\mathbb R^{2\times32}$ has a quasiconvex envelope strictly below its rank-one convex envelope at a mean gradient.

Read [Statements](docs/Statements.md) for the definitions and precise scope, and [ProofGuide](docs/ProofGuide.md) for a route through the proofs.

## Companion reading

- **[Research progress report](docs/companion/research-progress-report.pdf):** The ideas and approaches leading to the counterexample.
- **[Proof exercises](docs/companion/proof-exercises.pdf):** 178 guided steps through the construction in twelve modules.
- **[Worked answers](docs/companion/worked-answers.pdf):** Solutions with matching step numbers and each question included.

See the [companion reading guide](docs/companion/README.md) for an overview and suggested reading order.

## Build and verify

Install the pinned compiler and dependencies using [SETUP.md](SETUP.md), then run from the repository root:

```sh
bin/lake build HierarchicalLaminates
python3 verify.py
```

Use `python3 verify.py --clean` for a clean project rebuild. Successful verification produces [certificate.json](verification/certificate.json). [Verification](docs/Verification.md) explains the checks and how to interpret the result.

## Use in Lean

```lean
import HierarchicalLaminates
```

## Related manuscript

Lianghao Cao. *[Hierarchical Laminates Cannot Reproduce All Effective Properties of Planar Two-Phase Composites: A Counterexample with a 16-Component Potential](https://arxiv.org/abs/2610.37899)*. arXiv preprint, 2026. [DOI: 10.48550/arXiv.2610.37899](https://doi.org/10.48550/arXiv.2610.37899). [BibTeX](CITATION.bib).

## License

Licensed under the [Apache License 2.0](LICENSE).
