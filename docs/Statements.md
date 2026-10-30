# Formal statements

The public import [HierarchicalLaminates.lean](../HierarchicalLaminates.lean) exposes the results corresponding to Theorems 1.1 and 6.1 of the manuscript ([arXiv:2610.37899v1](https://arxiv.org/abs/2610.37899v1)). Gradients use spatial-first indexing: $\mathbb R^{2\times m}$ means two spatial variables and $m$ scalar potentials. Tensors act on this full gradient space, and `quadraticEnergy A F` is the pairing $F\cdot AF$; no factor of $1/2$ is included.

## Theorem 1.1: periodic two-phase materials

[HierarchicalLaminates.composite_counterexample](../HierarchicalLaminates/Statements/Composite.lean) states that for every integer $m\ge16$ there are symmetric positive-definite tensors $L_0,L_1$ such that, for every $0<\theta<1$,

$$
G^{\mathrm L}_{\theta}(L_0,L_1)\subsetneq G_{\theta}(L_0,L_1).
$$

The same two constituents work for every prescribed phase fraction $0<\theta<1$. The theorem also supplies a periodic binary coefficient at fraction $\theta$ whose effective tensor lies outside the closure of **all** finite hierarchical laminates, even when the overall fractions in an approximating sequence vary.

The closure and witness definitions are:

- `genericGClosure L₀ L₁ θ` is the closure of effective tensors of measurable periodic binary coefficients with exact fraction $\theta$.
- `laminationClosureAt L₀ L₁ θ` is the closure of finite laminate tensors with exact overall fraction $\theta$. Each layer minimizes over compatible jumps and permits any real unit normal and any proportion in $[0,1]$; finite depth is unrestricted.
- `IsPeriodicBinaryWitness` requires a self-adjoint tensor, a measurable zero-one coefficient, its exact normalized fraction on a period-$2\pi$ cell, and the cell-energy identity at **every** mean gradient. Its cell energy is an infimum over weak periodic H¹ potentials.

[Attainment](../HierarchicalLaminates/GClosure/Attainment.lean) proves that the constructed cell energies are attained by weak periodic potentials at every $m\ge16$ and every positive period.

## Theorem 6.1: two quadratic branches

[HierarchicalLaminates.two_well_energy_gap](../HierarchicalLaminates/Statements/TwoWell.lean) supplies symmetric positive-definite tensors $A_0,A_1$ on $\mathbb R^{2\times32}$ and a mean gradient $F$ such that

$$
\operatorname{QC}W(F)<\operatorname{RC}W(F),
\qquad W(G)=\min\{G\cdot A_0G,G\cdot A_1G\}.
$$

The branches are homogeneous quadratic forms. The construction uses two groups of sixteen potentials; [Components32](../HierarchicalLaminates/TwoWell/Components32.lean) identifies them with the full thirty-two-potential space and preserves unrestricted rank-one compatibility.

Both envelopes are defined as pointwise suprema over real-valued minorants. Rank-one minorants are convex along every rank-one line. Periodic quasiconvex minorants satisfy integrability and Jensen's inequality for every C¹ periodic potential on the normalized unit torus.

[EnvelopeCharacterization](../HierarchicalLaminates/TwoWell/EnvelopeCharacterization.lean) proves that every such quasiconvex minorant below a continuous obstacle is rank-one convex. For a continuous nonnegative obstacle, its quasiconvex supremum is itself quasiconvex and is the greatest admissible minorant. [EnvelopeCharacterization32](../HierarchicalLaminates/TwoWell/EnvelopeCharacterization32.lean) transfers these results to the full space and establishes the global comparison $\operatorname{QC}W\le\operatorname{RC}W$ for the constructed energy.

[PeriodTransport](../HierarchicalLaminates/TwoWell/PeriodTransport.lean) proves equivalence of the C¹ test predicate and envelope at every positive period, for every energy function. [Statements/TwoWellPeriod](../HierarchicalLaminates/Statements/TwoWellPeriod.lean) provides the strict gap at every positive period, including the period-$2\pi$ variant `two_well_energy_gap_manuscript`. Normalized torus integrals are identified with open-cell Lebesgue averages.

## Main proof steps and their formal entry points

| Manuscript result or step | Formal entry points |
| --- | --- |
| Proposition 3.1: the material family and energy equality survive every lamination and tensor limit | [PhysicalLamination](../HierarchicalLaminates/Lamination/PhysicalLamination.lean), especially `laminateClosure_loading_balance`, and [CompactFamily](../HierarchicalLaminates/Lamination/CompactFamily.lean), especially `laminateClosure_mem_materialFamily`. Norm conventions are connected in [ClosureTopology](../HierarchicalLaminates/Lamination/ClosureTopology.lean). |
| Proposition 4.1: the smooth medium has a positive fifth-order energy difference at small contrast | [Contrast/Asymptotic](../HierarchicalLaminates/Contrast/Asymptotic.lean): `physicalGap_asymptotic` and `physicalGap_eventually_positive`. [Finite/Coefficients](../HierarchicalLaminates/Finite/Coefficients.lean) checks the coefficient by exact recurrence. |
| Lemma 5.1: the selected stripe mean fluxes converge to those of the smooth medium | [Corrector/BinaryComparison](../HierarchicalLaminates/Corrector/BinaryComparison.lean), [BinaryResidual](../HierarchicalLaminates/Corrector/BinaryResidual.lean) and [Material/BinaryGap](../HierarchicalLaminates/Material/BinaryGap.lean) give the residual and response estimates used to choose a finite stripe count. |
| Section 5.3: every prescribed phase fraction and every $m\ge16$ | [Composition/Counterexample](../HierarchicalLaminates/Composition/Counterexample.lean) gives exact-fraction recovery; [GClosure/DimensionPeriod](../HierarchicalLaminates/GClosure/DimensionPeriod.lean) carries the witness to additional potentials and the period-$2\pi$ cell. |
| Proposition 6.2: a continuous homogeneous rank-one convex minorant and its completed-square lower bound | [MaterialCompactness](../HierarchicalLaminates/TwoWell/MaterialCompactness.lean), [MinorantRegularity](../HierarchicalLaminates/TwoWell/MinorantRegularity.lean), [Minorant](../HierarchicalLaminates/TwoWell/Minorant.lean) and [DualLamination](../HierarchicalLaminates/TwoWell/DualLamination.lean). |
| Theorem 6.1's upper bound and quantitative envelope gap | [ExactTrials](../HierarchicalLaminates/TwoWell/ExactTrials.lean) gives the primal and stream-potential trial, with one shared phase indicator; [H1Trial32](../HierarchicalLaminates/TwoWell/H1Trial32.lean) supplies the weak-H¹ trial inequality. [PeriodicTrials](../HierarchicalLaminates/TwoWell/PeriodicTrials.lean) gives the density-based upper bound. |
| Appendix B: reduced cell response, effective tensor and field regularity | [Contrast/Response](../HierarchicalLaminates/Contrast/Response.lean), [FullTensor](../HierarchicalLaminates/Contrast/FullTensor.lean), [ReducedSymmetry](../HierarchicalLaminates/Contrast/ReducedSymmetry.lean), [Regularity](../HierarchicalLaminates/Contrast/Regularity.lean) and [Smoothness](../HierarchicalLaminates/Contrast/Smoothness.lean). |

For the three-cosine profile, the detecting functional is $\ell(B)=\eta\cdot B\eta-\xi\cdot B\xi$. Its first nonzero coefficient is $2\kappa$, where $\kappa=1/1062744883200$. The construction uses $\rho=\kappa/32=1/34007836262400$; the physical remainder estimate yields $\ell(B)\ge(269/256)\kappa\rho^5>0$.

## Analytic foundations and supporting results

Weak derivatives are defined by integration by parts against smooth periodic tests. The Hilbert-space cell solver uses the L² closure of periodic gradients. [Periodic/Attainment](../HierarchicalLaminates/Periodic/Attainment.lean) proves a Poincaré estimate, equality with the weak-gradient range, potential recovery and unique zero-mean minimizing correctors. Positive-period transport uses $u_L(x)=L u(x/L)$, which preserves gradients and normalized energy averages.

| Supporting result | Formal scope |
| --- | --- |
| [Weak-H¹ trials](../HierarchicalLaminates/TwoWell/H1Trial32.lean), [exact trials](../HierarchicalLaminates/TwoWell/ExactTrials.lean) | Arbitrary weak variations are admissible in the constructed envelope bound. An attained primal corrector and a stream potential give the exact selected two-cell energy and quantitative gap. |
| [Smooth trials](../HierarchicalLaminates/TwoWell/SmoothTrials.lean) | Jointly smooth periodic gradients are dense in the weak-gradient space, and smooth potentials achieve every strict upper margin above the selected cell-energy bound. For a continuous integrand whose energy integral is continuous in the strong L² topology, smooth and C¹ Jensen tests are equivalent. The two-well energy satisfies these conditions. |
| [Variable contrast](../HierarchicalLaminates/Contrast/Asymptotic.lean) | The physical response has a fifth-order expansion and an eventually positive loading difference as contrast tends to zero from above. Physical identification holds for $0\le r<2/3$, with coercivity $\min(1/4,1-3r/2)$. The fixed numerical construction is a specialization. |
| [Joint smoothness](../HierarchicalLaminates/Corrector/Smoothness.lean) | Polynomial Fourier moments give joint C∞ regularity of the real lifts, including mixed derivatives of the potential, gradient and source field. |
| [Rational branches](../HierarchicalLaminates/TwoWell/RationalBranches.lean) | The quadratic branch matrices have rational entries, including the inverse-dependent complementary block. |
