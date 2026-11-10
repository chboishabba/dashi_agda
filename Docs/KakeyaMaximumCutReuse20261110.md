# Kakeya maximum-cut reuse inventory — 2026-11-10

## Exact status

The original three-dimensional Kakeya dimension theorem is by **Hong Wang and Joshua Zahl** (2025), *Volume estimates for unions of convex sets, and the Kakeya set conjecture in three dimensions*, https://arxiv.org/abs/2502.17655. The streamlined argument is by **Larry Guth, Hong Wang and Joshua Zahl** (2026), https://arxiv.org/abs/2601.14411. Credit for classical Cauchy--Schwarz remains with Cauchy and Schwarz. The finite interface in this repository is repository-original **integration**, not an original Kakeya dimension theorem.

The Chinese Academy of Sciences (2026-09-08) reports a kernel-checked Lean 4 formalisation by the MMAT/Project Numina collaboration, combined with Nankai/Seed work: https://www.amss.cas.cn/kyjz1/202609/t20260908_8279602.html . Their description explicitly treats a key sticky-Kakeya estimate as an external input in the relevant chain. Audit the actual Lean source and dependency graph before asserting fully assumption-free equivalence of any particular entry theorem. This is prior art worth importing or translating, not rediscovering.

## Maximum-cut graph

| Cut | Reusable prior art | Deliverable | Status |
| --- | --- | --- | --- |
| K0 finite algebra | `NSTriadKNRationalOrderedFiniteL2`: finite Gram identity, rational squared CS, restricted pairs | `KakeyaFiniteIncidenceReuseExact`: naming, exact finite incidence and geometric adapter | Implemented, Agda kernel verification not run in this environment |
| K1 geometric adapter | Existing C3 complex Euclidean carrier; existing geometry modules | Certify *actual* rational cell discretisation of delta tubes, support, intersection, disjointness, occupancy, mass, and parameter uniformity | OPEN |
| K2 convex concentration | Wang--Zahl Convex Wolff Axioms / 2026 streamlined theorem | Formal selected convex-set concentration, shadings, parent-child compatibility and rescaling | OPEN |
| K3 multiscale | Guth--Wang--Zahl, external Lean formalisation | Reuse induction-on-scales and sticky-Kakeya estimates; check all external assumptions and constants | OPEN |
| K4 dimension transfer | Lean 4 formalisation, measure and Hausdorff/Minkowski content | Prove `delta`-uniform union volume to full Hausdorff/Minkowski dimension for Kakeya sets | OPEN in Agda |
| K5 maximal function | Separate stronger inequality; 2026 AI research claims require independent proof audit | State correct maximal-operator assertion with exponent/constants, check independently | OPEN in this repo |

## Exact declarations completed in this tranche

- `finiteIncidenceGramIdentity`: exact Gram-defect identity inherited from proved rational L2 source
- `finiteIncidenceGramDefectNonnegative`: nonnegative defect
- `finiteIncidenceSecondMoment`: exact finite second-moment inequality
- `finiteRestrictedIncidenceSecondMoment`: restricted family with explicit monotonicity certificate
- `GeometricIncidenceAdapter` and `geometricAdapterSecondMoment`: no hidden identification with physical tube geometry

These statements are only as strong as their concrete rational meaning. Occupied weight is **not** automatically Euclidean Lebesgue union volume. An arbitrary finite incidence pair is **not** automatically a genuine tube incidence. None of the above proves the Wolff geometric estimates or dimension theorem.

## Specific next unpaid proof obligations

1. `tubeCellMultiplicityCorrect`: finite cell multiplicity computed from the original tube membership relation, with explicit finite resolution.
2. `occupiedCellsAreUnion`: equivalence of support with union membership, and a disjoint finite-cell volume equality.
3. `tubeIncidenceTotalCorrect`: weighted incidence first moment equals the sum of individual selected tube contributions; handle clipping and boundaries.
4. `tubeOverlapEnergyCorrect`: second moment equals intersection sums, including multiplicities.
5. `convexWolffOriginalFamily`: precise concentration bounds on arbitrary selected convex sets for the *same* tube family.
6. `grainParentChildShadingCompatible`: chosen parent/child refinement and shading-mass compatibility, with no free multiplicity assumption.
7. `inductionScaleLossUniform`: same-family constants, small scale losses and quantitative iteration.
8. `kakeyaDimensionFromUniformVolume`: proof from arbitrarily small scales to Hausdorff and Minkowski dimension three.
9. `leanFormalizationDependencyAudit`: pinned external formal proof versions, axioms, sorry/admit, exported theorem types, source and attribution.
10. `maximalFunctionIndependentGate`: do not equate the Kakeya set theorem to the stronger maximal-function estimate.

## Verification contract

No Agda executable or checked build was available in this interaction. Source-written declarations are **not** promoted to kernel-checked. Run Agda 2.9 with the existing project's pinned Nix environment and explicitly check the changed module and its transitive imports. Follow the repository's no-CI-dependence policy; record a local reproducible check instead.

## Attribution / non-promotion

Record the exact mathematical origin of every imported result. Distinguish inherited algebra, source theorem, translated formal proof, selected input assumptions, and original connector code. Do not claim priority over Wang, Zahl, Guth, the MMAT/Project Numina/Seed/Nankai groups, or the historical authors. Do not represent a conditional adapter as a full 3D or 4D proof.
