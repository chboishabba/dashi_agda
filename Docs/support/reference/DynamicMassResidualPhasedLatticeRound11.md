# Dynamic mass, minimal residuals, and phased relational lattices — Round 11

This tranche extends PR #530 without duplicating the stacked PNF/reopenable-evidence core. The base already supplies `ProvenanceBearingQuotient`, `DynamicalQuotientSafety`, `ConsumerIndexedRelevanceMeasure`, `ConsumerProjectionSufficiency`, the finite `CantorConsumerRelevanceReference`, signed `TypePressure`, horizon/depth orthogonality, and the earlier aligned memory-wheel adapter.

## Exact additions

### Recoverable quotient composition

`DASHI.Core.RecoverableQuotientCompositionExact` adapts the existing `ProvenanceBearingQuotient` to a composable exact projection shell and proves that

`X --pi1--> Y --pi2--> Z`

reopens exactly when the composite residual is

`delta21(x) = (delta1(x), delta2(pi1 x))`.

Thus composition does not silently discard the intermediate residual.

### Minimal sufficient residual: hidden phase

`DASHI.Core.MinimalDynamicResidualExact` reuses the existing hidden-phase dynamic-insufficiency counterexample. Boolean observation alone is dynamically unsafe, but the pair `(visible Bool, C3 phase)` reopens the complete packed state exactly. In the explicit two-tier family `{no residual, phase residual}`, the zero tier has no sufficiency constructor and the phase tier has cost one. This is a finite exact minimal-residual witness, not a general global minimization theorem.

### Cantor unit mass is not truth

`DASHI.Foundations.CantorUnitMassDynamicBridgeExact` composes the already-existing static unit-mass certificate with dynamic trace-congruence. It therefore distinguishes:

- normalized consumer/task mass;
- objective-world coverage;
- dynamic sufficiency;
- exact reopening through a residual.

The depth-three finite Cantor reference still has 27 ambient ternary cells and 8 surviving polar cells while the consumer-normalized surviving region carries unit task mass. The unit is explicitly model/task-relative, not a truth value.

### Approximate MDL residual-budget analogue

`DASHI.Core.ApproximateMDLResidualBudgetExact` records the motivation from Qian Li, Xinyu Mao, Shang-Hua Teng, and Guangxu Yang, *Prediction Under Imperfect Compression: A Theory of Approximate MDL*, arXiv:2606.04834v1 (2026). No DOI is asserted for the arXiv preprint.

The paper proves a statistical separation between fixed additive and multiplicative approximation in sequential MDL. The Agda does not import that theorem as proof authority. It formalizes only the finite DASHI analogue: fixed additive slack is independent of carrier complexity, while scale-relative slack can grow with complexity. A concrete cost-2 residual is admitted by unit scale-relative slack at complexity 3 but rejected by fixed unit slack.

### Independent wheel grade

`DASHI.Cognition.PNF.IndependentWheelMemoryGradeExact` fixes the abstraction boundary identified in the later memory synthesis. `MemoryFibre.phase` remains an application-level coordinate. A separate `WheelDepthCoordinate` is attached without mutating the legacy phase, and optional alignment is represented by an extra witness. The older `WheelMemoryFibre` remains a useful aligned subcarrier rather than the universal memory representation.

### Constraint frustration

`DASHI.Cognition.PNF.ConstraintPhaseFrustrationExact` refines the earlier raw phase-disagreement energy. Each coupling now declares an admissible relative phase relation (`samePhase`, `nextPhase`, or `unconstrained`). The exact witness

`phase-0 -> phase-1`

has raw disagreement 1 but zero constraint cost under `nextPhase`. Thus asynchronous channels are not intrinsically frustrated. A separate finite theorem proves that `samePhase` and `nextPhase` cannot both be satisfied on the same pair.

### Phased relational lattice

`DASHI.Cognition.PNF.PhasedRelationalLatticeExact` reuses `TypePressure`, `EvidenceDepthWheelOrthogonality`, and the existing relational-horizon carrier. A cell is typed by resolution depth, relational horizon, process phase, a signed type-pressure envelope, and a semantic phase derived from that envelope. Process-phase advance preserves semantic phase when evidence is unchanged, and horizon expansion commutes with process advance.

This keeps the distinct coordinates explicit:

- representation/refinement resolution;
- relational horizon;
- C3 process phase;
- evidence-derived semantic phase.

The semantic phase is therefore a coarse observation of the retained signed pressure, not an independently mutable truth label.

## Boundary

The tranche does not prove the classical limiting Cantor measure theorem, the Approx-MDL paper's statistical theorems, a universal minimal sufficient statistic theorem, a clinical trauma model, or a universal biological phase law. It supplies finite/type-theoretic constructions and exact counterexamples that can serve as regression laboratories for those stronger questions.

The resulting spine is:

**unit mass is a normalization/accounting claim; safe forgetting is a future-dynamics theorem; when safety fails, the smallest proven sufficient residual should remain explicitly reopenable.**
