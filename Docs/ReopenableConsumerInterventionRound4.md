# Reopenable consumer/intervention kernel — round 4

This tranche turns the SeaMeInIt / Animalexic / LES cross-pollination into theorem-bearing reusable DASHI modules rather than another set of domain receipts.

## Core theorem spine

The shared state-transition object is consumer indexed:

```text
fine state
  -- declared action --> fine state
      |                    |
      v                    v
 consumer observation   consumer observation
      |
      +-- authority is a separate coordinate
```

`DASHI.Core.ConsumerIndexedGovernedTransitionExact` defines finite-depth action/observation equivalence and proves that an abstraction which preserves action transitions, consumer observations, and consumer authority makes every same-fibre pair future-equivalent at every requested finite depth.

This is intentionally stronger than current-score equality and weaker than world identity. It is relative to the declared consumer and action language.

## Selective authority

`DASHI.Core.SelectiveAuthorityCertificateExact` separates numerical certification from promotion. A candidate can be `promote`, `abstain`, or `reject`; abstention falls back to an independently valid anchor, while rejection yields no canonical candidate. A numerical certificate cannot construct an authorised candidate without the separate authority witness.

References:

- J. Hendrickx et al., **Machine learning with a reject option: a survey**, *Machine Learning* (2024), DOI `10.1007/s10994-024-06534-x`.
- Richard H. Byrd, Peihuang Lu, Jorge Nocedal, Ciyou Zhu, **Algorithm 778: L-BFGS-B: Fortran Subroutines for Large-Scale Bound-Constrained Optimization**, *ACM Transactions on Mathematical Software* 23(4), 1997, DOI `10.1145/279232.279236`.

## Decision-relative multi-fidelity escalation

`DASHI.Core.AdaptiveFidelityConsumerMarginExact` does not demand globally tiny surrogate error. A domain supplies a discrepancy bound and a consumer-specific region on which the decision is invariant. If the discrepancy bound lies inside that region, low- and high-fidelity decisions are theorem-equal; otherwise the system has an escalation obligation rather than evidence that the cheap result is false.

References:

- Marc C. Kennedy and Anthony O'Hagan, **Predicting the output from a complex computer code when fast approximations are available**, *Biometrika* 87(1), 2000, DOI `10.1093/biomet/87.1.1`.
- Natalia M. Alexandrov, J. E. Dennis Jr., Robert M. Lewis, Virginia Torczon, **A trust-region framework for managing the use of approximation models in optimization**, *Structural Optimization* 15, 1998, DOI `10.1007/BF01197433`.

## Counterexample-guided refinement

`DASHI.Core.CounterexampleGuidedConsumerRefinementExact` packages one consumer-descent defect and a refined observer which splits that concrete collision. It proves that such a genuine split cannot itself factor through the old coarse observer. The boundary is explicit: one repaired collision does not prove global separation or future safety; repeated refinement still needs a stopping theorem. Existing finite-ranked stabilization and certified future-quotient modules remain the owners of those global finite claims.

## Evidence and dependency reopening

`DASHI.Core.TypedEvidenceDependencyExact` separates provenance-root independence from statistical independence. Multiple downstream metrics from one evidence root cannot be certified as multiple provenance-independent confirmations. It also gives exact transitive dependency paths and typed reopen reasons (`budgetDeferred`, `ambiguityUnresolved`, `dependencyChanged`, `fidelityEscalation`, `policyChanged`).

This is the shared kernel behind:

- Animalexic: same-frame/multimodal evidence and hypothesis reopening;
- SeaMeInIt: body/ROM/panel/manufacturing invalidation;
- LES: assimilation followed by selective replanning.

## World actions and information actions

`DASHI.Core.DualEffectInformationActionExact` places both in one action language. An action can change the world coordinate, the information coordinate, or both. A pure information action is therefore a property of an action rather than a separate planner universe. `InformationSeparatingAction` captures the exact bounded form of active sensing/experimentation: two currently collapsed information states become distinguishable after the declared action.

## Proof-carrying compliance

`DASHI.Core.CompositionalComplianceExact` treats a stage receipt as a proof of a predicate over the actual input and output. Sequential composition retains the intermediate carrier in a dependent pair, preventing unrelated endpoint proofs from being spliced merely because their types match.

References:

- George C. Necula, **Compiling with Proofs**, PhD thesis, Carnegie Mellon University, Technical Report CMU-CS-98-154 (1998), no DOI recorded here.
- Nir Bitansky, Ran Canetti, Alessandro Chiesa, Eran Tromer, **Recursive composition and bootstrapping for SNARKS and proof-carrying data**, STOC 2013, DOI `10.1145/2488608.2488623`.

No cryptographic proof-system claim is made; the reuse is the compliance-predicate composition shape.

## Adaptive wearable instance

`DASHI.Geometry.AdaptiveWearableCompilerExact` is the SeaMeInIt-facing formal instance. It provides:

- explicit finite empirical ROM fields and exact max/total projections;
- abstract-scalar discrete angle-defect / regional curvature measure;
- an explicit curvature-accommodation vocabulary (material strain, seam, dart, gusset, subdivision, approximation);
- panel action grammar;
- distinct seam/manufacturing/thermal/support consumers;
- an adapter into the generic consumer-indexed governed transition system.

The ROM layer deliberately starts with finite sampled poses. It does not invent a probability distribution. Probability-weighted tail risk/CVaR is a later domain theorem once pose weights have a justified semantics.

Geometry/fabrication references:

- Oded Stein, Eitan Grinspun, Keenan Crane, **Developability of Triangle Meshes**, *ACM Transactions on Graphics* 37(4), 2018, DOI `10.1145/3197517.3201303`.
- Nico Pietroni, Corentin Dumery, Raphael Falque, Mark Liu, Teresa A. Vidal-Calleja, Olga Sorkine-Hornung, **Computational Pattern Making from 3D Garment Models**, *ACM Transactions on Graphics* 41(4), 2022, DOI `10.1145/3528223.3530145`.
- David Cohen-Steiner and Jean-Marie Morvan, **Restricted Delaunay Triangulations and Normal Cycle**, SoCG 2003, DOI `10.1145/777792.777839`.
- Katja Wolff, Philipp Herholz, Verena Ziegler, Frauke Link, Nico Brügel, Olga Sorkine-Hornung, **Designing Personalized Garments with Body Movement**, *Computer Graphics Forum* 42(1), 2023, DOI `10.1111/cgf.14728`.

The module does not claim that angle defect alone determines a manufacturable pattern or that a cut destroys Gaussian curvature. The intended statement is that panel/material operators redistribute the planar-realisation burden induced by non-developable geometry.

## LES theorem reuse

`DASHI.Environment.LESResearchCrossPollinationRound4Exact` proves that Round-2 exact causal abstraction is literally an instance of the generic `Intertwiner`, that its outcome square is a generic `ConsumerDescent`, and that LES hybrid execution is a world-only instance of the dual-effect action system.

Thus the cross-project relation is theorem-level rather than a similarity table.

## Focused roots

```text
DASHI/ReopenableConsumerInterventionCrossDomainEverything.agda
DASHI/Core/ReopenableConsumerInterventionCrossDomainRegression.agda
DASHI/Environment/PlanningLoopRegression.agda
```

## Claim boundary

The common kernel proves structural facts about abstraction, finite future behaviour, fidelity escalation, evidence provenance, reopening and authority. It does not establish cloth constitutive laws, animal semantics, environmental calibration, stakeholder legitimacy, or continuous-state global search completeness. Those remain domain producers and can now be attached without reimplementing the shared theorem machinery.
