# General GR, empirical cosmology, and quantum-gravity boundaries

This tranche answers five promotion questions explicitly:

1. general Levi-Civita theorem;
2. differential Bianchi theorem;
3. continuum Einstein-matter solution;
4. empirical cosmology;
5. quantum gravity.

None was previously implemented as a complete theorem or validated physical result. The repository contained conditional interfaces and exact finite models. This tranche adds the general target signatures, eliminators that are valid once their hypotheses are supplied, and fail-closed promotion gates.

## General Levi-Civita theorem

`DASHI.Geometry.GeneralLeviCivitaTheoremBoundary` defines an abstract smooth metric geometry, existence data, and a `KoszulDetermination` producer. From that producer it proves uniqueness among torsion-free metric-compatible connections.

What is still absent is an internal smooth-manifold library, a constructive Koszul-formula derivation, and a general existence construction. The module therefore formalizes the theorem boundary rather than claiming to have recreated differential geometry from first principles.

## Differential Bianchi theorem

`DASHI.Geometry.DifferentialBianchiTheoremBoundary` separates:

- the full cyclic second Bianchi identity;
- inverse-metric contraction;
- commutation of contraction with covariant differentiation;
- divergence freedom of the Einstein tensor.

The finite continuity residual already in the repository is not treated as the general theorem.

## Continuum Einstein-matter solution

`DASHI.Physics.Closure.ContinuumEinsteinMatterSolutionBoundary` defines the data of a continuum solution: a domain, Lorentzian metric field, matter field, regularity, field equations, contracted Bianchi identity, and divergence transport. It proves conservation of stress-energy from Einstein equality plus Bianchi.

It does not construct a new smooth global solution or prove well-posedness.

## Empirical cosmology

`DASHI.Physics.Closure.EmpiricalCosmologyValidationBoundary` requires:

- a locked quantitative prediction;
- independent calibrated data with covariance and selection effects;
- a likelihood or loss;
- a null model and preregistered decision rule;
- parameter penalties, holdout or posterior-predictive checks, and systematic sensitivity;
- external replication.

The repository currently has no such completed empirical result, so empirical-cosmology promotion remains false.

## Quantum gravity

`DASHI.Physics.Closure.QuantumGravityTheoryBoundary` requires all of the following before promotion:

- a gravitational quantum state space;
- matter state space;
- diffeomorphism and local-frame gauge control;
- a positive physical inner product or measure;
- anomaly-free dynamics and closed constraints;
- composition or gluing;
- unitarity or reflection positivity;
- controlled renormalization and either UV completion or a predictive EFT;
- semiclassical recovery of Einstein dynamics;
- recovery of QFT on curved spacetime;
- controlled backreaction;
- matched low-energy constants;
- a novel validated observable prediction.

The current finite joint quantum/GR model proves interface inhabitation only. It is not promoted to quantum gravity.

## Scientific status

The implementation is intentionally honest:

- theorem **schemas and composition results** are now present;
- complete general proofs and empirical validation are not;
- no postulates or unchecked theorem names are used to promote the framework;
- all five claims remain blocked until their producer obligations are discharged.

The next mathematically substantive work is to import or build a genuine smooth differential-geometry foundation, prove the Koszul and Bianchi developments internally, then connect a physically derived matter model to a controlled continuum limit. Empirical cosmology and quantum gravity require external data and new physics, not merely additional type declarations.
