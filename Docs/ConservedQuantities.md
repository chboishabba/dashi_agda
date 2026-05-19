# Conserved Quantity Lane

## Scope
This lane documents the most promising conserved quantities that are already visible in the Dashi closure program, highlights what is formalized versus what remains to be defined, and frames a theorem-style note describing the minimal failures should those quantities not be preserved. No shared files are touched; everything lives under `Docs/`.

## Candidate conserved quantities
- **MDL descent as quasi-conservation.** The execution contract makes `L(x)` a Lyapunov function: each step satisfies `L(step x) ≤ L(x)`. Formally we can treat `ΔL := L(x) - L(step x)` as the “energy dissipated” per step, and the conservation candidate is the cumulative `L0 - L(x)` reaching a plateau whenever the coarse descent terminates. Already formalized: `shiftExecutionAdmissible` uses `OldMDL.Lyapunov.descent` and `RGCoarseWitnessPackage.signatures` preserve `mdlLevel`. Missing: a precise statement that `(L0 - L(x))` is conserved across coarse schedules and how deviations signal failure modes.
- **Cone membership as invariant charge.** The cone witness `ShiftConeCompatible x` represents a binary statement that the state stays within the Lorentz cone. Its candidate conserved quantity is the indicator `1_{InCone}`. Formalized: `shiftConeTransportStep/Coarse` prove that the witness is preserved under allowed schedules. Missing: a scalar charge (e.g., cone depth) and a theorem that `Δcone` equals zero unless a failure mode (e.g., crossing the boundary) occurs.
- **Gödel/Hecke signature counts.** The flattening to `Sig15` and eigen profiles yields a finite set of bits. The conserved quantity is the signature histogram (counts of primes flagged as `true`). Formalized: `shiftPipeline` extracts `shiftPrimeEmbedding` and the RG surface preserves `heckeSignature`. Missing: a proof that these counts are invariant up to MDL or coarse updates and explicit failure modes when they are not.
  Current boundary correction: after the archived `Dashi and Physics Insights`
  thread and the failed canonical widening probe, raw `heckeSignature` should
  now be treated first as representation-layer structure rather than as the
  next default conserved-witness candidate. See
  [`HeckeRepresentationLayer.md`](./HeckeRepresentationLayer.md).

- **Eigen-profile payload.** The RG layer already computes
  `RGOI.RGObservable.eigenSummary`, and the live shift witness package proves
  `shiftEigenSchedule` on the shift carrier. Missing: a bridge from the
  canonical closure-derived carrier law in
  [`CanonicalAbstractGaugeMatterInstance.agda`](../DASHI/Physics/Closure/CanonicalAbstractGaugeMatterInstance.agda)
  into that shift-side schedule. The current blocker is not a missing rewrite:
  the canonical law `x ↦ [ CR , x ]` lives on the three-point canonical
  carrier, while the available eigen schedule is proved only for
  `shiftCoarse/step` on the transported shift carrier. Until that bridge
  exists, `eigenSummary` is not an honest next conserved witness.

## Current classification boundary

The current closure results now support an explicit three-way split.

### Descending physical observables

These are the channels currently known to survive the closure quotient and
bridge canonically to the schedule side on the canonical carrier:

- `Gauge`
- `basinLabel`
- `motifClass`
- and the products/subquotients they generate

The strongest currently bridged package is therefore:

- `Gauge × basinLabel × motifClass`

That coarse package is now formalized in
`DASHI/Physics/Closure/CanonicalClosureCoarseObservable.agda`, so the current
conserved-quantity boundary is no longer only a doc claim.

### Structured fibre/defect data

These channels are theorem-bearing and informative, but they are not conserved
base observables of the current closure law:

- bridge-level `mdlLevel`
- bridge-level `eigenShadow`
- raw `eigenSummary`
- raw `heckeSignature`

The current best reading is that they live as internal fibre or defect data
over the coarse quotient, not as the next conserved package.

So the current conserved-quantity lane should no longer ask only
"is this channel preserved?". It should also ask:

- does the channel descend to the coarse closure quotient?
- if not, does it define a lawful field on the fibre over that quotient?

That reframes the current `CP` failures constructively: they are candidates
for structured fibre fields rather than evidence that the observable is useless.

### Scaffolding and diagnostics

These objects remain construction or diagnosis surfaces until a stronger
descent theorem promotes them:

- raw prime-address carriers
- support-style quotient probes
- synthetic transport wrappers
- correspondence/defect packaging used to expose obstruction structure

## Theorem-style formulation
Let `Q(x)` denote one of the candidate scalars above. For the conserved quantity to hold across the closure, state:

> **Conservation Clause:** For any admissible execution/coarse step pair `(evolve, coarse)` and any state `x` satisfying `admissible x`, `Q(coarse(evolve x)) = Q(evolve(coarse x))`.  
> **Failure modes:** If the equality fails, then either (a) `x` left the Shannon basin `ShiftInBasin`, (b) the cone witness is violated, or (c) the observable signature changed, each of which can be detected via the respective witness records already tracked in `shiftRGWitnessPackage`.

Execution-side refinement:

- the live contract should be read as a step contract on projected deltas,
  not as a claim that absolute-state quadratics descend globally;
- source-side `j-fixed` tags should currently be treated as diagnostics or
  proposal-side metadata, not as the admissibility criterion for traces;
- the runtime acceptance surface is now aligned to the same five clauses as
  the Agda contract:
  arrow,
  projected-delta cone,
  MDL,
  basin,
  eigen overlap.
- `DASHI/Physics/Closure/ExecutionContractLaws.agda` packages the readable
  receipt layer for those obligations, and `scripts/execution_contract.py`
  is the matching projected-delta enforcement surface.
- the closure-side tightening is now explicit rather than implied:
  `DASHI/Physics/Closure/Projection.agda` carries the projection and
  projected-delta compatibility structure,
  `DASHI/Physics/Closure/Basin.agda` carries the attractor-relative basin
  structure on the projected carrier,
  `ExecutionContract.agda` now consumes those objects directly, and
  `scripts/run_execution_contract_on_closure_csv.py` is the dedicated runtime
  adapter for `closure_embedding_per_step.csv`.

## Missing links
- Need a scalar lifting for each candidate (e.g., `L` difference, cone depth, prime counts) with a formal `DeltaQ = 0` definition.
- Need explicit failure categories (e.g., `Δcone > 0` triggers Lorentz lock failure) with code references to where they should be asserted.
- Need a note tying these charges to MDL/observable universality theorems so the control law can raise alarms rather than silently discard them.
- Need a canonical closure-to-shift schedule bridge before any eigen-profile
  conserved-quantity widening can be proved honestly.
- The first explicit fibre-field surface is now landed on the canonical
  carrier in `CanonicalClosureFibre.agda` and
  `CanonicalClosureFibreFields.agda`; the next remaining proof step is to
  push from count-level control into the richer factorization layer now
  landed in `CanonicalClosureFibreDefectFactorization.agda`, and then show
  that actual Hecke/eigen fibre fields are controlled by those defect-profile
  or histogram carriers rather than only by their count projections.
- `CanonicalClosureFibreEigenShadowObstruction.agda` now also proves that
  `eigenShadow` varies inside the coarse quotient
  `Gauge × basinLabel × motifClass` itself, so it must be treated as genuine
  fibre data rather than the next plausible descending conserved package.
- `CanonicalClosureFibreOrbitSummaryControl.agda` adds the first positive
  control signal after that obstruction: the richer orbit-summary carrier
  already detects the same-fibre `eigenShadow` variation on the canonical
  carrier, and the `p2` orbit-summary coordinate already detects it by itself.
- That same module now goes one step further on the canonical carrier:
  equality of the `p2` orbit-summary coordinate forces equality of
  `eigenShadowField` on the coarse fibre. So `p2` is now a theorem-bearing
  control surface there, not only a diagnostic witness.
- That control is now packaged explicitly as a quotient-facing factor surface
  in `CanonicalClosureFibreOrbitSummaryControl.agda`, and the same
  `p2` coordinate now also controls `heckeField` on the canonical coarse
  fibre.
- `ShiftContractObservableTransportPrimeCompatibilityProfileInstance.agda`
  replays the observable-transport/prime-compatibility bridge stack on full
  `ShiftContractState`, showing that the witness-level bridge and
  forced-stable inequality surface already survive on a broader noncanonical
  carrier.
- `ShiftContractCoarseObservable.agda` now lifts the same coarse observable
  package `Gauge × basinLabel × motifClass` onto that broader carrier, so the
  coarse conserved package is no longer canonical-only even though the richer
  fibre controls still are.
- `ShiftContractCoarseFibre.agda` and
  `ShiftContractCoarseFibreFields.agda` now extend that broader carrier with a
  thin coarse fibre and the first noncanonical Hecke/eigen/prime/count field
  surface, so the next gap is a theorem-bearing noncanonical control law
  rather than missing fibre vocabulary.
- `ShiftContractNoncanonicalP2ControlObstruction.agda` now proves that the
  current noncanonical coarse observable is too weak for a canonical-style
  `p2` control surface: same coarse observable does not force same
  transported prime image on `ShiftContractState`.
- `ShiftContractMdlLevelCoarseObservable.agda` and
  `ShiftContractMdlLevelCoarseFibre.agda` now package the cheapest aligned
  strengthening above that coarse package,
  `mdlLevel × (Gauge × basinLabel × motifClass)`, as a reusable normalized
  surface with its own thin fibre; the same obstruction pair is already
  separated there. `ShiftContractMdlLevelCoarseFibreFields.agda` now mirrors
  the first Hecke/eigen/prime/count/orbit-summary field layer on that
  stronger surface. `ShiftContractMdlLevelP2ControlAttempt.agda` packages the
  first positive theorem there, and
  `ShiftContractMdlLevelCounterexampleAudit.agda` records that the old coarse
  counterexample is no longer the active blocker. `ShiftContractNoncanonicalMdlP2Control.agda`
  still packages the missing stronger control-shape beyond that narrow
  positive result. `ShiftContractMdlLevelOrbitSummaryControlAttempt.agda`
  adds the first intermediate orbit-summary theorem on that stronger fibre:
  prime equality already forces equality of the `p2` orbit-summary
  coordinate. `ShiftContractMdlLevelP2PrimeBridge.agda` then packages the
  full orbit-summary coordinate corollaries of that bridge, and
  `ShiftContractMdlLevelPrimeImageSubfamilyAttempt.agda` adds the first
  singleton-subfamily prime-image theorem.
  `ShiftContractMdlLevelPrimeImageSubfamilyRefinement.agda` now wraps the
  current explicit witness set into a two-point family and records that the
  mixed case is already excluded by `π-mdl-max`.
  `ShiftContractMdlLevelWitnessSearchAudit.agda` now packages the bounded
  same-carrier search outcome explicitly: no fresh equal-`π-mdl-max` /
  unequal-prime-image witness has been recovered from the current in-repo
  `ShiftContractState` examples.
  `ShiftContractMdlLevelWitnessSourceAudit.agda` records the same exhaustion at
  the source level.
  `ShiftContractMdlLevelExplicitStateSearchAudit.agda` then closes the obvious
  direct explicit-state pool on the actual `ShiftContractState` carrier, but
  only as a pairwise search boundary.
  `ShiftContractTriadicFamily.agda` now promotes the one-hot subset of that
  same pool into the first genuine same-carrier family theorem:
  the three one-hot states share one `π-mdl-max` value while their
  transported prime images are pairwise distinct.
  `ShiftContractAnchoredTriadicFamily.agda` now lands the next explicit
  family on the same seam: a support-width-two triad with fixed coarse head
  and rotating active tail coordinate, again with constant `π-mdl-max` and
  pairwise distinct transported prime images.
- `ShiftContractEigenShadowNormalizedPackage.agda`,
  `ShiftContractEigenShadowP2ControlCandidate.agda`, and
  `ShiftContractRGObservableProjection.agda` now give the next stronger
  fallback surfaces above it; `ShiftContractEigenShadowOrbitSummaryObstruction.agda`
  now shows that the normalized `eigenShadow × π-max` fallback still does not
  control the canonical `p2` orbit-summary key, and
  `ShiftContractEigenShadowOrbitSummaryControlAttempt.agda` packages the same
  failure as a direct no-go control theorem shape.
- So the next conserved-quantity search here is no longer "try another nearby
  quotient". The first small explicit cyclic families have now landed, and
  `ShiftContractDenseTriadicFamily.agda` now shows that the positive cyclic
  branch already extends through support width three.
  `ShiftContractAnchoredTrajectoryFamily.agda` now gives the first positive
  live-step family on the same seam: a three-state same-fibre trajectory
  prefix followed by an exit to the one-hot fixed point.
  `ShiftContractSupportCascadeTrajectory.agda` now adds the first mixed-scale
  live trajectory: a dense seed gives one same-fibre width-three step, then
  exits through the anchored and one-hot fibres.
  `ShiftContractParametricTriadicFamily.agda` now packages the positive cyclic
  branch itself as one normalized width-indexed surface, and
  `ShiftContractFullSupportTrajectory.agda` adds a distinct full-support seed
  whose live trajectory cascades 4 -> 3 -> 2 -> 1.
  `ShiftContractTailPatternTrajectoryObstruction.agda` now closes the obvious
  negative dynamic branch: the direct neg/pos tail-sign seeds leave the
  `π-mdl-max` fibre immediately.
  The nearest representation-level fallback is still blocked. The remaining
  high-value move is to go beyond the current explicit cyclic/trajectory
  families: introduce a new family generator on `ShiftContractState` and ask
  whether `π-mdl-max` can stay constant while transported prime image varies
  along that family.
- The search boundary can now be stated more tightly:
  - hold the family inside one `π-mdl-max` fibre;
  - vary in directions outside `ker(primeImage)` but inside
    `ker(π-mdl-max)`;
  - avoid pair-generated constructions and direct-tail-only probes;
  - treat triadic/cyclic structure as the current positive source class;
  - do not exclude support widths one, two, or three a priori once they are
    used as triadic same-carrier families rather than pairs.

## Goal of this lane
Produce a documentation artifact that future proofs can cite when they refer to “conserved physical quantity” detection. When the conservation equality fails, the note should be the first reference for which witness or empirical variable to inspect before declaring system failure.
