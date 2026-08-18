# Boundary shadows, observer families, and reconstruction

This note records the cross-domain theorem boundary linking observer refinement,
future-language safety, exact reopening, typed hyperfabric gluing, and the
repository's cautious holography vocabulary.

## Core distinction

An observation

```text
O : State -> Boundary
```

is only a projection.  It becomes an exact reconstructive encoding only after
an explicit map

```text
R : Boundary -> State
```

and proof

```text
R (O x) = x.
```

`DASHI.Core.BoundaryObservationReconstructionExact` proves that exact
reconstruction implies observer separation.  Therefore any explicit observer
collision rules out exact reconstruction through that boundary surface.

The existing provenance-bearing quotient supplies the canonical positive case:

```text
(surface , exact reopening receipt)
```

reconstructs the fine carrier exactly.

This is the safe structural content behind the phrase:

> a statistic is a boundary shadow, not a hologram, unless a reconstruction
> theorem has been supplied.

No physical AdS/CFT theorem is imported by that analogy.

## Relevant rather than ontological reconstruction

For decision and policy systems exact whole-state reconstruction is often much
stronger than necessary.  `FutureRelevantBoundaryReconstructionExact` uses the
existing canonical future-observation equivalence instead.

If

```text
coarsen : State -> Coarse
```

is future-language safe for a declared action/observation system and has a
section, then selecting the section representative reconstructs a state with
the same complete declared future observation language as the original state.

Thus:

```text
sectioned future-safe projection
  -> future-relevant representative reconstruction.
```

This does not promote future equivalence into universal world identity.

## Multi-outcome policy/evaluation regression

`MultiOutcomeBoundaryShadowRegressionExact` gives a deliberately abstract
three-coordinate outcome carrier.

It proves by explicit collisions that:

```text
one outcome
  != whole outcome state,

one outcome + a second outcome
  != whole outcome state.
```

The declared full three-coordinate vector is reconstructive only because the
toy carrier is exactly that vector and the reconstruction theorem is supplied.
The example does not claim that any real social programme is exhausted by
three outcomes.

The point is methodological: salience and informativeness are not substitutes
for a separation or reconstruction theorem.

## Hyperfabric gluing is a distinct gate

`TypedHyperfabricCore` already requires a compatibility witness before local
vertex/edge values constitute a `GlobalSection`.

`HyperfabricObservationGluingExact` extracts this boundary and supplies a tiny
counterexample in which a local vertex carries `false` while the shared edge
carries `true` under the identity restriction.  The local assignment therefore
cannot glue.

Hence the hierarchy is:

```text
local observations
  != compatible global section
  != separating observer family
  != relevant reconstruction
  != exact reconstruction.
```

Each step requires its own theorem.

## Holographic receipt correction

The legacy `HolographicBulkBoundaryReceipt` contains an internal inconsistency:
its field named `continuumYangMillsConstructedIsFalse` is typed as

```text
continuumYangMillsConstructed = true
```

and the canonical receipt sets that flag to `true`, while the module-level
comments and receipt boundary explicitly state that no continuum Euclidean
Yang--Mills construction is promoted.

`HolographicBulkBoundaryReceiptCorrectionExact` quarantines that legacy flag
and supplies a corrected fail-closed downstream boundary:

```text
continuumYangMillsConstructed = false
Clay Yang--Mills promoted      = false
boundary observation implies reconstruction = false.
```

The legacy record is not silently reinterpreted; consumers can migrate to the
corrected boundary explicitly.

## Existing clopen holography agrees with the reconstruction boundary

`ClopenHolographicEffectiveFieldTheoryBoundary` already classifies its
finite-depth boundary observable as `target-only`, keeps physical p-adic
spacetime promotion false, and requires a separate covariance-aware empirical
receipt before observable promotion.

`ClopenHolographicObserverReconstructionBoundaryExact` makes the corresponding
reconstruction statement explicit:

```text
target-only boundary observable
  != bulk decoder
  != physical ontology promotion.
```

## Combined anti-collapse ladder

The observer/refinement stack can now distinguish all of the following:

```text
static relevance
!= current-query sufficiency
!= local observational data
!= compatible/glued global section
!= static observer refinement
!= separating observer
!= factorized/natural refinement
!= policy/action naturality
!= future-language safety
!= future-relevant reconstruction
!= exact reconstruction
!= world identity/completeness
!= physical fidelity/ontology.
```

The constructive path is correspondingly theorem-driven:

```text
projection
-> exhibit collision if present
-> add the smallest source-native refinement
-> prove compatibility/gluing where required
-> prove future-language safety for the declared decision language
-> reconstruct only the relevant equivalence class when that is enough
-> require an explicit exact decoder before claiming full-state reconstruction.
```
