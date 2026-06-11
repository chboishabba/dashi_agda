# Hecke Defect Orbit Summaries

## Scope

This note records the first orbit-style summary layer above the full
defect-profile correspondence.

Relevant module:

- [`Ontology/Hecke/FactorVecDefectOrbitSummaries.agda`](../Ontology/Hecke/FactorVecDefectOrbitSummaries.agda)
- [`Ontology/Hecke/FactorVecOrbitSummaryObstruction.agda`](../Ontology/Hecke/FactorVecOrbitSummaryObstruction.agda)
- [`Ontology/Hecke/FactorVecOrbitForcedStableLowerBound.agda`](../Ontology/Hecke/FactorVecOrbitForcedStableLowerBound.agda)
- [`Ontology/Hecke/ForcedStableTransferBridge.agda`](../Ontology/Hecke/ForcedStableTransferBridge.agda)
- [`Ontology/Hecke/ChamberToShiftWitnessBridge.agda`](../Ontology/Hecke/ChamberToShiftWitnessBridge.agda)
- [`DASHI/Physics/Closure/PrimeCompatibilityProfile.agda`](../DASHI/Physics/Closure/PrimeCompatibilityProfile.agda)
- [`DASHI/Physics/Closure/TransportedPrimeCompatibilityProfile.agda`](../DASHI/Physics/Closure/TransportedPrimeCompatibilityProfile.agda)
- [`DASHI/Physics/Closure/ObservableTransportPrimeCompatibilityProfile.agda`](../DASHI/Physics/Closure/ObservableTransportPrimeCompatibilityProfile.agda)
- [`DASHI/Physics/Closure/CanonicalForcedStableTransferBridgeInstance.agda`](../DASHI/Physics/Closure/CanonicalForcedStableTransferBridgeInstance.agda)
- [`DASHI/Physics/Closure/CanonicalChamberToShiftWitnessBridgeInstance.agda`](../DASHI/Physics/Closure/CanonicalChamberToShiftWitnessBridgeInstance.agda)

## What is implemented

For each fixed target prime `p` and state `v`, the repo now compresses the full
15-entry defect-profile fiber into a single `DefectOrbitSummary` carrying:

- `forcedStableCount`
- `motifChangeCount`
- `totalDrift`
- `repatterningCount`
- `contractiveCount`
- `expansiveCount`

It also packages the 15-target family:

- `profileSummaryFamily : FactorVec → Vec15 DefectOrbitSummary`

and the resulting coarse comparison surface:

- `sameOrbitSummary`

## Why this matters

The full defect histogram is now known not to be chamber-invariant.

So the next honest move is not another failed chamber law on the raw full
profile fiber. It is to compare states at a coarser orbit-style summary level
and only then ask what stability, reachability, or clustering laws survive.

This module is that intermediate layer.

## Current boundary

This is a summary surface, not yet a theorem-heavy one.

The repo does **not** yet claim that:

- orbit summaries are chamber-invariant;
- orbit summaries are transport-invariant;
- `sameOrbitSummary` captures actual reachability or orbit equivalence.

It only claims that the summary object is now local and executable on the
representation layer.

## Stronger boundary already landed

The repo now also records the first negative result on this layer.

The same small `p7 = 2` versus `p7 = 3` counterexample used at the histogram
layer already shows that the full orbit-style summary is not determined by the
same pointwise legality signature alone.

So the next theorem work on this layer should not start from:

- "orbit summaries are chamber-invariant".

That claim is already too strong in the current exact-chamber setting.

## First positive law on this layer

The first field of `DefectOrbitSummary` is now constrained honestly:

- the histogram-layer `forcedStableCount p v` is a lower bound for
  `DefectOrbitSummary.forcedStableCount (profileSummaryAt p v)`.

Why this is the right statement:

- histogram `forcedStableCount` counts illegal entries only;
- orbit-summary `forcedStableCount` counts all entries whose full defect
  profile is `Stable`;
- illegal entries are always `Stable`, but the converse need not hold.

So the orbit-summary layer now inherits one genuine law from below:

- the already-landed chamber-stable illegal count injects into the first
  orbit-summary component.

## Paper-style bridge candidate

For a closure-state `x`, transported shift image `S x`, and target prime `p`,
the highest-probability next bridge remains the forced-stable lower-bound
statement:

```text
Theorem (Forced-Stable Transfer Candidate):
  illegalCount_chamber(x,p)
  ≤ forcedStableCount_hist(S x,p)
  ≤ forcedStableCount_orbit(S x,p)

Corollary (desired refinement):
  if illegalCount_chamber(x,p) = forcedStableCount_hist(S x,p)
  then the two-step bridge becomes
  illegalCount_chamber(x,p) = forcedStableCount_hist(S x,p)
    ≤ forcedStableCount_orbit(S x,p).
```

The bridge ladder is now packaged explicitly as a theorem surface:

- `illegalCount-chamber-invariant` re-exports the exact-chamber equality law
  for the chamber-side illegal count;
- `ForcedStableTransferBridge` packages the still-abstract bridge datum
  `S : ClosureState -> FactorVec` together with the first compatibility
  inequality
  `illegalCount_chamber(x,p) <= forcedStableCount_hist(S x,p)`;
- the record then derives
  `illegalCount_chamber(x,p) <= forcedStableCount_orbit(S x,p)` by composing
  that assumption with the already-proved Hecke-side lower bound.

So the repo now has the exact `1,2,3` bridge ladder as code, but only step `2`
remains abstract: the concrete closure-to-shift bridge inhabitant is still
missing.

## First concrete inhabitant

The repo now also has a first concrete inhabitant of that bridge surface on the
canonical closure carrier.

It uses the least-synthetic existing map already in the closure stack:

- `canonicalTransportState`
- then `canonicalShiftHeckeState`
- then `shiftPrimeEmbedding`

So the concrete image map is:

```text
S(x) = shiftPrimeEmbedding (canonicalShiftHeckeState (canonicalTransportState x))
```

This is packaged in:

- [`DASHI/Physics/Closure/CanonicalForcedStableTransferBridgeInstance.agda`](../DASHI/Physics/Closure/CanonicalForcedStableTransferBridgeInstance.agda)

Current honesty boundary:

- this is a real inhabitant of the bridge record;
- the orbit-side inequality is now instantiated on the canonical closure
  carrier;
- but the closure-side `illegalCountChamber` is still defined from the
  transported shift image, so this is not yet an independent closure-native
  chamber observable.

## Minimal witness bridge

The repo now also has the smaller bridge surface suggested by the current proof
boundary:

- fixed target prime `p`;
- closure-side illegal mask indexed by the 15 paired primes;
- shift witness carrying only a 15-entry forced-stable mask;
- aggregate theorem
  `illegalCount-chamber <= forcedStableCount-hist`
  proved directly from pointwise witness soundness.

This is packaged in:

- [`Ontology/Hecke/ChamberToShiftWitnessBridge.agda`](../Ontology/Hecke/ChamberToShiftWitnessBridge.agda)
- [`DASHI/Physics/Closure/PrimeCompatibilityProfile.agda`](../DASHI/Physics/Closure/PrimeCompatibilityProfile.agda)
- [`DASHI/Physics/Closure/TransportedPrimeCompatibilityProfile.agda`](../DASHI/Physics/Closure/TransportedPrimeCompatibilityProfile.agda)
- [`DASHI/Physics/Closure/CanonicalTransportedPrimeCompatibilityProfileInstance.agda`](../DASHI/Physics/Closure/CanonicalTransportedPrimeCompatibilityProfileInstance.agda)
- [`DASHI/Physics/Closure/CanonicalChamberToShiftWitnessBridgeInstance.agda`](../DASHI/Physics/Closure/CanonicalChamberToShiftWitnessBridgeInstance.agda)

This is the current minimal bridge with a real chance of surviving future
inhabitants, because it preserves only the exact index data counted by the
inequality and does not claim a richer closure-to-shift semantic identification.

The first canonical instance of that minimal bridge is now also landed.

Current honesty boundary:

- it gives a real canonical proof of
  `illegalCount-chamber <= forcedStableCount-hist`
  on the canonical closure carrier;
- the illegal mask is now computed from a closure-native compatibility profile
  on the three-generator canonical carrier;
- that compatibility profile is now factored through a reusable
  `PrimeCompatibilityProfile` surface rather than being wired directly into the
  canonical witness bridge instance;
- a second reusable route now exists for broader families that only expose a
  transported `State -> FactorVec` image so far:
  `TransportedPrimeCompatibilityProfile` forgets multiplicities and recovers
  the same witness-level bridge interface from lane presence alone;
- that transported route is now exercised concretely on the canonical carrier
  in `CanonicalTransportedPrimeCompatibilityProfileInstance`, where the
  transported profile is shown to agree with the closure-native prime
  embedding and inherits the same witness-level inequality;
- the first broader concrete carrier now uses the full `ShiftGeoV` state
  family directly in `ShiftGeoVPrimeCompatibilityProfileInstance`, so the
  same witness-level inequality and the orbit-side forced-stable bridge are
  now instantiated beyond the tiny canonical carrier;
- a second broader concrete family now instantiates the same bridge surfaces
  on full shift execution-contract states in
  `ShiftContractStatePrimeCompatibilityProfileInstance`, using
  `canonicalShiftHeckeState -> shiftPrimeEmbedding` for the transported
  prime-address image;
- a third reusable route now lifts that same construction through
  `ObservableTransportWitness`, so any bundle carrier with a target-side
  transport and target-side prime image can inherit the witness-level bridge
  automatically;
- that third route is now also exercised concretely on the canonical abstract
  gauge/matter bundle carrier in
  `CanonicalObservableTransportPrimeCompatibilityProfileInstance`, using the
  canonical bundle transport witness together with
  `canonicalShiftHeckeState -> shiftPrimeEmbedding`;
- the transported canonical shift image is retained only through an explicit
  equality/audit path, not as the mask definition itself;
- the remaining gap is no longer “find any broader carrier”, and no longer
  “exercise the full `ObservableTransportWitness` lift concretely”: those now
  exist. The next gap is to widen beyond the canonical bundle leaf or to
  strengthen the continuum target. The AGMB continuum surface now uses a projected continuum
  observable, so the canonical instance compiles with a closure-honest
  `Gauge × basinLabel × mdlLevel × motifClass × eigenShadow` target, where
  `eigenShadow = (earth , hub)` is the first nontrivial preserved quotient of
  `eigenSummary`; a stronger continuum target would still be blocked because
  the current closure-derived law does not preserve `canonicalRGObservableOf`
  on the `CP` branch.

## Next seam

The next honest theorem targets are:

- identify which orbit-summary components, if any, are chamber-stable even
  though the full summary is not;
- test whether repeated transport induces stable orbit-style families on this
  summary carrier.
