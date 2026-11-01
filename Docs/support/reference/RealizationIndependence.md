# Realization-Independent Theorem Scope

The strongest realization-dependent seams remaining in the physics closure
inventory are:

1. The canonical `ShiftLorentzEmergenceInstance` still ties geometry to the
   specific `(m=1,k=3)` carrier, a canonical cone point, and the explicit
   `ShiftCoarseHead` predicate. The key basin hypothesis is still the
   shift-specific clause `ShiftInBasin x ≡ ShiftCoarseHead x ≡ pos ∷ []`.
2. The RG lane in
   [`ShiftRGObservableInstance.agda`](../DASHI/Physics/Closure/ShiftRGObservableInstance.agda)
   still builds cones, basins, and admissibility from the specific shift
   execution contract; the witnesses refer to canonical bridges rather than an
   abstract carrier.
3. The current universality witnesses are still derived from concrete
   `shiftCoarse` / `shiftCoarseAlt` choices rather than from a generic
   cone-preserving coarse pair and offset schedule.

## What a realization-independent theorem would need

- **Hypotheses**: an abstract contract `C` with a carrier `State`, admissible
  coarse maps `coarseA`, `coarseB`, an admissibility predicate tied to a
  generic cone-like witness, and an offset map that can be specialized to
  `step` or any other schedule carrier.
- **Invariant carrier**: an additive or geometric carrier `A` supporting a
  cone `Cone` with a quadratic `Q` such that cone membership is preserved by
  both coarse maps and by the offseted evolution.
- **Admissible maps**: abstract versions of `shiftCoarse` and
  `shiftCoarseAlt`, together with admissibility-preserving witnesses and a
  commutation lemma relating the two schedules up to the offset.
- **Instantiations**: explicit evidence that the canonical shift instance
  satisfies those abstract hypotheses without baking the theorem back into
  `Vec ℤ 4`.

## Current gap

The gap is not that the repo lacks an execution or admissibility surface from
zero. The gap is that the current strongest witnesses are still:

- canonical,
- realization-specific,
- or partially trivialized.

In particular, the shift instance currently hardwires placeholder quantities
like constant arrow/eigen summaries, while the basin witness becomes
nontrivial only on the canonical `(1,3)` carrier.

So the realization-independent theorem target is:

> replace canonical and partially trivial shift witnesses with abstract
> hypotheses and reusable transport lemmas, then show that the canonical shift
> instance is only one inhabitant of that abstract surface.

## Current minimal theorem surface

The basic offset-universality surface is already present:

- [`RGObservableInvariance.agda`](../DASHI/Physics/Closure/RGObservableInvariance.agda)
  defines `ObservableRGOffsetUniversality`;
- [`ShiftRGObservableInstance.agda`](../DASHI/Physics/Closure/ShiftRGObservableInstance.agda)
  instantiates it as `shiftObservableRGOffsetUniversality`.

So the next realization-independent promotion is no longer to invent that
record. It is to connect that already-landed offset-universality surface to
the abstract gauge/matter bundle story, rather than leaving the two abstractions
adjacent but separate.

That connection is now present at the first honest level:

- `AbstractGaugeMatterBundle.agda` exports a conversion from
  `GaugeMatterRecoveryTheorem` into `ObservableRGOffsetUniversality`;
- the canonical abstract bundle instance exposes that converted offset witness.

So the remaining realization-independent gap is no longer “offset universality
exists somewhere else.” It is to make the bundle-level offset witness less
canonical and less tied to the current concrete inhabitant.

The next abstraction surface above the shift instance is now explicit:

- [`RGObservableInvariance.agda`](../DASHI/Physics/Closure/RGObservableInvariance.agda)
  now defines `ProjectionDeltaCompatibility`, an abstract record for:
  - two admissible projection schedules,
  - a shared cone witness on projected deltas,
  - and an observable universality law between those schedules.
- [`ShiftRGObservableInstance.agda`](../DASHI/Physics/Closure/ShiftRGObservableInstance.agda)
  instantiates it as `shiftProjectionDeltaCompatibility` using the live
  `shiftCoarse`, `shiftCoarseAlt`, and cone transport witnesses.

That closes the first honest promotion step for the projection/Δ lane:
the abstraction now exists in code and is inhabited by the live shift RG
surface, instead of only being described in docs.

That promotion has now been lifted one level higher:

- `AbstractGaugeMatterBundle.agda` now exports
  `toProjectionDeltaCompatibility`, deriving the same abstraction from a
  bundle-level `GaugeMatterRecoveryTheorem`;
- the canonical abstract bundle instance exposes that converted witness as
  `canonicalBundleProjectionDeltaCompatibility`.
- the canonical instance now also exposes a quotient-sensitive variant over the
  transported live `RGObservable`, using the shift RG lane’s own observable
  quotient rather than plain equality.
- the canonical instance now also exposes a transport-attached target-side
  witness on the live shift carrier, so the carrier/dynamics side is no longer
  limited to bundle-side reconstructed schedules only.
- that target-side witness is now backed by a reusable
  `TransportedProjectionDeltaWitness` surface in
  `AbstractGaugeMatterBundle.agda`, rather than existing only as a
  canonical one-off export.
- the canonical instance now inhabits that transported surface with both the
  base and alternate phase schedule families on the live shift carrier.
- the abstract recovery theorem itself now also requires one transported
  projection/Δ witness, so target-side schedule compatibility is no longer
  only a parallel theorem export beside the recovery surface;
- the recovery theorem now carries both the base and alternate transported
  phase families directly, so this part of the abstraction is no longer
  hard-coded to a single target-side schedule pair.

So the remaining realization-independent gap is narrower again:
the projection/Δ theorem is no longer trapped at the shift RG layer, and it is
no longer only inhabited canonically on the bundle side.

The first honest noncanonical inhabitant is now landed too:

- [`ShiftContractProjectionDeltaCompatibility.agda`](../DASHI/Physics/Closure/ShiftContractProjectionDeltaCompatibility.agda)
  exports `shiftContractProjectionDeltaCompatibility`, a direct
  `ProjectionDeltaCompatibility` witness on the broader live
  `ShiftContractState` carrier using the noncanonical observable replay from
  `ShiftContractObservableTransportPrimeCompatibilityProfileInstance.agda`.

So the remaining realization-independent gap is no longer “find any
noncanonical inhabitant at all.” It is narrower:

- widen beyond the first `ShiftContractState` inhabitant;
- reduce dependence on the current shift-RG-flavored admissibility and cone
  transport;
- and eventually promote a broader noncanonical transported or bundle-level
  recovery witness.
