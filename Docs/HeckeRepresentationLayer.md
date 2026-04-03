# Hecke, FRACTRAN, and the Representation Layer

## Scope

This note records the current repo-accurate boundary for Hecke/FRACTRAN-style
structure after the archived `Dashi and Physics Insights` thread was pulled
into the local DB on 2026-03-31.

The key correction is simple:

> Hecke/FRACTRAN belong first on the prime-lattice representation layer, not
> on the transported conserved-witness layer of the contractive dynamics.

This does not demote the Hecke lane. It places it on the right side of the
stack.

## The split

The current codebase already has two different kinds of structure:

- a representation layer:
  prime exponent vectors, SSP/Hecke scans, finite factor vectors, lattice
  coordinates, orbit/shell statistics;
- a contractive dynamics layer:
  admissible execution, projected-delta cone screens, MDL descent, basin
  preservation, coarse observables.

The archive makes the non-commutation explicit:

> the lattice/orbit side and the contractive-dynamics side are both real, but
> they are not yet the same conserved structure.

That is exactly what the recent canonical widening failures already showed in
the repo:

- `motifClass` is stable under the current closure-derived carrier law;
- raw `heckeSignature` is not;
- full `eigenSummary` is not.

## Why raw Hecke fails as a conserved charge

The failed widening attempt in the canonical abstract gauge/matter bundle is
not a nuisance. It is the correct mathematical signal.

The current closure-derived dynamics law is contractive and quotient-facing.
It is built to preserve admissibility, projected-delta cone structure, and a
small stable observable payload. A raw Hecke signature is finer-grained than
that payload.

So the honest statement is:

> a Hecke signature is currently a representation-layer diagnostic, not a
> proved conserved quantity of the contractive closure law.

Trying to force it into the conserved witness too early confuses:

- address/representation structure,
- with dynamics/invariance structure.

The obstruction is concrete on the canonical carrier. The bracket law
`x ↦ [CR , x]` sends `CP` to `CC` (see
`DASHI/Physics/Closure/CanonicalAbstractGaugeMatterInstance.agda` for the
carrier definitions), yet the Hecke signature reads its `b3` bit from the
`space1` coordinate of the shift geometry. `CP` is encoded with `space1=1`
while `CC` walks to `space1=0`, and the `p3` compatibility bit
(`DASHI/Physics/Closure/ShiftRGObservableInstance.agda` `shiftCompat p3`)
turns from `false` to `true` across that flow. The `b3` entry of
`HS.Sig15` therefore flips and the raw `heckeSignature` cannot stay equal.

## Where Hecke and FRACTRAN do belong

The archived thread sharpens the right placement.

### Hecke

Hecke belongs on a structured family of states or functions over a symmetry
domain:

- prime exponent lattice,
- quotient/orbit family,
- modular or transport-averaging correspondence,
- eigenstructure on that family.

In that role, a Hecke operator is closer to structured averaging over
admissible transport channels than to a literal conserved scalar attached to a
single contracting trajectory.

### FRACTRAN

FRACTRAN belongs with the same address language:

- prime-exponent updates,
- divisibility flow,
- p-adic/ultrametric addressing,
- multiplicative lattice coordinates.

So the current safe bridge is:

> FRACTRAN and Hecke are both natural on the prime-lattice representation
> layer.

That is the layer where Dashi and DuPont look closest.

## Dashi and DuPont

The strongest archived phrasing is worth preserving conceptually:

> Dashi and DuPont are equivalent at the state-address level, but not yet at
> the conserved-dynamics level.

Repo-facing interpretation:

- state-address level:
  prime vectors, SSP coordinates, factor embeddings, orbit/address grammar;
- conserved-dynamics level:
  what the closure-derived law actually preserves under admissible execution
  and coarse schedules.

That second layer remains narrower.

## Consequences for the current roadmap

This note changes the priority order in one narrow but important way.

Do not spend the next proof effort on:

- another direct raw-Hecke lift into the canonical conserved witness.

Do spend effort on:

- stronger/noncanonical dynamics-target pairings;
- a coarser quotient derived from the RG spectral data if one is genuinely
  stable;
- a representation-layer theorem surface for Hecke/FRACTRAN on prime-lattice
  objects;
- transport theorems only after the representation layer and the contractive
  layer are related by a real bridge.

The first local step of that representation-layer work is now landed in:

- [`ReverseHeckeRepresentation.md`](./ReverseHeckeRepresentation.md)
- [`Ontology/Hecke/ReverseRepresentation.agda`](../Ontology/Hecke/ReverseRepresentation.agda)

The second local step is now also landed:

- [`HeckeQuotientRepresentation.md`](./HeckeQuotientRepresentation.md)
- [`Ontology/Hecke/QuotientRepresentation.agda`](../Ontology/Hecke/QuotientRepresentation.agda)

The third local step is now also landed:

- [`HeckeCorrespondenceRepresentation.md`](./HeckeCorrespondenceRepresentation.md)
- [`Ontology/Hecke/CorrespondenceRepresentation.agda`](../Ontology/Hecke/CorrespondenceRepresentation.agda)
- [`Ontology/Hecke/FactorVecCorrespondence.agda`](../Ontology/Hecke/FactorVecCorrespondence.agda)

The fourth local step is now also landed:

- [`HeckeDefectCorrespondence.md`](./HeckeDefectCorrespondence.md)
- [`Ontology/Hecke/DefectCorrespondenceRepresentation.agda`](../Ontology/Hecke/DefectCorrespondenceRepresentation.agda)
- [`Ontology/Hecke/FactorVecDefectCorrespondence.agda`](../Ontology/Hecke/FactorVecDefectCorrespondence.agda)

The fifth local step is now also landed:

- [`HeckeDefectProfileCorrespondence.md`](./HeckeDefectProfileCorrespondence.md)
- [`HeckeChamberDefectCorrespondence.md`](./HeckeChamberDefectCorrespondence.md)
- [`Ontology/Hecke/FactorVecDefectProfileCorrespondence.agda`](../Ontology/Hecke/FactorVecDefectProfileCorrespondence.agda)
- [`Ontology/Hecke/FactorVecChamberDefectCorrespondence.agda`](../Ontology/Hecke/FactorVecChamberDefectCorrespondence.agda)

## Safe current claim

The strongest current claim the repo can support is:

> Hecke/FRACTRAN structure is real and important, but it is currently justified
> as representation-layer structure rather than as a conserved charge of the
> contractive closure dynamics.

## Full stack status

The current Hecke-side stack is now clearer than it was when this note started.
The repo has already moved beyond plain address and transport diagnostics.

### Layers already landed locally

- substrate:
  raw carriers such as `FactorVec`, prime coordinates, finite trace/state
  carriers;
- representation:
  address maps, prime-lattice coordinates, SSP-facing scans and embeddings;
- transport:
  positive, signed, and multi-lane transport families on the representation
  carrier;
- defect:
  reverse-Hecke discrepancy, scan-visible drift, and coarse defect classes;
- quotient:
  equality, support-mask, and quotient-facing Hecke surfaces, together with
  explicit no-go results for overly coarse signed-transport quotients;
- correspondence:
  finite sum-over-fiber Hecke operators on quotient classes, defect classes,
  and full defect profiles;
- exact chambers:
  legality-signature chambers for the current `PairMode` multi-lane transport
  family.

The first orbit-summary component is now constrained cleanly:

- the histogram-layer forced-stable / illegal count is a lower bound for the
  current orbit-summary `forcedStableCount` field;
- illegal entries are always Stable at the full defect-profile level, but not
  every Stable profile entry is forced by illegality.
- the bridge ladder is now packaged explicitly in
  `Ontology/Hecke/ForcedStableTransferBridge.agda`:
  exact-chamber illegal-count constancy,
  an abstract closure-to-shift transfer inequality,
  and the composed orbit-summary lower bound.
- above that bridge, the current certified representative set now carries a
  first genuinely collapse-free numeric quotient in
  `Ontology/Hecke/CertifiedRepresentativePersistence.agda`:
  on that finite certified domain, the Hecke-side `forcedStableCountOrbitP2`
  count already determines a small persistence tier
  (`reducedPersistence` or `saturatedPersistence`), and
  `Ontology/Hecke/DefectProfileCollapseFactorization.agda` now records the
  corresponding certified representative orbit-count factorization.
- the same certified persistence quotient now also factors through the full
  Hecke-side `DefectOrbitSummary` in
  `Ontology/Hecke/CertifiedRepresentativeOrbitSummaryPersistence.agda`:
  the current tier is recovered by projecting the summary's
  `forcedStableCount` field, so the repo now has a richer Hecke-summary
  factorization on the certified representative set without introducing a
  speculative new summary.
- the next honest refinement above collapse time is now landed in
  `Ontology/Hecke/DefectPersistenceRefinement.agda`:
  collapse time alone does not determine the exact certified `p2`
  orbit-pressure count, but collapse time plus one Hecke-side persistence
  refinement does. On the current certified set, `explicitWidth1` is the
  unique `lowStay` case, `explicitWidth3` and `denseComposed` are `highStay`,
  and the current anchored/immediate representatives are `nonStay`.
  This refinement still factors through the full `DefectOrbitSummary` only by
  way of its `forcedStableCount` field, so the saturated side is still not
  split by a richer Hecke-side invariant yet.
- that refinement has now been pushed one small step beyond the original
  certified finite set in `Ontology/Hecke/SupportCascadePersistence.agda`:
  the mixed-scale `supportCascade` stay-class also has exact
  `forcedStableCount = 15` at `p2`, so the saturated persistence side is not
  confined to the original certified prefix representatives.
- the positive refinement law is now also lifted to the full current
  generator taxonomy in
  `Ontology/Hecke/CurrentGeneratorPersistenceRefinement.agda`:
  every currently landed generator class now has an explicit current
  refinement and exact `p2` orbit-pressure value, with `supportCascade`
  joining the saturated stay branch.
- the matching negative boundary is now explicit in
  `Ontology/Hecke/CertifiedSaturatedForcedStableCollapse.agda`:
  every current saturated certified representative already has the same
  `forcedStableCount = 15`, so the present orbit-summary factorization
  through that field cannot separate the saturated side any further.
- that same negative boundary is now lifted to the full current generator
  scope in `Ontology/Hecke/CurrentSaturatedForcedStableCollapse.agda`:
  every currently saturated generator class still has
  `forcedStableCount = 15`, so the present `forcedStableCount`-based summary
  remains too coarse to distinguish the saturated side anywhere in the
  current taxonomy.
- the current whole-summary negative boundary is also explicit now:
  `Ontology/Hecke/CurrentSaturatedOrbitSummaryCollapse.agda` shows that the
  full currently landed `DefectOrbitSummary` already collapses on the current
  saturated branch, not only the extracted `forcedStableCount` field.
- the current refinement lane is therefore no longer "find more classes" or
  "add more representative scaffolding". It is "resolve the next saturated
  splitter". The long-compute modules
  `Ontology/Hecke/DefectOrbitSummaryRefinement.agda`,
  `Ontology/Hecke/TriadIndexedDefectOrbitSummaryRefinement.agda`,
  `Ontology/Hecke/CurrentSaturatedTriadHistogramSeparation.agda`, and
  `Ontology/Hecke/CurrentSaturatedSectorHistogramComputations.agda`
  now package that fixed-domain question directly.

## Current status line

The honest repo-accurate status is now:

> Layer 1 is closed on the current generator taxonomy, while Layer 2 remains
> open on the current saturated branch.

Expanded:

- closed:
  `generator -> collapse class -> stay refinement -> exact p2 pressure`
- open:
  `current saturated branch -> next separating invariant I₂`

So the next proof effort should stay tightly local:

- first, sector-by-sector separation on the packaged current-saturated
  histogram data;
- then, full triad-package separation if a sector split appears;
- otherwise, prove collapse of that refinement too and move one notch up in
  summary richness.
- recommended first pair order:
  `balancedCycle` vs `supportCascade`,
  `balancedComposed` vs `supportCascade`,
  then `denseComposed` vs `fullSupportCascade`.
- the fixed-domain comparison targets for that proof order are now packaged
  explicitly in
  `Ontology/Hecke/CurrentSaturatedPredictedPairComparisons.agda`.
- if the triad-histogram lane also collapses on those pairs, the next
  smallest fallback is now explicit rather than only implicit:
  `Ontology/Hecke/TriadSectorCorrelationRefinement.agda` packages the
  sector-correlation summary
  `(v₀·v₁, v₁·v₂, v₂·v₀)` above the ordered triad histogram, and the same
  predicted-pair module now carries correlation comparison targets as the next
  fixed-domain step after histogram collapse.
- archived context check:
  the canonical thread `Dashi and Physics Insights`
  (`69ca43a9-09fc-839b-8cc3-e5ce3868eef5`,
  canonical ID `ad17536d8eeb320106585654a0950424abafa93b`,
  source `db`) still records the earlier `Forced-Stable Transfer Bridge`
  as the best bridge-closing theorem candidate. That remains historically
  correct for the earlier Hecke/closure bridge phase, but it is no longer the
  tightest live bottleneck. The current repo state has moved one rung beyond
  that: Layer 2 is now a fixed-domain separator problem on the saturated
  branch.
- the stronger negative theorem is now also landed in
  `Ontology/Hecke/CurrentSaturatedOrbitSummaryCollapse.agda`:
  on the full current saturated generator set, the whole current
  `DefectOrbitSummary` at `p2` already collapses to the same fully stable
  summary
  `(15, 0, 0, 0, 0, 0)`.
  So the next honest separator cannot come from re-reading the currently
  landed orbit-summary fields more carefully; it has to come from a richer
  Hecke-side summary/package than the present `DefectOrbitSummary`, or from
  genuinely new generator classes not yet in the current taxonomy.
  The right interpretation is now:
  `3` is the generative radix of the recursive ternary hierarchy, while
  `15` is an emergent saturated value of the current fixed-prime orbit
  summary surface. A decomposition such as `15 = 9 + 6` is therefore a
  reasonable structural hypothesis to test, but not a theorem the repo has
  landed yet. A factorization such as `15 = 3 × 5` is now a comparably strong
  structural hypothesis: three triadic sectors times five symmetry-reduced
  local classes.
- four implementation surfaces now exist for that next step:
  `Ontology/Hecke/DefectOrbitSummaryRefinement.agda` packages the smallest
  histogram-style refinement above the current orbit summary, and
  `Ontology/Hecke/ForcedStableCountDecomposition.agda` packages both the
  current additive `9 + 6` candidate and the multiplicative `3 × 5`
  factorization on the saturated branch, and
  `Ontology/Hecke/TriadIndexedDefectOrbitSummaryRefinement.agda` packages the
  next triad-indexed refinement candidate, and
  `Ontology/Hecke/CurrentSaturatedPredictedPairComparisons.agda` packages the
  current fixed-domain pairwise comparison order for the Layer 2 speedrun,
  while `Ontology/Hecke/TriadSectorCorrelationRefinement.agda` packages the
  next correlation-level fallback if the triad histogram itself is exhausted.
  next candidate refinement above the flat histogram as a triad-indexed
  `3 × 5` surface. The fixed-domain specialization is now also explicit in
  `Ontology/Hecke/CurrentSaturatedTriadHistogramSeparation.agda`:
  the next honest question is whether that triad-indexed histogram separates
  any classes inside the already-classified current saturated taxonomy, or
  whether this refinement is exhausted too. The current-scope packaged-data
  companion is now also explicit in
  `Ontology/Hecke/CurrentSaturatedSectorHistogramComputations.agda`:
  it exposes named three-sector histogram packages for each current
  saturated class so the next proof step can test sector-level and whole-
  package separation directly on those computations. The repo now also
  packages the status boundary explicitly in
  `Ontology/Hecke/SaturatedInvariantRefinementStatus.agda`:
  Layer 1 is closed on the current generator taxonomy, while Layer 2 is the
  still-open invariant-refinement problem on the saturated branch.
  The repo now also carries
  `Ontology/Hecke/Layer2FiniteSearch.agda`
  as a deliberately thin helper above those surfaces: it packages the actual
  speedrun order
  (`sector -> package -> correlation` on the three predicted pairs)
  as a bounded finite search, rather than as another invariant layer.
  And it now also carries the zero-cost shell
  `Ontology/Hecke/Layer2FiniteSearchShell.agda`,
  which packages the same order with postulated targets only.
  That shell is the genuinely cheap Agda surface for validating the Layer 2
  control program without importing the histogram computations.
  To make the same control order usable outside Agda, the repo now also
  carries
  [`scripts/generate_layer2_long_compute_queue.py`](../scripts/generate_layer2_long_compute_queue.py),
  which now emits two separate batches:
  a compile-thin shell check batch and an offline-heavy three-pair replay
  batch, with optional `agda --parallel` command templates.
  It can also write batch artifacts to disk, including grouped
  offline-heavy-by-pair and offline-heavy-by-stage files for offline
  execution handoff.
  Those artifact directories now also carry `index.txt` and `index.json`
  summaries so the batch layout is self-describing.
  The repo now also carries
  [`scripts/render_layer2_batch_commands.py`](../scripts/render_layer2_batch_commands.py),
  which turns one of those emitted batch JSON files into executable command
  lines or a runnable shell script.
  It can also dedupe repeated identical command lines while preserving order.
  This is a queue emitter only, not a proof runner.
  Current operational boundary:
  the shell can be validated interactively, but the histogram-connected
  modules should still sit on the long-compute list rather than being
  re-validated in-session, because that class of Agda check has already
  proved expensive enough to destabilize the live session.
- the minimal fixed-prime witness-level bridge is now also landed in
  `Ontology/Hecke/ChamberToShiftWitnessBridge.agda`,
  where a closure-side illegal mask is compared only to a 15-entry
  forced-stable witness mask, with no larger state semantics attached.
- the closure-side profile feeding that bridge is now factored through
  `DASHI/Physics/Closure/PrimeCompatibilityProfile.agda`,
  so closure-native compatibility data can be turned into a prime embedding,
  illegal mask, and witness bridge without rewriting that construction.
- broader families that currently only expose a transported `State -> FactorVec`
  image can now use
  `DASHI/Physics/Closure/TransportedPrimeCompatibilityProfile.agda`
  to recover the same witness-level bridge surface by forgetting multiplicity
  and keeping only lane presence.
- the current classified collapse branches now also have explicit
  representative-order witnesses in
  `Ontology/Hecke/StaysVsImmediateRepresentativeOrder.agda`:
  the certified `staysOneMoreStep` and `exitToAnchored` representatives are
  both proved `≤` the current certified `immediateExit` representatives at the
  exact `p2` forced-stable orbit-count level, and the guarded numeric
  pressure predicates are discharged on those certified sets.
- that transported route is now exercised concretely on the canonical carrier
  in
  `DASHI/Physics/Closure/CanonicalTransportedPrimeCompatibilityProfileInstance.agda`,
  where the resulting prime embedding agrees with the closure-native profile
  on `CR/CP/CC` and therefore inherits the same witness-level inequality.
- the first genuinely broader concrete carrier now uses the full shift geometry
  state space directly in
  `DASHI/Physics/Closure/ShiftGeoVPrimeCompatibilityProfileInstance.agda`,
  so the transported-profile route and the orbit-side forced-stable bridge are
  no longer confined to the tiny canonical `CR/CP/CC` carrier.
- a second broader concrete family now lifts the same surfaces to the full
  shift execution-contract state carrier in
  `DASHI/Physics/Closure/ShiftContractStatePrimeCompatibilityProfileInstance.agda`
  by composing
  `canonicalShiftHeckeState -> shiftPrimeEmbedding`.
- bundle-level closure carriers can now inherit the same profile through
  `DASHI/Physics/Closure/ObservableTransportPrimeCompatibilityProfile.agda`
  whenever they already export an `ObservableTransportWitness` and a target-side
  prime embedding.
- that bundle-level route is now exercised concretely on the canonical abstract
  gauge/matter bundle carrier in
  `DASHI/Physics/Closure/CanonicalObservableTransportPrimeCompatibilityProfileInstance.agda`,
  by composing the canonical bundle transport witness with
  `canonicalShiftHeckeState -> shiftPrimeEmbedding`.
- the first canonical instance of that smaller bridge is now landed in
  `DASHI/Physics/Closure/CanonicalChamberToShiftWitnessBridgeInstance.agda`,
  so the repo now has a concrete proof of
  `illegalCount-chamber <= forcedStableCount-hist`
  on the canonical closure carrier. Its mask is now computed from a
  closure-native compatibility profile for `CR/CP/CC`, with the transported
  shift image kept only as an audit equality.
- the first concrete inhabitant of that bridge surface is now landed for the
  canonical closure carrier in
  `DASHI/Physics/Closure/CanonicalForcedStableTransferBridgeInstance.agda`,
  using the existing map
  `canonicalTransportState -> canonicalShiftHeckeState -> shiftPrimeEmbedding`.
- the remaining concrete gap at this layer is now narrower: the
  `ObservableTransportWitness` lift is now exercised concretely, and the AGMB continuum lane now
  uses a projected continuum observable rather than demanding preservation of
  the full transported `RGObservable`. The canonical instance therefore
  compiles again with a closure-honest continuum target
  (`Gauge × basinLabel × mdlLevel × motifClass × eigenShadow`), where
  `eigenShadow = (earth , hub)` is the first nontrivial preserved quotient of
  `eigenSummary`; stronger continuum targets remain blocked because the
  current closure-derived law does not preserve the raw eigen lane on the
  `CP` branch, now explicitly witnessed by
  `canonicalEigenLevel-CP-obstructed`.

### Layers still open in the strong sense

- compressed chamber quotients that survive proof rather than intuition;
- orbit families and reachability classes above the current exact chambers;
- algebra on correspondences:
  composition, closure, commutators, or semigroup structure;
- weighted or measured correspondences rather than bare uniform finite sums;
- spectral structure for those operators:
  eigenfunctions, eigenvalues, decomposition;
- any proven bridge from this representation-layer Hecke stack into the
  contractive physics bundle.

### Current location in the stack

The clean status line is now:

```text
SUBSTRATE
  ↓
REPRESENTATION
  ↓
TRANSPORT
  ↓
DEFECT
  ↓
QUOTIENT
  ↓
CORRESPONDENCE
  ↓
EXACT CHAMBERS
  ↓
COMPRESSED CHAMBERS / ORBITS / ALGEBRA / MEASURE / SPECTRAL
```

So the repo is no longer "approaching" chambers from the outside. It already
has exact chamber structure. The open work is what survives after chamber data
is compressed or aggregated into stronger laws.

## Immediate next seam

The next honest theorem target is still not another abstract transport or
correspondence interface.

The first histogram step is now landed:

- defect histograms are extracted from the 15-entry defect correspondence
  fiber;
- chamber-stability is now proved for the forced-stable / illegal component of
  that histogram.

So the new next seam is narrower:

- full defect-histogram constancy is now known to fail on the exact legality
  signature alone;
- a first orbit-style summary layer above the full defect-profile
  correspondence is now landed locally, and its full summary is also already
  known not to be determined by legality-signature data alone;
- replace the first concrete but transported/reflexive bridge inhabitant with a
  real inhabitant of the smaller witness-level bridge that computes a
  closure-native illegal mask rather than re-reading it from the transported
  shift image; the first canonical witness inhabitant is now landed with a
  closure-native mask on the three-generator carrier;
- generalize that closure-native witness beyond the tiny canonical carrier to a
  less hand-tabulated closure family;
- then test whether full defect-profile correspondences collapse to chamber
  invariants or only to weaker orbit-style families.

That is the shortest route from "representation gadget" to a stronger law on
the Hecke-side geometry.

### Reporter-readiness check

The current repo state is still a representation-layer theorem stack, not a
complete physics law. A minimal transported closure→shift schedule surface is
now explicit in
`DASHI/Physics/Closure/CanonicalClosureShiftScheduleBridge.agda`, but a
stronger raw-eigen closure/schedule bridge shape is obstructed on `CP`, and
the first attempted bridge on the larger projected charge
`Gauge × basinLabel × mdlLevel × motifClass × eigenShadow` is also obstructed
on `CP`. What now does bridge canonically is the smaller projected observable
`Gauge × basinLabel × motifClass`, via the new
`closureMotifToSchedule` / `sourceMotifToSchedule` theorems in
`CanonicalClosureShiftScheduleBridge.agda`. Raw `heckeSignature` and raw
`eigenSummary` still fail on the `CP` branch (see
`DASHI/Physics/Closure/CanonicalAbstractGaugeMatterInstance.agda`), and the
closure bundle itself still only conserves the projected observable
`Gauge × basinLabel × mdlLevel × motifClass × eigenShadow`. So the reporter
boundary has moved slightly but not across the physics line: we now have a
real closure→schedule bridge on a nontrivial quotient, but not yet a unified
transported physical observable. The safe external story remains
math/formal-methods: the representation layer, the contractive bundle, the
forced-stable inequality ladder, and now a canonical motif-level
closure→schedule bridge are all real; a physics-discovery claim is still
premature.

That boundary is now theorem-bearing in its own right rather than only
described in prose. `DASHI/Physics/Closure/CanonicalClosureCoarseObservable.agda`
formalizes `Gauge × basinLabel × motifClass` as the maximal currently bridged
canonical package, factors it through the landed schedule-side bridge, and
re-exports obstruction-facing wrappers for the wider bridge shapes that still
fail on `CP`.

### Closure target, stated strictly

The current repo state also sharpens what "physics closure" must eventually
mean here. It is not enough that isolated bridges compile or that one toy
carrier supports a quotient-level theorem. A completed closure would require:

- one carrier rather than separate closure-side, shift-side, and
  representation-side objects with open seams;
- one admissible law whose quotients/projections produce both the coarse
  causal story and the operator/defect story;
- one observable package split honestly into descending observables and
  non-descending defect/fibre structure;
- one RG/coarse-graining story internal to that same law;
- no unresolved bridge theorem between those layers.

The present canonical results already show the shape of that target. The
closure law behaves like a quotient selector:

- `Gauge × basinLabel × motifClass` survives the closure→schedule bridge;
- `mdlLevel`, `eigenShadow` at the bridge level, raw `eigenSummary`, and raw
  `heckeSignature` do not.

The fibre-control lane also advanced beyond witness-only separation.
`CanonicalClosureFibreOrbitSummaryControl.agda` now proves that, on the
canonical coarse fibre, equality of the `p2` orbit-summary coordinate forces
equality of `eigenShadowField`. So `p2` is now a genuine control surface on
that carrier rather than only a single separating witness. That control has
also now been packaged as an explicit quotient-facing surface in the same
module: `P2EigenShadowFactorLaw` with the canonical inhabitant
`canonicalP2EigenShadowFactorLaw`.

The same module now carries the first parallel control result for the Hecke
side itself: on the canonical coarse fibre, equality of the `p2`
orbit-summary coordinate also forces equality of `heckeField`. So the first
nontrivial Hecke/eigen fibre controls now share the same canonical
orbit-summary surface.
That Hecke control is also now packaged explicitly as
`P2HeckeFactorLaw` with the canonical inhabitant
`canonicalP2HeckeFactorLaw`.

The bridge/witness stack has also been replayed on a broader noncanonical
carrier in
`DASHI/Physics/Closure/ShiftContractObservableTransportPrimeCompatibilityProfileInstance.agda`.
That result does not yet lift the coarse observable package or `p2` theorem
off the tiny canonical fibre, but it does show that the
observable-transport/prime-compatibility surface survives on full
`ShiftContractState`, not only on `CR/CP/CC`.

That broader replay has now been strengthened one notch as well.
`DASHI/Physics/Closure/ShiftContractCoarseObservable.agda` packages the same
maximal currently bridged coarse observable surface on full
`ShiftContractState`, factoring it through the observable-transport witness
and the noncanonical bundle observable surface. So the coarse package is no
longer canonical-only, even though the fibre-control theorems still are.

The same-carrier generator lane is also no longer only a pile of ad hoc
examples. `DASHI/Physics/Closure/ShiftContractStateFamily.agda` now packages a
repo-native family schema on the live `ShiftContractState` carrier itself: the
coarse surface is fixed as `π-mdl-max`, the fine surface is the transported
prime image, and the cyclic source branch is exposed uniformly through a
generic family record plus a cyclic-3 specialization. The currently landed
width-1, width-2, and width-3 triadic families now inhabit that shared
surface directly.
`DASHI/Physics/Closure/ShiftContractTriadic3CycleInstance.agda` now adds the
first fully concrete balanced-cycle inhabitant of that search pattern on the
live carrier: with head fixed at `pos`, the tail cycle
`(pos , zer , neg) -> (zer , neg , pos) -> (neg , pos , zer)` preserves
`π-mdl-max` and still splits pairwise at the transported prime image.
`DASHI/Physics/Closure/ShiftContractBalancedComposedFamily.agda` now shows the
same balanced cycle is also reachable through the composed-generator lane:
starting from `fullSupport`, vary one cut mask and one neg-restore mask, and
the resulting ternary interaction reconstructs the balanced 3-cycle exactly.

The same seam now also has its first genuinely compositional generator.
`DASHI/Physics/Closure/ShiftContractComposedFamily.agda` defines a ternary
interaction rule on the live carrier itself, combining a shared base state, a
varying cut mask, and a shared restore mask. On the current carrier that rule
recovers the dense width-three cyclic branch exactly. So the generator search
is no longer limited to hand-written explicit families; there is now a
theorem-bearing state-building surface as well.
`DASHI/Physics/Closure/ShiftContractParametricTrajectoryCompositionFamily.agda`
now packages the successful 3-state prefixes from that search into one
normalized generator-class interface: explicit cyclic, balanced cyclic,
dense composed, balanced composed, and anchored trajectory.
`DASHI/Physics/Closure/ShiftContractGeneratorFourthStepBoundary.agda` now
adds the first reusable live fourth-step classifier above that interface:
anchored trajectory and explicit width-two are certified fourth-step exits;
balanced explicit/composed cycles are certified exits into the anchored
branch; explicit width-three and dense composed are certified to stay in the
same `π-mdl-max` fibre for one more live step.
`DASHI/Physics/Closure/ShiftContractMixedScaleTrajectoryFamily.agda` now
packages the mixed-scale trajectory branch itself as one normalized generator
surface above those same-fibre prefixes: the dense support cascade is the
canonical stay-then-exit family, and the full-support cascade is the
canonical immediate-exit family.
`DASHI/Physics/Closure/ShiftContractGeneratorTaxonomy.agda` now ties the two
normalized branches together into one higher-level surface: prefix families
remain indexed by generator class with explicit fourth-step shape labels,
while mixed-scale generators are exposed through their own normalized family
classes rather than left as parallel ad hoc modules.
`DASHI/Physics/Closure/ShiftContractCollapseTime.agda` now promotes that
taxonomy to a coarse collapse-time observable on generator classes:
`immediateExit`, `exitToAnchored`, and `staysOneMoreStep`.
`explicitWidth1` is now classified on the prefix side as `staysOneMoreStep`,
so the current prefix taxonomy no longer carries a `boundaryUnknown` hole.
`Ontology/Hecke/DefectOrbitCollapseBridge.agda` then adds
the first honest Hecke-side bridge from that observable: it chooses one
representative live `ShiftContractState` per generator class and reuses the
already-landed `illegalCount <= forcedStableCount_orbit` ladder at `p2`.
That is deliberately a weak lower-bound bridge, not yet a full
collapse-time/persistence identification.
`Ontology/Hecke/DefectOrbitCollapsePressure.agda` now packages the next
coarse Hecke-side layer above that bridge: collapse class induces a
three-tier pressure classification, and each generator class now has a named
representative `p2` pressure summary carrying the same orbit lower bound.
`Ontology/Hecke/DefectProfileCollapseFactorization.agda` then lands the first
explicit factorization scaffold above that layer: on the current classified
generator set, collapse time factors through the coarse defect-pressure
summary. This is still weaker than a Hecke-determined defect-profile quotient
theorem, but it turns the closure-side taxonomy into a theorem-bearing
collapse-to-pressure dictionary rather than leaving it as prose.
`Ontology/Hecke/StaysOneMoreStepRepresentativeComputations.agda` now makes
the stay-class side explicit rather than implicit: each certified
`staysOneMoreStep` class now carries a chosen representative state, a
transported prime image, a computed `p2` orbit summary, and the inherited
low-pressure tier. `Ontology/Hecke/DefectOrbitPressureOrder.agda` then adds
the first actual order theorem above that dictionary:
`staysOneMoreStep ≤ exitToAnchored ≤ immediateExit` as an ordered pressure
law on the current coarse pressure classes. This is still not a numeric orbit
pressure bound, but it is stronger than the earlier representative-state
lower-bound surface.
The next stronger theorem surfaces are now explicit and guarded rather than
left as prose. `Ontology/Hecke/DefectOrbitPressureOrder.agda` exposes
success-predicate interfaces for numeric orbit-pressure bounds, and
`Ontology/Hecke/DefectProfileCollapseFactorization.agda` now also carries the
corresponding guarded summary-factorization surfaces for a future
Hecke-determined defect-summary quotient. `Ontology/Hecke/ImmediateExitRepresentativeComputations.agda`
now mirrors the stay-class computation module on the immediate-exit side, so
both ends of the current collapse-to-pressure order have named representative
`p2` computation surfaces. `Ontology/Hecke/ExitToAnchoredRepresentativeComputations.agda`
now does the same for the intermediate `exitToAnchored` branch. The current
exact `p2` counts are now partly normalized on that three-way split:
all currently classified `immediateExit` and `exitToAnchored`
representatives sit at `illegalCountP2 = 15` and
`forcedStableCountOrbitP2 = 15`, while the current stay branch separates:
`explicitWidth1` has `forcedStableCountOrbitP2 = 2`, but
`explicitWidth3` and `denseComposed` already sit at `15`.

The same broader carrier now also has the first matching fibre vocabulary:
`DASHI/Physics/Closure/ShiftContractCoarseFibre.agda` defines the thin fibre
over that coarse package, and
`DASHI/Physics/Closure/ShiftContractCoarseFibreFields.agda` lifts the first
noncanonical `heckeField`, `eigenField`, `eigenShadowField`, `primeField`,
and count/orbit-summary fields onto it. So the remaining noncanonical gap is
no longer representational; it is theorem-bearing control.

That control gap is now theorem-bearing on the negative side as well.
`DASHI/Physics/Closure/ShiftContractNoncanonicalP2ControlObstruction.agda`
proves that the current broader coarse package is too weak for a
canonical-style `p2` factor law: two explicit `ShiftContractState` values have
the same `π-max` image but different transported prime images. So the next
noncanonical positive attempt has to strengthen the invariant package itself,
not just replay the canonical `p2` recipe.

The candidate search above that coarse package has now moved one notch.
`DASHI/Physics/Closure/ShiftContractMdlLevelCoarseObservable.agda`
and `DASHI/Physics/Closure/ShiftContractMdlLevelCoarseFibre.agda` now package
the cheapest aligned strengthening,
`Nat × (Gauge × basinLabel × motifClass)`, as a reusable normalized surface
with its own thin fibre. The same counterexample pair that obstructed the old
`π-max` quotient is already separated there, and
`DASHI/Physics/Closure/ShiftContractMdlLevelCoarseFibreFields.agda` now lifts
the first Hecke/eigen/prime/count/orbit-summary field vocabulary onto that
stronger fibre. `DASHI/Physics/Closure/ShiftContractMdlLevelP2ControlAttempt.agda`
then packages the narrowest positive theorem currently supported there:
equality of the normalized package determines both its `mdlLevel` coordinate
and its old coarse observable, while
`DASHI/Physics/Closure/ShiftContractNoncanonicalMdlP2Control.agda` still marks
the missing stronger step to prime-image or orbit-summary control.
`DASHI/Physics/Closure/ShiftContractMdlLevelCounterexampleAudit.agda` records
that the original coarse counterexample pair is no longer the active blocker
on this stronger surface. `DASHI/Physics/Closure/ShiftContractEigenShadowNormalizedPackage.agda`
and `DASHI/Physics/Closure/ShiftContractEigenShadowP2ControlCandidate.agda`
now do the same one rung higher for `eigenShadow × π-max`, while
`DASHI/Physics/Closure/ShiftContractRGObservableProjection.agda` keeps the
full normalized shift RG observable projection as an upper-bound reference
surface. `DASHI/Physics/Closure/ShiftContractMdlLevelOrbitSummaryControlAttempt.agda`
now adds the first normalized intermediate theorem on that stronger fibre:
prime equality already forces equality of the `p2` orbit-summary coordinate.
`DASHI/Physics/Closure/ShiftContractMdlLevelP2PrimeBridge.agda` strengthens
that same bridge one notch by packaging the resulting
orbit-summary coordinate consequences explicitly:
`forcedStableCount`, `motifChangeCount`, `totalDrift`,
`repatterningCount`, `contractiveCount`, and `expansiveCount`.
`DASHI/Physics/Closure/ShiftContractMdlLevelPrimeImageSubfamilyAttempt.agda`
also shows that the subfamily route is honest, albeit still tiny: on the
explicit singleton family around `coarseCounterexampleLeft`, equality of
`π-mdl-max` already forces equality of transported prime image.
`DASHI/Physics/Closure/ShiftContractMdlLevelPrimeImageSubfamilyRefinement.agda`
now wraps the same in-tree witness set into an explicit two-point family
`{ coarseCounterexampleLeft , coarseCounterexampleRight }`: the same-state
cases still satisfy prime-image equality, while the mixed case is rejected
already at `π-mdl-max`.
`DASHI/Physics/Closure/ShiftContractMdlLevelWitnessSearchAudit.agda` now
packages the bounded same-carrier search state explicitly: among the current
in-repo `ShiftContractState` witnesses, the old coarse pair is retired, the
certified prime-image subfamily is still only that singleton, and no fresh
equal-`π-mdl-max` / unequal-prime-image pair has yet been recovered.
`DASHI/Physics/Closure/ShiftContractMdlLevelWitnessSourceAudit.agda` now makes
that exhaustion boundary explicit as a separate source audit: the retired pair,
singleton subfamily, and current bounded witness-search wrappers are all
checked pools, and none has yet produced a fresh same-carrier witness.
`DASHI/Physics/Closure/ShiftContractMdlLevelExplicitStateSearchAudit.agda`
packages the most obvious direct explicit-state pool on the actual
`ShiftContractState` carrier itself: the retired coarse pair, the one-hot
states, and the direct neg/pos tail patterns. That pool is no longer globally
exhausted, because `DASHI/Physics/Closure/ShiftContractTriadicFamily.agda`
now shows that the three one-hot states become a genuine same-carrier family
once they are treated triadically rather than pairwise: `π-mdl-max` is
constant across the family, while the transported prime images are pairwise
distinct. `DASHI/Physics/Closure/ShiftContractAnchoredTriadicFamily.agda`
pushes that one rung further by fixing the coarse head and rotating a second
active tail coordinate: support width two now also survives as a triadic
same-carrier family with constant `π-mdl-max` and pairwise distinct prime
images. `DASHI/Physics/Closure/ShiftContractAnchoredTrajectoryFamily.agda`
then turns that same support-width-two source into the first live-step family
on the seam: starting from the broadest anchored state, the first three
trajectory states stay in one `π-mdl-max` fibre while their transported prime
images stay pairwise distinct, and the next live step exits that fibre by
collapsing to the one-hot fixed point.
`DASHI/Physics/Closure/ShiftContractDenseTriadicFamily.agda` now shows this is
not just a width-one/width-two effect: support width three also admits a
same-carrier triadic family with constant `π-mdl-max` and pairwise distinct
prime images.
`DASHI/Physics/Closure/ShiftContractSupportCascadeTrajectory.agda` now adds
the first mixed-scale live trajectory on the same seam: a dense seed gives one
same-fibre width-three step, then exits successively through the anchored and
one-hot fibres as the live dynamics contracts support width from 3 to 2 to 1.
`DASHI/Physics/Closure/ShiftContractParametricTriadicFamily.agda` now
normalizes the positive explicit cyclic branch itself into one width-indexed
surface over support widths 1, 2, and 3.
`DASHI/Physics/Closure/ShiftContractFullSupportTrajectory.agda` then adds a
distinct trajectory source above that branch: the full-support seed cascades
4 -> 3 -> 2 -> 1 under the live shift step.
`DASHI/Physics/Closure/ShiftContractTailPatternTrajectoryObstruction.agda`
closes the obvious negative trajectory branch beside it: the direct neg/pos
tail-sign seeds leave the `π-mdl-max` fibre immediately under the same live
step.
`DASHI/Physics/Closure/ShiftContractMdlLevelChi2WitnessAudit.agda` closes one
bounded search path by recording that the current chi2 witness pool lives on
the wrong carrier for this seam.
On the prepared fallback branch,
`DASHI/Physics/Closure/ShiftContractEigenShadowOrbitSummaryObstruction.agda`
now turns the old packaging-level warning into a theorem-bearing obstruction:
even equality on the normalized `eigenShadow × π-max` surface does not force
equality of the `p2` orbit-summary key on the canonical witness pair.
`DASHI/Physics/Closure/ShiftContractEigenShadowOrbitSummaryControlAttempt.agda`
then packages that as a direct no-go schema: any attempted control theorem
from the normalized `eigenShadow × π-max` surface to the canonical `p2`
orbit-summary key collapses on the CP/CC witness pair.
So the next noncanonical theorem attempt is no longer "find some stronger
package"; it is specifically to find the new witness or prove the first
genuine control theorem from the now-formalized `mdlLevel × π-max`
surface into prime-image data itself.

That changes the nature of the problem. The repo is no longer in a nearby
representation-widening phase here. It is now in a source-of-states phase.
The eliminated options are now explicit, modulo that new triadic one-hot
exception:

- the old local coarse obstruction pair;
- the current bounded same-carrier witness wrappers;
- pairwise probes on the direct explicit-state pool on `ShiftContractState`;
- the immediate representation-level fallback
  `eigenShadow × π-max` at the canonical `p2` seam.

So the remaining search space is no longer "more small perturbations" or
"another nearby quotient". It is:

- structured same-carrier families generated by a rule;
- trajectory-generated families under the available dynamics;
- or mixed-scale families whose normalized `π-mdl-max` image stays fixed while
  transported prime image varies.

The derived constraints are now sharper than that broad description.
Any fresh same-carrier family on this seam should satisfy:

- coarse equality:
  all states stay in one `π-mdl-max` fibre;
- fine separation:
  at least one family direction survives transported prime-image extraction;
- kernel discipline:
  the active variation lies in
  `ker(π-mdl-max) \ ker(primeImage)`;
- support discipline:
  direct tail-only probes are still weak, but both one-hot and anchored
  support-width-two states are now known to work once they are assembled into
  triadic families instead of pairs, and support width three now works too;
  by contrast, the direct neg/pos tail-sign seeds now fail dynamically as well
  by leaving the fibre in one live step;
- symmetry discipline:
  the family should not be generated by a single pairwise involution or simple
  reflection.

That last point matters now. The current audits have effectively eliminated the
obvious pairwise constructions, and the repo now has a concrete witness that a
triadic family escapes that collapse. Three states are still not proved
necessary, but the current seam has a real theorem-bearing triadic source and
still kills the nearby two-point/reflection-level options.

That is a stronger conclusion than the earlier obstruction notes. It means the
repo has already ruled out the obvious local and representation-level sources
for this seam, and it now also has positive static, dynamic, and mixed-scale
sources, so the next real leverage is a genuinely new family generator rather
than another one-off witness probe.

So the next theorem-bearing move is to define the maximal
closure-invariant observable package explicitly and treat the non-descending
Hecke/eigen channels as lawful defect or fibre data rather than as failed
would-be invariants.

### Observable split at the current boundary

The repo can now describe the closure-side observable lattice more sharply than
before.

#### Base physics

The downward-closed family of currently proved closure-invariant observables is
generated by:

- `Gauge × basinLabel × motifClass`

and its subquotients. This is the strongest currently proved package that
bridges canonically from the closure carrier to the schedule side.

#### Fibre/defect data

The following channels are still structured, but they do not descend through
the current closure quotient:

- bridge-level `mdlLevel`
- bridge-level `eigenShadow`
- raw `eigenSummary`
- raw `heckeSignature`
- finer defect/correspondence profile data on the Hecke side

These should now be treated as fields on the fibres above the coarse quotient,
not as failed base observables. In other words, the current closure law keeps
them as internal fine structure rather than erasing them as noise.

The next clean theorem surface is therefore:

- define the coarse projection
  `π : ClosureState -> Gauge × basinLabel × motifClass`;
- define the thin fibre
  `Fibre(q) = Σ ClosureState (λ x -> π x ≡ q)`;
- lift Hecke/eigen observables to fibre-indexed fields;
- prove their variation is governed by already-landed defect or
  correspondence laws rather than being arbitrary.

That first fibre surface is now concrete on the canonical carrier:

- `DASHI/Physics/Closure/CanonicalClosureFibre.agda` defines the thin fibre
  over the coarse quotient `Gauge × basinLabel × motifClass`;
- `DASHI/Physics/Closure/CanonicalClosureFibreFields.agda` exposes
  `heckeField`, `eigenField`, `eigenShadowField`, and the transported
  `primeField` on each fibre;
- the first control law is now implemented at the forced-stable/illegal-count
  level: if two fibre representatives land in the same exact pair chamber on
  the transported prime side, then their forced-stable and illegal counts are
  equal.
- `DASHI/Physics/Closure/CanonicalClosureFibreDefectFactorization.agda`
  now lifts the same fibre representatives into explicit
  defect-profile/histogram carriers:
  `defectProfileEntryField`, `defectHistogramField`, and
  `orbitSummaryField`. The current theorem surface is still intentionally
  honest: illegal chamber entries force stable/zero-drift profile behaviour,
  and the fibre-side forced-stable count is bounded above by the richer
  orbit-summary stable count.
- `DASHI/Physics/Closure/CanonicalClosureFibreEigenShadowObstruction.agda`
  sharpens the classification further: `eigenShadow` already varies inside the
  canonical coarse fibre itself. Concretely, `CR` and `CP` inhabit the same
  coarse fibre `Gauge × basinLabel × motifClass`, but their
  `eigenShadowField` values are unequal.
- `DASHI/Physics/Closure/CanonicalClosureFibreOrbitSummaryControl.agda`
  gives the first concrete detection theorem for that variation: the same
  `CR`/`CP` pair is already separated by the richer orbit-summary family on
  the transported prime carrier, and in fact the single `p2` orbit-summary
  coordinate already suffices.

The strongest eventual version of that statement would be a factorization law:
the Hecke/eigen fibre fields should factor through a defect-profile or
histogram carrier on each fibre. The immediate next target is weaker and more
realistic: show that the actual Hecke/eigen fibre fields themselves, not only
their forced-stable count projections, are controlled by or factor through
those richer defect-profile/histogram carriers. For `eigenShadow`, that is now
the only honest next move: it has been ruled out as a descending coarse
observable on the canonical fibre, but it is at least detected by the richer
orbit-summary carrier. The next structural question is therefore whether
`eigenShadow` variation is controlled by a specific orbit-summary quotient,
not merely by the existence of some separating summary in the full family.

#### Scaffolding

The remaining representation gadgets are still primarily proof and diagnostic
machinery:

- raw prime-address carriers such as `FactorVec`
- support-mask and other overcoarse quotient probes
- synthetic local transport shells used to expose obstruction structure
- raw correspondence packaging before a quotient- or chamber-law is extracted

They remain essential to the theorem pipeline, but they are not yet part of
the physical quotient without an additional descent or invariance theorem.
