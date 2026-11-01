# Dark-sector collider formalism

This tranche adds the collider-observation adapter missing from the existing hidden-sector quotient, Higgs-order-parameter, metastability, and coarse-projection work.

The exact finite linked chain is:

```text
gauge-singlet portal
-> visible portal decay graph
-> indexed finite persistence datum
-> lifetime-matched boosted displacement
-> displacement-matched reconstructed vertex
-> prompt-trigger rejection
-> dedicated LLP-trigger acceptance.
```

`LinkedColliderChainExact.agda` carries these stages dependently. Each boosted stage is indexed by its metastable stage and proves that its proper-lifetime units agree with the preceding lifetime datum. Each detection stage is indexed by that boosted stage and proves that the reconstructed displacement agrees with the boosted displacement before the two trigger decisions are attached. This replaces the weaker interpretation in which unrelated canonical witnesses merely occupied fields of one outer product record.

The implementation deliberately does **not** identify a displaced decay with delayed wave-function collapse. The physical interpretation is an unstable excitation with finite width, a corresponding proper lifetime, Lorentz boost, and decay into detector-visible daughters.

## Modules

```text
DASHI/Physics/DarkSector/
  SectorCarrier.agda
  GaugeSingletPortal.agda
  HiggsPortalDecay.agda
  MetastableLifetime.agda
  BoostedDecayGeometry.agda
  DisplacedVertex.agda
  TriggerCensoring.agda
  LinkedColliderChainExact.agda
  DarkSectorColliderSourceAtlas.agda
  DarkSectorColliderBoundary.agda
  DarkSectorColliderRegression.agda
  Everything.agda
```

## Sector and portal typing

`SectorCarrier.agda` separates:

```text
visible versus dark sector;
Standard-Model singlet versus charged state;
sector membership versus detector visibility;
visible versus invisible decay daughters.
```

A dark singlet can therefore be detector-visible through its decay products without being assigned an ordinary Standard-Model charge.

`GaugeSingletPortal.agda` represents a portal as an interaction operator with invariant visible and dark factors. The canonical quadratic scalar portal is admitted only when both factors are singlets. Observation projections remain a different type.

The finite witness mirrors the schematic interaction

```text
-lambda_(H chi) (H dagger H) chi^2,
```

but does not calculate a Wilson coefficient or branching fraction.

## Decay topology and lifetime

`HiggsPortalDecay.agda` contains the two typed chains

```text
pp -> h -> chi chi -> visible daughters
pp -> h -> chi chi -> invisible daughters.
```

`MetastableLifetime.agda` separates deterministic finite persistence from the continuum stochastic law. Its scaled reciprocal witness is

```text
widthUnits * lifetimeUnits = reciprocalScale
3 * 4 = 12.
```

This is a finite exact analogue of `tau = Gamma^(-1)`, not a derivation of an exponential decay distribution.

## Boosted geometry and vertex reconstruction

`BoostedDecayGeometry.agda` keeps the three factors in

```text
ell = beta gamma c tau
```

typed separately. The canonical scaled witness is

```text
2 * 1 * 4 = 8.
```

`DisplacedVertex.agda` checks:

```text
minimum displacement <= reconstructed displacement <= maximum displacement;
visible daughter multiplicity;
vertex-quality acceptance.
```

The canonical event has interaction point `0`, decay point `8`, accepted window `[2,10]`, two daughter tracks, and a passing quality flag. Prompt and outside-detector controls fail the displaced predicate for different reasons.

## Dependent chain and trigger censoring

`LinkedColliderChainExact.agda` defines four nested stages:

```text
PortalProduction
MetastablePropagation production
BoostedPropagation metastable
ReconstructedDetection boosted.
```

The canonical chain proves, within one dependent object:

```text
portalAllowed portal = true
widthUnits * lifetimeUnits = reciprocalScale
boost.properLifetimeUnits = lifetime.lifetimeUnits
vertexDisplacement event = laboratoryDisplacement boost
isDisplacedVertex event = true
promptTrigger event = rejectEvent
llpTrigger event = acceptEvent.
```

An allowed portal alone still does not generate the downstream stages; the later indexed records require their own declared data and proofs.

`TriggerCensoring.agda` also proves the finite acceptance no-go:

```text
recordedSignalCount 5 2 0
=
recordedSignalCount 9 1 0
=
0.
```

Thus a recorded null at zero acceptance cannot identify the underlying production rate. In experimental notation, a null result constrains a production-times-branching-times-acceptance product, not production alone.

## Cross-pollination with the complete attached formalism

The same branch adds:

```text
FiniteHistoryOrientationExact.agda
HistoryWeightFiltrationExact.agda
FiniteHistoryFunctionalExact.agda
FormalReceiptBoundaryExact.agda
FiniteResidueCycleReachabilityExact.agda
FiniteWeightedTernaryKernelExact.agda
TernaryKernelQuotientLyapunovExact.agda
FiniteMultiscaleKernelCompatibilityExact.agda
FiniteStatisticalFiltrationExact.agda
ProbabilityDecoratedReebExact.agda
FiniteUltrametricReebFlowExact.agda
Round5AttachedFormalismBoundary.agda
Round5AttachedCompletionBoundary.agda
Round5CompleteBoundary.agda.
```

These modules implement:

- primitive admissible histories, a reversible subsystem, action as a history functional, stationary finite candidates, two-boundary pruning, and charge conjugation distinct from order reversal;
- filtering distinct from future-boundary smoothing;
- Gibbs, quantum-phase, and MDL weights as separate types;
- formal source, kernel theorem, and reproducible receipt as separate levels;
- exact six- and nine-residue cycles, bounded reachability, finite geometric-series identities, and explicit remaining p-adic-completion obligations;
- symmetry-compatible and symmetry-breaking finite ternary kernels;
- exact quotient descent, an explicit period-two counterexample, and strict finite-rank convergence;
- exact, defective, and quotient-valued multiscale kernel compatibility;
- physical states, probability laws, and statistical coordinates as separate carriers;
- a probability-decorated split/merge Reeb analogue with mass conservation, typed transition semantics, preservation maps, finite MDL model selection, ultrametric addresses, normalised transition rows, history weights, temporal thickness, and topological currents.

## Source records

`DarkSectorColliderSourceAtlas.agda` records author, title, venue, year, persistent DOI, imported role, and excluded promotion for:

- Silveira and Zee, *Scalar Phantoms*, DOI `10.1016/0370-2693(85)90624-0`;
- Schabinger and Wells, *A Minimal Spontaneously Broken Hidden Sector and its Impact on Higgs Boson Physics at the Large Hadron Collider*, DOI `10.1103/PhysRevD.72.093007`;
- Patt and Wilczek, *Higgs-field Portal into Hidden Sectors*, DOI `10.48550/arXiv.hep-ph/0605188`;
- Alimena et al., *Searching for Long-Lived Particles beyond the Standard Model at the Large Hadron Collider*, DOI `10.1088/1361-6471/ab4574`;
- CMS, displaced dimuon LLP search, DOI `10.1007/JHEP05(2024)047`;
- CMS, LLP trigger strategy and performance, DOI `10.48550/arXiv.2601.17544`, CMS-EXO-23-016, submitted to *Physics Reports*.

## Authority boundary

The checked finite statements do not establish:

```text
an actual dark sector;
a measured Higgs portal;
a physical decay width;
a continuum Lorentz representation;
a calibrated detector acceptance;
a CMS signal or exclusion;
a dark-matter abundance or cosmology.
```

They establish a precise typed interface by which such calibrated physics can later be connected without confusing portal interactions, hidden projections, metastability, boosted geometry, reconstruction, trigger selection, and empirical evidence.

Validation is performed by the combined pinned Agda workflow on a temporary branch whose base already contains the updated workflow definition.
