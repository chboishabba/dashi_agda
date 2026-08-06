# Dark-sector collider formalism

This tranche adds the collider-observation adapter missing from the existing hidden-sector quotient, Higgs-order-parameter, metastability, and coarse-projection work.

The exact finite chain is:

```text
gauge-singlet portal
-> hidden intermediate state
-> finite persistence witness
-> boosted nonzero displacement
-> reconstructed displaced vertex
-> prompt-trigger rejection
-> dedicated LLP-trigger acceptance.
```

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

`DisplacedVertex.agda` then checks:

```text
minimum displacement <= reconstructed displacement <= maximum displacement;
visible daughter multiplicity;
vertex-quality acceptance.
```

The canonical event has interaction point `0`, decay point `8`, accepted window `[2,10]`, two daughter tracks, and a passing quality flag. Prompt and outside-detector controls fail the displaced predicate for different reasons.

## Trigger censoring theorem

`TriggerCensoring.agda` defines separate prompt and LLP selections. On the canonical displaced event:

```text
promptTrigger = rejectEvent
llpTrigger    = acceptEvent.
```

It also proves the finite acceptance no-go:

```text
recordedSignalCount 5 2 0
=
recordedSignalCount 9 1 0
=
0.
```

Thus a recorded null at zero acceptance cannot identify the underlying production rate. In experimental notation, a null result constrains a production-times-branching-times-acceptance product, not production alone.

## Cross-pollination with the attached formalism

The same branch adds:

```text
FiniteHistoryOrientationExact.agda
HistoryWeightFiltrationExact.agda
FormalReceiptBoundaryExact.agda
FiniteWeightedTernaryKernelExact.agda
TernaryKernelQuotientLyapunovExact.agda
FiniteStatisticalFiltrationExact.agda
ProbabilityDecoratedReebExact.agda.
```

These modules implement:

- history reversal distinct from internal sign conjugation;
- filtering distinct from future-boundary smoothing;
- Gibbs, quantum-phase, and MDL weights as separate types;
- formal source, kernel theorem, and reproducible receipt as separate levels;
- symmetry-compatible and symmetry-breaking finite ternary kernels;
- exact quotient descent, an explicit period-two counterexample, and strict finite-rank convergence;
- physical states, probability laws, and statistical coordinates as separate carriers;
- a probability-decorated split/merge Reeb analogue with mass conservation, typed transition semantics, preservation maps, and finite MDL model selection.

## Source records

`DarkSectorColliderSourceAtlas.agda` records author, title, venue, year, DOI or explicit arXiv/no-DOI marker, imported role, and excluded promotion for:

- Silveira and Zee, *Scalar Phantoms*, DOI `10.1016/0370-2693(85)90624-0`;
- Schabinger and Wells, *A Minimal Spontaneously Broken Hidden Sector and its Impact on Higgs Boson Physics at the Large Hadron Collider*, DOI `10.1103/PhysRevD.72.093007`;
- Patt and Wilczek, *Higgs-field Portal into Hidden Sectors*, `arXiv:hep-ph/0605188`;
- Alimena et al., *Searching for Long-Lived Particles beyond the Standard Model at the Large Hadron Collider*, DOI `10.1088/1361-6471/ab4574`;
- CMS, displaced dimuon LLP search, DOI `10.1007/JHEP05(2024)047`;
- CMS, LLP trigger strategy and performance, `arXiv:2601.17544`.

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
