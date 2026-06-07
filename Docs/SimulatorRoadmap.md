# DASHI Simulator Roadmap

Declared surface level: `packaging` and `roadmap`.

This note is the entry surface for the word "simulator" in this repo. It
records what is already structurally available, what the first executable
slice should be, and which claims remain blocked.
For the broader plan that extends this receipt-gated route pattern across the
other lanes, read `Docs/UnifiedRoutesLanePlan.md`.

## Current Simulator Meaning

DASHI is being organized as a receipt-gated simulator surface, not as a
finished predictive engine. A simulated object should eventually be readable
as:

```text
object
  -> parent lane structure
  -> unified carrier grammar
  -> observable/projection surface
  -> numerical or formal receipt
  -> residual and promotion boundary
```

The current checked facade already gives unified objects the same formal
parent bundle:

- observation and projection;
- carrier and role vector;
- residual level;
- proof posture;
- invariant posture;
- modular-j, Hecke, Bott, Kolmogorov, category, quotient, lattice, and
  operator projection parents.

The owner modules for that surface are:

- `DASHI.Unified.InvariantSpine`
- `DASHI.Unified.FormalObjectParents`
- `DASHI.Unified.CrossScaleMatterPhysics`
- `DASHI.Unified.Everything`

The unified language owner is:

- `DASHI.Interop.UnifiedMathLanguageSpine`

The current cross-scale matter parent records:

```text
atoms
  -> molecules
  -> chemistry
  -> cells
  -> organisms
  -> stellar bodies
```

with strong nuclear, weak, electromagnetic, and gravitational carriers as the
stability and transition parents.

## What Is Already Solid

- The repo has an importable unified facade under `DASHI.Unified`.
- Chemistry and supervoxel chemistry have local definitional proof surfaces.
- PNF/hyperfabric has checked internal structure.
- Brain/fMRI, Navier-Stokes, Yang-Mills, and cross-scale matter are present as
  non-promoting parent objects.
- The physics/chemistry/biology/DNA discharge is connected as receipt-gated
  observation transport.
- Weak-field GR has an executable external-baseline diagnostic, but it is not
  carrier-derived DASHI gravity.

The current state is therefore a typed simulator scaffold: objects can be put
on the common carrier/projection spine, but most quantitative predictions are
still external-baseline, bounded proxy, empirical, or blocked surfaces.

## First Quantitative Slice

The first simulator slice should be narrow and non-promoting:

```text
stellar composition vector
  -> bounded matter/force proxy carrier
  -> stability observable
  -> JSON/CSV/Markdown numerical receipt
  -> Agda receipt with blocked promotion guards
```

The first target is now an executable bounded stellar-composition diagnostic,
not a full Sun model.

Inputs:

- hydrogen mass fraction;
- helium mass fraction;
- metal mass fraction;
- optional normalized total-composition check;
- repeatable named composition rows from the CLI.

Bounded proxy observables:

- mean-molecular-weight proxy;
- support proxy ratio versus the reference composition;
- energy-generation proxy ratio versus the reference composition;
- stability score or regime label.

Required output shape:

- JSON summary;
- CSV rows for each sampled composition;
- Markdown report;
- explicit booleans for `carrierInternalPrediction = false`,
  `stellarEvolutionPromoted = false`, `solarInstabilityClaimPromoted = false`,
  and `externalBaselineOrProxyOnly = true`.

Implemented surfaces:

- `scripts/run_stellar_composition_proxy_diagnostic.py`
- `tests/test_stellar_composition_proxy_diagnostic.py`
- `DASHI.Unified.StellarCompositionProxyReceipt`
- `DASHI.Unified.CrossScaleMatterPhysics`

The implementation pattern should match existing audit lanes:

- Python script in `scripts/`;
- focused pytest file in `tests/`;
- Agda receipt module under `DASHI/Unified`;
- documentation update in this roadmap and the validation manifest.

The staged real-model adapter path remains blocked until the proxy lane can be
connected to accepted EOS, opacity, reaction-network, hydrostatic-solver, and
empirical validation receipts without changing the fail-closed promotion
guards.

## Known Constants And Laws Inputs

Known constants and law names are not left implicit. The repo-wide owner is
`DASHI.Constants.Registry`, and the route-level map is
`Docs/UnifiedRoutesLanePlan.md#known-constants-and-laws-population`.
The registry is imported by `DASHI.Everything` for discoverability, but it is
still a non-promoting input registry rather than a theorem owner.
The receipt to cite from simulator slices is
`DASHI.Constants.Registry.canonicalKnownInputsPopulationReceipt`.
It currently checks 40 constant slots, 33 law slots, and 11 authority-source
slots.
Numeric or law-consuming simulator slices should also cite
`DASHI.Constants.Registry.canonicalAuthorityConsumptionPolicyReceipt`, which
requires source version, checksum, access date, uncertainty, rounding, unit,
validity-regime, URI, and provider-receipt metadata before a measured value or
rounded expression can support a promoted consumer.
Physics-adapter slices should cite
`DASHI.Constants.Registry.canonicalPhysicsAdapterKnownInputsReferenceReceipt`,
which promotes only bounded physics target population and keeps Maxwell, GR,
Standard Model, Gate 3, Navier-Stokes Clay, Yang-Mills Clay, and
known-physics translation completion unpromoted.
Arithmetic/Gate 3 slices should cite
`DASHI.Constants.Registry.canonicalArithmeticGate3KnownInputsReferenceReceipt`,
which promotes only finite route population and density/fill-distance evidence
while keeping Gate 3 closure, Mosco recovery, no-spectral-pollution,
continuum transfer, mass-shell bridging, and physics claims unpromoted.
Quantum-facing slices should cite
`DASHI.Constants.Registry.canonicalQuantumKnownInputsReferenceReceipt`, which
keeps Schrodinger dynamics, Born-rule semantics, QFT, and quantum empirical
adequacy unpromoted while naming the exact and measured quantum inputs.
Chemistry-facing slices should cite
`DASHI.Constants.Registry.canonicalChemistryKnownInputsReferenceReceipt`, which
promotes only local definitional chemistry population and keeps physical
chemistry, spectroscopy, bonding interpretation, and wet-lab validation
unpromoted.
Biology-facing slices should cite
`DASHI.Constants.Registry.canonicalBiologyKnownInputsReferenceReceipt`, which
promotes only structured biology bridge population and keeps causation,
intervention, clinical validity, genome-to-connectome closure, and brain-state
recovery unpromoted.
Empirical/runtime slices should cite
`DASHI.Constants.Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt`,
which promotes only receipt-infrastructure population and keeps provider
authority, comparison law, covariance/calibration, holdout validation, runtime
replay authority, semantic adequacy, and empirical adequacy unpromoted.
Systematic lane interlinks should cite
`DASHI.Interop.CategoricalInterlinkLayer.canonicalCategoricalInterlinkReceipt`.
That receipt records the promotion ladder, lane objects, lane morphisms, and
registry bindings while keeping theorem, empirical, Clay, full Standard Model,
and terminal promotion false.
Promotion-gated simulator slices should cite
`DASHI.Promotion.ObligationIndex.canonicalUnifiedPromotionObligationIndex`.
That receipt joins the six obligation lanes and records 73 open promotion
obligations while keeping terminal/full-unification promotion false.

Simulator slices may consume exact SI defining constants from that registry as
reference inputs, and may consume exact derived SI expressions such as `hbar`,
`R`, and `F` with an explicit rounding policy. Measured constants, physical
laws, chemistry laws, and biology laws must still arrive with
source/version/unit/uncertainty or domain-validation receipts before a
real-model claim can use them.

Every constants/laws input artifact must remain fail-closed unless a consuming
authority receipt is supplied:

```text
constantCarrierDerived = false
physicalLawDerived = false
calibrationPromoted = false
empiricalAdequacyAccepted = false
externalInputOnly = true
```

This prevents a populated input table from being mistaken for a derivation of
constants, physical law, wet-lab chemistry, biology causation, clinical
validity, or empirical adequacy.

Authority-source slots in the registry identify where a future adapter must
obtain source/version/checksum/uncertainty or protocol data. A source URI in
that list is not an accepted authority token until a lane-specific receipt
consumes it.

## Blocked Claims

This roadmap does not promote:

- full stellar evolution;
- real solar-composition counterfactuals;
- a claim that a 3 percent hydrogen perturbation makes the Sun unstable;
- carrier-derived physical constants;
- equation-of-state authority;
- opacity-table authority;
- nuclear reaction-network authority;
- molecular dynamics from QFT/YM/NS;
- atoms-to-cells biological prediction;
- disease causation or clinical prediction.

Those remain blocked until the relevant physical models, constants, solvers,
empirical receipts, and Agda receipt guards are inhabited.

## Future Facade API

After the docs-first pass, the next Agda ergonomics target is a small parent
API that makes common imports obvious. A reader should be able to import one
surface and ask whether an object has the unified parent structure associated
with physics, chemistry, biology, cross-scale matter, or the shared carrier
grammar.

That API should not change claim strength. It should only expose existing
parent/facade records in a cleaner way, with the same non-promotion proofs.

## Validation Policy

For docs-only edits, validate by checking links and cited modules with `rg`.

For facade edits, prefer:

```bash
agda DASHI/Unified/CrossScaleMatterPhysics.agda
agda DASHI/Unified/Everything.agda
```

Use `DASHI/Everything.agda` only as a deliberate aggregate check, not as the
normal inner-loop target.
