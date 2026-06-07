# DASHI Simulator Roadmap

Declared surface level: `packaging` and `roadmap`.

This note is the entry surface for the word "simulator" in this repo. It
records what is already structurally available, what the first executable
slice should be, and which claims remain blocked.

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
still external-baseline, toy, empirical, or blocked surfaces.

## First Quantitative Slice

The first simulator slice should be narrow and non-promoting:

```text
stellar composition vector
  -> toy matter/force carrier
  -> stability observable
  -> JSON/CSV/Markdown numerical receipt
  -> Agda receipt with blocked promotion guards
```

The recommended first target is a toy stellar-composition diagnostic, not a
full Sun model.

Inputs:

- hydrogen mass fraction;
- helium mass fraction;
- metal mass fraction;
- optional normalized total-composition check.

Toy observables:

- mean-molecular-weight proxy;
- central-pressure or support proxy;
- energy-generation proxy;
- stability score or regime label.

Required output shape:

- JSON summary;
- CSV rows for each sampled composition;
- Markdown report;
- explicit booleans for `carrierInternalPrediction = false`,
  `stellarEvolutionPromoted = false`, `solarInstabilityClaimPromoted = false`,
  and `externalBaselineOrToyOnly = true`.

The implementation pattern should match existing audit lanes:

- Python script in `scripts/`;
- focused pytest file in `tests/`;
- Agda receipt module under `DASHI/Unified` or
  `DASHI/Physics/Closure`, depending on whether the receipt is treated as a
  facade object or a physics closure support surface;
- documentation update in this roadmap and the validation manifest.

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
