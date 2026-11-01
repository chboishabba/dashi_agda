# NS Analytic Braid Residue Depletion Conjecture

This note records the single productive Navier-Stokes conjecture that fuses the
split DASHI residue gates.

The conjecture is:

```text
AnalyticBraidResidueDepletionForNS:
  there exists a BraidResidue369 functional of actual NS data
  and constants C, r with r * sqrt(2) < 1 such that:

  1. the residue controls physical shell stretching;
  2. the residue decays deterministically from shell K to K+1
     along every actual NS trajectory.
```

ELI5: define a real bad-stretch meter for every whirlpool scale.  The meter
must actually measure how hard the rope is being pulled, and real water must
force that badness to shrink fast enough at each smaller scale.  If the shrink
factor beats the `sqrt(2)` growth, viscosity wins.

## Why this was added

Earlier receipts already had the content split across separate gates:

```text
BraidResidue369 analytic functional
BraidResidueControlsPhysicalStretching
DynamicBraidResidueDecayForNS
ResidueDecayBeatsHalfDerivative
```

The new receipt names the single conjecture that would make those gates
productive together:

```text
AnalyticBraidResidueDepletionForNS
  -> BraidResidueControlsPhysicalStretching
  -> DynamicBraidResidueDecayForNS
  -> ResidueDecayBeatsHalfDerivative
  -> StretchAbsorption
  -> PointwiseEnstrophyControl
  -> NoFiniteTimeBlowup
  -> Clay Navier-Stokes would promote
```

## Reference checks

Any proposed residue must pass these checks:

- Beltrami-null cases should have small or zero residue.
- Two-dimensional/no-stretching cases should have small or zero residue.
- The result should be compatible with Constantin-Fefferman-Majda vorticity
  direction coherence.
- The result should be compatible with Beale-Kato-Majda continuation logic.
- Coherent vortex tubes must either be excluded or absorbed.

## Boundary

This is not a proof.  It does not define `BraidResidue369`, prove physical
stretching control, prove deterministic decay, exclude coherent tubes, prove
pointwise enstrophy control, or promote Clay Navier-Stokes.

The Agda surface is:

```text
DASHI/Physics/Closure/NSAnalyticBraidResidueDepletionConjectureReceipt.agda
```
