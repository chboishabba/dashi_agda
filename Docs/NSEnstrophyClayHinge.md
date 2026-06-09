# Navier-Stokes Enstrophy Clay Hinge

This document is the reader-facing companion to:

```text
DASHI/Physics/Closure/NSEnstrophyClayHingeReceipt.agda
```

Sprint 6 removes the last shortcut reading of the HighLow route.  The
commutator target is Clay-equivalent:

```text
CommutatorLipschitzControlWithoutRegularity
<-> PointwiseEnstrophyControl
<-> no finite-time blowup
```

The live Clay hinge is the vortex-stretching absorption estimate:

```text
| integral partial_i u_j partial_j u_k partial_k u_i |
  <= epsilon * nu * ||Delta u||_2^2
   + C(E0, nu) * ||grad u||_2^2
```

with no Serrin, BKM, global `H118`, global `LInfinity`, or continuation norm
input.

## Corrected NS Chain

```text
TransportTermEnergyCancellation
-> HighLowEqualsCommutator
-> CommutatorLipschitzEquivalentToPointwiseEnstrophy
-> VortexStretchingAbsorption
-> PointwiseEnstrophyControl
-> NoFiniteTimeBlowup
-> GlobalSmoothExistence
-> Uniqueness
-> clayNavierStokesPromoted = true
```

## Boundary

This receipt records the hinge and the circularity guard.  It does not prove
vortex-stretching absorption, pointwise enstrophy control, no blowup, global
smoothness, uniqueness, or Clay Navier-Stokes promotion.
