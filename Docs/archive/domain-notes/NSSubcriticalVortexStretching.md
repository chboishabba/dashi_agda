# NS Subcritical Vortex-Stretching Receipt

Canonical receipt:
`DASHI/Physics/Closure/NSSubcriticalVortexStretchingReceipt.agda`

## Closed Theorems / Safe Results

The lane keeps the Sprint 7 useful facts:

- transport cancellation is recorded
- HighLow reduces to a commutator
- the old `K^-1/2` suppression claim is retracted

## Corrected Ladyzhenskaya Obstruction

For enstrophy

```text
E = ||grad u||_2^2
```

the standard 3D interpolation gives the cubic obstruction:

```text
dE/dt <= C_nu E^3
```

This is the corrected Sprint 8 surface.  It does not close large-data
regularity and does not prove blowup by the actual solution; it only records
the failure of this estimate to close the Clay route.

## Remaining Clay Lemma

The exact missing theorem is:

```text
SubcriticalVortexStretchingAbsorption
```

It would need to replace the standard cubic bound by a subcritical absorption
estimate with no Serrin, BKM, global `H118`, global `LInfinity`, or
continuation input.

Equivalently, one can prove the obstruction sharp:

```text
LadyzhenskayaObstructionIsSharp
```

All Navier-Stokes and Clay promotion flags remain false.
