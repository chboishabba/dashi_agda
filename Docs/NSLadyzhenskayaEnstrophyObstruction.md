# NS Ladyzhenskaya Enstrophy Obstruction

Companion to:

```text
DASHI/Physics/Closure/NSLadyzhenskayaEnstrophyObstructionReceipt.agda
```

Sprint 7/8 attacks `VortexStretchingAbsorption` directly and recovers the
classical Ladyzhenskaya/Prodi/Serrin obstruction.

The corrected 3D Gagliardo-Nirenberg route gives:

```text
|T_stretch| <= C ||grad u||_L3^3
            <= C ||grad u||_L2^(3/2) ||Delta u||_L2^(3/2)
```

After Young's inequality the enstrophy estimate has the form:

```text
dE/dt + nu ||Delta u||_2^2 <= C_nu E^3
```

where `E = ||grad u||_2^2`.  This cubic ODE can blow up from large data.
That is a failure of the estimate, not a proof that the Navier-Stokes solution
blows up.

The missing non-circular input is subcritical vortex-stretching absorption,
equivalently a way to replace the `E^3` estimate by a linear/subcritical
enstrophy bound.  One standard sufficient lane is the Serrin-scale condition:

```text
u in L^4(0,T; L^4)
```

## Updated NS Route

```text
Serrin L4_t L4_x control without circularity
-> PointwiseEnstrophyControl
-> NoFiniteTimeBlowup
-> GlobalSmoothSolution
-> clayNavierStokesPromoted = true
```

## Boundary

The receipt records the obstruction and the classical frontier match.  It does
not prove Serrin control, pointwise enstrophy, no blowup, global smoothness,
uniqueness, or Clay Navier-Stokes.
