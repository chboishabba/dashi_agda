# NS Ladyzhenskaya Cubic Obstruction

Companion to:

```text
DASHI/Physics/Closure/NSLadyzhenskayaCubicObstructionReceipt.agda
```

Sprint 8 corrects the live enstrophy obstruction.  For

```text
E(t) = ||grad u(t)||_2^2
D(t) = ||Delta u(t)||_2^2
```

the enstrophy identity gives the vortex-stretching term:

```text
1/2 E'(t) + nu D(t)
  = - integral partial_i u_j partial_j u_k partial_k u_i
```

The standard 3D interpolation route gives:

```text
||grad u||_L3^3 <= C ||grad u||_L2^2 ||Delta u||_L2
```

and Young's inequality yields:

```text
E'(t) <= C_nu E(t)^3
```

This is a cubic enstrophy ODE, not a Clay closure.  It can blow up at the
level of the estimate, with scale comparable to `1 / (C E0^2)`.

## Clay Hinge

The missing Clay estimate is:

```text
SubcriticalVortexStretchingAbsorption:
  |T_stretch|
    <= epsilon * nu * ||Delta u||_2^2
     + C(E0,nu) * ||grad u||_2^2
```

That would reduce the cubic `E^3` behavior to a linear/subcritical enstrophy
bound.  Standard Leray/Sobolev machinery does not provide it.

## Boundary

This receipt records the sharp classical obstruction and supersedes the older
quadratic wording as the current live state.  It does not prove pointwise
enstrophy control, no blowup, global smoothness, uniqueness, or Clay
Navier-Stokes.

