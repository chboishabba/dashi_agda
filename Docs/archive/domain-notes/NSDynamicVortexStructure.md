# NS Dynamic Vortex Structure

This receipt records the good-route Navier-Stokes algebra after the
Leray/Sobolev route has been killed by scaling.

Solved pieces:

- vorticity energy identity isolates vortex stretching
- only the symmetric strain tensor stretches vorticity
- exact Beltrami alignment makes the projected nonlinearity vanish
- approximate Beltrami alignment supplies a multiplicative angle defect
- adjacent-only cascade control is conditionally absorbable if the angle
  defect supplies the missing half derivative
- pressure is projection/gauge in this identity, not direct enstrophy
  dissipation
- the `H118` fallback alone does not close Clay

The live Clay-critical theorem is:

```text
DynamicHalfDerivativeDepletion:
  angleDefect_K(t) * 2^(K/2) is bounded, preferably small,
  along actual Navier-Stokes trajectories.
```

For absorption one needs the stronger smallness surface:

```text
sup_K angleDefect_K(t) * 2^(K/2) <= epsilon * nu / C
```

The pressure route is also first-class but open:

```text
PressureInducedStrainVorticityMisalignment:
  pressure changes the geometry of u so strain and vorticity misalign.
```

Everything else is scaffolding.  The receipt does not prove dynamic vortex
alignment, pressure-induced strain/vorticity misalignment, pointwise
enstrophy control, no blowup, global smoothness, uniqueness, or Clay
Navier-Stokes.
