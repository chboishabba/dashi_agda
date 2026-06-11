# Physics Closure Quick Attack

Date: 2026-03-28

This is the short-session closure push surface for the remaining isotropy /
finite-speed / quadratic-forcing / signature seams.

## Added Agda Targets

- `DASHI/Lorentz/ConeSignature.agda`
  - exposes the exact cone assumptions behind the cone ⇒ Lorentz signature step
- `DASHI/Physics/IsotropyInvariant.agda`
  - exposes when an `O(3)`-invariant placeholder stays Lorentzian and when it introduces a preferred frame
- `DASHI/Physics/QuadForcingScaling.agda`
  - exposes the energy-subcritical scaling gate behind quadratic local well-posedness

These files are intentionally skeletal and use postulates as assumption markers.
They are for assumption-audit speed, not proof completion.

## Added Empirical Target

- `scripts/toy_pde_finite_speed.py`
  - runs one hyperbolic and one elliptic toy evolution
  - reports support radius vs cone growth
  - prints a minimal MDL comparison table for A/B/C closure candidates

Suggested local run:

`python scripts/toy_pde_finite_speed.py --csv /tmp/dashi_toy_pde.csv`

## Next Tightening Step

Replace each postulated conclusion with the smallest real bridge theorem that
connects to the current canonical closure path, rather than widening these
stubs into a second parallel formalization.
