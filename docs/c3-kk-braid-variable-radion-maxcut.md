# KK + C3 six-step framed braid: direct analytic and geometric max-cut

## New verified analytical fixture
The new `scripts/check_kk_variable_radion_5d.py` constructs an explicit five-dimensional smooth metric `diag(-1,1,1,1,phi(x)^2)` and computes Christoffel, full Ricci and scalar curvature by symbolic differentiation. It asserts and locally passes `R5=-2 phi''/phi`, `Rxx=-phi''/phi`, `R55=-phi phi''`, and `det G=-phi²`. This is a new **variable-radius** sector with zero gauge potential, complementing #1238's nonzero-B constant-radius sector and #1239's abstract radion-variation receipt. **It is not the coupled varying-phi/F general tensor identity.**

## C3/mirror and O2 KK duality distinction
`scripts/check_c3_o2_kk_inversion.py` algebraically checks the optional action `theta'=-theta+chi`, `A'=-A-(1/k)dchi`, hence `dy'+k A'=-(dy+kA)`; the quadratic KK fibre metric is invariant. The balanced 27-cube spatial x-mirror is an order-two orientation-reversing orthogonal map. Both involutions are concrete, but **there is no proved physical action automatically identifying the spatial mirror with internal circle inversion**.

The selected three-strand orbit is on a 3×3 sheet. It has a 12-step sampled period and a 6-step left/right mirror, not twelve site states. Its true geometric carrier hierarchy is 3=line, 6=two compatibly glued lines, 9=3×3 sheet, 18=two compatibly glued sheets, 27=3×3×3 cube or separately typed 27-coordinate graph-completion. Do not infer state counts from those descriptors.

## Critical bridge from frame to continuous phase
For each moving strand `gamma_i(t)`, specify a transverse normal `n_i(t)`, one angular lift `Theta_i(t)∈R`, and a connection-dependent transport convention. The true framed braid invariant requires the full continuous history and gluing; terminal site or frame samples do not recover arbitrary integer winding. An optional O(2) lift of spatial reflection to the KK circle can act as `theta→-theta+chi`, but requires an explicit orientation/phase bundle map, transition compatibility on overlaps, and dynamical/empirical support.

## General KK unification residual
Prove from the full 5D metric `G(g,A,phi)` at arbitrary curved base that `R5=R4-k²phi² F²/4-2 phi^-1 Box phi` under conventions; reduce action with honest boundary terms; obtain all Einstein, Maxwell and radion Euler–Lagrange equations. The 5D vacuum constant-radius pure magnetic fixture is not an admissible solution, while F²=0 nonzero fields aren't excluded by the scalar constraint alone. The existing 3D/colour/QCD and moonshine work remains separately typed; a 1D KK circle does not by itself generate SU3.

## Acceptance
```sh
python3 scripts/check_kk_variable_radion_5d.py
python3 scripts/check_c3_o2_kk_inversion.py
python3 scripts/check_c3_ninesite_borromean.py
```
The first two scripts were run locally from equivalent source in this round and passed, but the committed bytes were not executed from a checkout. Agda kernel is not certified. Attribution: user-origin spatial geometry and mirrored orbit; classical KK/O(2)/braid mathematics; new fixture/code current session.
