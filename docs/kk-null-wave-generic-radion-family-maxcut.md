# KK null-wave family — exact Ricci-flat completion cut

The earlier sibling Diamond PR #1238 provides a genuine 5D Ricci-curvature *fixture* for a magnetic field but not a 5D vacuum solution. The current PR #1239 adds both a nonconstant-radius nonzero-field solution and the more powerful symbolic arbitrary-profile family.

Coordinates (u,v,x,y,w), cylinder condition, phi(u) nonzero, a(u) smooth:
```
A=a(u) dx
g4=2du dv + dx² + dy² + H(u,x) du²
H= -[phi''(u)/phi(u) + phi(u)²(a'(u))²/2]x²
G5=g4+phi(u)²(dw+A)²
```
Direct tensor construction (all Christoffel symbols and all 25 Ricci entries) proves symbolic identically `Ricci5=0`, with `det G5=-phi²`, `F=a'(u)du∧dx`, `F²=0`. Verified locally via exact SymPy code with symbolic differentiable functions phi(u), a(u); additionally verified concrete phi=1+u², a=b*u. This is a **family of actual nontrivial local five-dimensional vacuum Einstein solutions**, not merely another nonvacuum magnetic fixture.

Source: `scripts/check_kk_general_null_wave_radion_family.py`; specialized regression: `scripts/check_kk_variable_radion_null_em_vacuum.py`.

This moves earlier 'solve a nonconstant-radion Ricci-flat 5D solution with electromagnetic flux' roadmap item to *discharged for the null pp-wave family*. It does **not** prove global completeness, arbitrary curved-base KK tensor identity, full 4D reduced action including boundary, nonabelian compactification, or a physical identification between braid framing and KK circle phase.

Braids: preserve 3=line, 6=glued lines, 9=sheet, 18=glued sheets, 27=cube structure; the twelve orbit **time** samples share a nine-position sheet. Next challenge is continuous gamma/normals/angle plus O2 transition and framed pants gluing, with correct independent C3 strand permutation, C2 reflection and Z winding.

## Acceptance
```bash
python3 scripts/check_kk_general_null_wave_radion_family.py
python3 scripts/check_kk_variable_radion_null_em_vacuum.py
```
The two symbolic calculations ran locally and passed with equivalent source. Agda kernel and exact GitHub checkout CI were not run.

## Remaining high-alpha target
Derive arbitrary smooth (g,A,phi) tensor identities in geometric proof assistant; then connect smooth framed braid O2 cocycle / holonomy to a *separately supplied* KK fibre map. Neither a common order-two symmetry nor a Monster coefficient is enough to promote a physical unification.
