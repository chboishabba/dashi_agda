# KK Einstein–Maxwell concrete vacuum solution and C3 framed braid focus

## Novel concrete upgrade from sibling Diamond #1238
Diamond #1238's `scripts/check_bioem_kk_5d_einstein_maxwell.py` proves correct 5D scalar-curvature and R55 identities for a uniform magnetic field on *flat 4D base*, but explicitly finds a nonvacuum R55=b²/2.

This branch now adds `scripts/check_kk_5d_ricci_flat_null_einstein_maxwell.py`, constructing a **true nontrivial 5D vacuum Einstein solution with F nonzero**, using
```
(u,v,x,y,w) null coordinates, parameter b
g4 = 2 du dv + dx² + dy² - (b²/2)x² du²
A = b u dx, phi = kappa = 1
G5 = g4 + (dw+A)²
F = b du wedge dx, F² = 0
```
The script directly differentiates all five-dimensional metric components and calculates all 125 Christoffels and all 25 Ricci entries; it checks Ric5=0 identically, determinant -1, F nonzero and F²=0. It also checks 4D Ric_uu = b²/2 from the Brinkmann wave profile. **This result was independently executed locally for the same five-dimensional metric** and showed the entire Ricci tensor zero, not merely selected equations. The specific committed script carries extra F² and base Ricci assertions which should be run on an exact checkout for certification.

## Physical interpretation and limits
This is the classical Kaluza–Klein lift of a null electromagnetic plane-wave configuration with gravitational backreaction. It defeats the mistaken generalized statement that constant KK radius forces F=0: it only forces the invariant F²=0 in sourceless 5D vacuum, and hence allows certain nonzero null F fields. This particular exact solution is not asymptotically flat, a complete QCD/quantum gravity theory or evidence the braid is the KK fibre.

## High-alpha remaining KK/braid work
1. General tensorial 5D->4D curvature identity with arbitrary curved g4, A, phi (coordinate-free or formalized over precise smooth prerequisites), including boundary terms and 4D field equations.
2. New nonconstant phi Ricci-flat 5D solution, with explicit four-dimensional curved backreaction and Maxwell flux.
3. Full continuous C3 braid framed path, true O2 transition cocycle (including reflection-induced inversion and gauge overlap), unwrapped integer winding and pants gluing; do not confuse spatial mirror with physical circle inversion.
4. Lift construction into the existing Clifford Pin/Spin and gauge/Dirac machinery using explicit commuting diagrams.
5. Nonabelian KK extension using W3/M3 SU3 and Yang-Mills; independently justified compactification geometry required for geometric origin of colour.

## Acceptance
```
python3 scripts/check_kk_5d_ricci_flat_null_einstein_maxwell.py
python3 scripts/check_c3_braid_o2_gluing_obstructions.py
```
Agda/kernel certification is separate from symbolic local algebra. Attribution: standard KK and Brinkmann pp-wave mathematics; user's independent C3/369 braid programme and preexisting repo sector owners; session authored finite exact symbolic implementation.
