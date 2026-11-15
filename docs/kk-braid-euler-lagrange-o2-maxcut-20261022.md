# KK / C3 framed braid round — source-to-equation cut

## This round's new mathematics

### KK radion + Maxwell, shared reduced action
The newly committed `scripts/check_kk_magnetic_radion_maxwell_euler_lagrange.py` starts with the standard *assumed* reduced Jordan action and restricts to `A_y=a(x)`, `phi=phi(x)`, with F²=2(a')². Its Euler–Lagrange equations are
```
E_phi = R4 - 3*kappa² phi² (a')² / 2
E_A = kappa² d_x(phi³ a')
```
where the A equation is source-free Maxwell for the chosen one-dimensional ansatz. This is a nontrivial compatibility constraint, not a claim that flat base solves all Einstein equations. For a linear potential `a=b*x`, `E_A=3*kappa²*b*phi²*phi'`; for b nonzero and phi positive, the radion must be constant. Together with the constant-phi trace condition `R4=0`, the scalar equation excludes nonzero pure magnetic F. Nonconstant flux can instead obey `phi³ a'=constant`, but gravitational/radion backreaction still must be checked. The reduced action's general 5D scalar curvature reduction and boundary terms remain independently open.

### Braid O(2) transport / unwrapped framing
`DASHI/Foundations/C3O2SignedWindingTransportExact.agda` models signed integer-like winding as an abstract additive group equipped with an involutive additive automorphism, and defines the reflection-parity action and semidirect multiplication. The `actionComposition` theorem is supplied at the carrier level. It is **not** a physical isomorphism between six-step x-reflection and KK fibre reversal, nor a proof that 27 ternary spatial positions contain unbounded winding. Source is committed and kernel-unverified.

## Acceptance
```
python3 scripts/check_kk_magnetic_radion_maxwell_euler_lagrange.py
agda -i . -i /path/to/agda-stdlib DASHI/Foundations/C3O2SignedWindingTransportExact.agda
```

## Remaining max-cut after this round
1. General curved base + phi + A full Riemann/Ricci tensor calculation and 5D Einstein equation decomposition; add matter sources/boundary terms.
2. Construct a genuine continuous S1 phase lift and geometric framed line/circle gluing, with an explicit compatible local gauge O2 structure.
3. Glue the 6-step balanced spatial mirror and C3 strand rotation into that circle bundle *only with an independent action/connection producer*.
4. Reuse existing nonabelian W3/M3, SU3 gauge and shared QFT/GR stress owners to establish actual field representation, not formal numerical similarity.
5. Put Monster/moonshine into the same action and Hilbert/observable sector with explicit spectral predicates and falsifiable independent data.

No general physical closure, Moonshine gravitational identity, or Agda kernel receipt asserted.
