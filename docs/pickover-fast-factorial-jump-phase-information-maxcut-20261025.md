# Pickover fast factorial jump / phase information max-cut (2026-10-25)

## Original target and exact convention
N=99^(9999!).  Not (99^9999)! and not tetration.
The sign is (-1)^floor(N/pi). A distinct base-10-only laboratory studies
s_b(k)=sign(sin(b^k)), b=10, especially k=n!.

## Compact exact powering
F_m(z)=z^m, F_a∘F_b=F_(ab), so F_b composed k times =F_(b^k).
Binary composition takes floor(log2(k)) squarings plus popcount(k)
selected multiplications (with standard implementation variations).
For k=9999!, bit_length(k)=118445; only 118444 squarings and
53996 nonzero binary digits are required to BUILD the symbolic map.
This is not a claim that arbitrary-precision complex evaluation is cheap.

CAUTION: the factorial-indexed circle phase z_n=e^(i*b^(n!)) satisfies
z_(n+1)=z_n^(b^(n*n!)), NOT z_n^(n+1). The latter is only true for the
underlying positive integer magnitudes b^(n!), not their complex exponential.

## Exact interval sensitivity
For lifted real circle coordinates α,β and integer multiplier M,
|Mα-Mβ|=M|α-β| before reduction mod1.
A generic phase interval of width δ is stretched to width Mδ.
To guarantee the resulting arc width <1/2, the initial width must be
<1/(2M). For M=b^k this demands Ω(k log2 b) bits in a
generic interval certificate. This is an obstruction for ordinary
interval propagation, NOT a lower bound for every possible algorithm
on the special phase 1/(2*pi).
A pair of rational phases differing only at depth 10^-6 have
opposite signed chambers after multiplying by 10^6. The regression
makes that information-loss test exact.

## Existing donors and attribution
- DASHI/Biology/SelfIndexingHyperfabricTetrationExact.agda:
  distinguishes program / execution / residual witness lengths.
- DASHI/Topology/TetrationalGateField.agda:
  chart retention/refinement and tower level, but target is iterated
  powering, not tetration.
- DASHI/Moonshine/JInvariant369ReflectionEquivarianceExact.agda:
  reflection commuting-square interface, NOT a proved powering
  endomorphism intertwiner on the exact π-phase.
- DASHI/Foundations/BishopMachinPiRationalWindowExact.agda:
  constructive Machin π brackets; source Machin (1706), Bishop/
  Bridges constructive real framework.
- Horned C3 PR #1244: infinite-order source with finite quotient
  information loss; no inferred equality to analytic unit-circle angle.

## Acceptance cut
Construct a source-specific short residual witness W(k) with
  verify(W(k), b, k, π) -> sign(sin(b^k)),
and an effective producer whose measured complexity grows
sublinearly in k for the base-10 controls.
Preserve and test same-object phase, exact real orientation,
and costs of BOTH producing and checking W(k).
Do not promote modular CRT observations or symbolic jump cost
to full real sign computation. Then instantiate b=99,
k=9999!. Original terminal sign remains open.
