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


## 2026-10-25: decisive perfect-ninth-power nilpotence non-descent
An attractive proposed shortcut says 9|9999! and 99^3=0 in
Z[omega]/(1-omega)^9, so the real sine phase must be locked.
The first two premises are true, the proposed real consequence is false.
The exact Machin rational certificates in
scripts/check_pickover_ninth_power_non_descent.py establish

  99^9=(99)^9, floor(99^9/pi)=290781571073447469, sin(99^9)<0;
  99^18=(99^2)^9, floor(99^18/pi)=265633980425984427859213880941867086,
  sin(99^18)>0.

Both exponent k>=3 images of 99^k are 0 in the same Eisenstein quotient
and both are perfect ninth powers. No sine-sign map can therefore descend
to that finite quotient on the whole ninth-power 99-orbit.
This does NOT refute an analytic source-specific witness at k=9999!, and
does NOT prove that all finite computations are useless. It rejects an
invalid same-object transport. No exact-head Agda kernel receipt asserted.

Roadmap: (1) retain exact finite certificates as tests, (2) certify the
same-phase reflection and integer-power commuting square using existing
JInvariant369ReflectionEquivarianceExact but DO NOT infer a powering
intertwiner from reflection equivariance, (3) benchmark base10-only
factorial Chebyshev U9 jumps with explicit rational error, (4) find a
source-specific terminal real-phase witness whose producing and checking
cost is sublinear in factorial position, (5) transfer only proved
conditions to base99 and terminate on sign(sin(99^(9999!))).

Attribution: classical Machin (1706) arctangent identity and elementary
sine half-period signs; DASHI-specific finite choice and exact script.

## 2026-10-26: punctured-nine hexadecimal arithmetic and P-vs-NP resource audit

Source carrier: OggSSPP2BalancedTernaryPuncturedPlaneExact has EIGHT
concrete nonzero NineSheet points with native antipode in FOUR pairs.
The DISJOINT UNION of two copies has 16 elements. A chosen indexing
8*s+i transports ordinary Z/16Z addition with exact low-three-bit
carry, as exhaustively checked in check_pickover_punctured_hex_cost_audit.py.
This is a *transported ring operation*, not an intrinsic multiplication
law already established for the punctured geometry.

STRONG NEGATIVE CONTROL: native antipode on two copies has ZERO fixed
points, whereas x -> -x mod16 has exactly TWO fixed points (0,8).
No bijection can intertwine these involutions. In particular the
previously-owned reflection commuting square cannot simply be
rebranded as hexadecimal additive inverse. Separate phase-action
intertwiner needed. This is stronger than a cardinality remark and
avoids falsely promoting source geometry to BBP arithmetic.

Resource prior art: Agda P-vs-NP PR #1129 exact candidate execution/
static program-size account, and PR #1040 identity-observer
losslessness, are negative-controls on purported information lower
bounds. Source-written compact repeated-square paths are NOT cheap
numeric squarings of N, and representational efficiency by itself says
nothing about the producer cost of a signed real-phase certificate.
Classical binary powering and 1995 BBP digit extraction retain source
authorship. Standard BBP still needs order d terms for digit index d;
power-of-two base does not produce an instant sign for sin(16^(1616!)).

Pending acceptance: actual operation-preserving BBP adapter that
preserves native geometry or documents changes of structure; check
cost for constructing AND validating the digit/phase witness; find an
effective sublinear terminal sign algorithm or an explicit lower bound
only for a specified observer class. Original target unchanged and
terminal sine sign OPEN. Agda exact-head typecheck and Actions receipt
still absent.

## 2026-10-26 BBP punctured-hex small-position constructive adapter
Added scripts/check_pickover_punctured_hex_bbp_exact.py. The eight
actual punctured-nine named points on each of TWO sheets become 16
hexadecimal digit states. Addition/carry and multiplication modulo 16
are transported through this coding, not inferred intrinsic operations.
Exact rational BBP sums use pow(16,k-j,8j+r) on j<=k and exact
rational negative powers on j>k; truncation after j=k+t has
absolute error <= (8/15)*16^(-t). Certifies hexadecimal digits of π
243F6A88 at offsets 0..7. Independent local rational check PASS.
Source root Bailey--Borwein--Plouffe (1995); original source authors
retain mathematical attribution. DASHI contribution is codec/testing.

The literal extraction uses >=4*(k+1) modular fraction terms for
position k. Short index description and prior-digit-free extraction do
not yield poly(log k) work, nor any direct extraction for 1/(2π).
The native antipodal involution remains incompatible with modular-16
negation. Compact symbolic jumping and certified small BBP digits are
complete as separate objects; original Pickover sine sign remains OPEN.
No Agda kernel or exact-head GitHub Actions execution receipt.
