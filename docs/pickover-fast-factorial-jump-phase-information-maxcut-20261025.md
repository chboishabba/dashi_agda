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

## 2026-10-26 C3 geometric pi route
Existing source owners JMDArchimedesDelta369FixedLocusBridgeExact,
JInvariant369ReflectionEquivarianceExact, and
BishopMachinPiRationalWindowExact provide typed polygon/phase reflection
and real-arctangent donors. Classical equilateral 60-degree angle proves
pi=6*atan(1/sqrt(3))=2*sqrt(3)*sum_{k>=0}(-1)^k/((2k+1)*3^k).
New scripts/check_pickover_c3_angle_pi_windows.py constructs integer-
sqrt rational brackets for sqrt3, monotone rational arctan alternating
bounds and exact base10 small-instance floor parity. Workflow requested,
but no CI receipt, Agda kernel or original terminal sine-sign proof.

For normalized analytic phase x=N/(2pi) mod1, represent C3 sector
x=j/3+r (j in {0,1,2}, 0<=r<1/3). Under m-fold rotation,
m*x=(m*j)/3+m*r mod1. The missing theorem is an efficient residual
update; the C3 label alone is not a sign oracle and conventional
interval width still multiplies by m. Ordinary Machin arctan(1/5)
series converges more rapidly per term than arctan(1/sqrt3).
Do not conflate pi-from-geometry with sublinear remote digit access.
This C3/pi mathematical identity is classical, DASHI contributes
concrete source reuse and rational checks.

## 2026-10-26: factor fibration via existing intersectional query adequacy
The relevant original donor is DASHI/Core/IntersectionalNonFactorability.agda
(conceptual precedent Kimberle Crenshaw 1991; DASHI's mathematical
fibre-collision abstraction is not a theorem of Crenshaw). Also reuse
DASHI/Core/QueryIndexedProjectionAdequacyExact.agda
(conceptual precedent David Blackwell 1953),
BalancedTernaryC2C3DihedralCodecBridgeExact.agda and
Physics/WaveAlgorithmLift.agda. The correct diagnosis is not that
binary encoding inherently forgets zero: the support/sign fibre is
lossless, but the support-only projection forgets orientation. In the
wave lane zero is zero amplitude, not an automatically interchangeable
third root of unity.

Exact factor-fibration rational test:
  x=j/3+r mod 1, j=floor(3x), 0<=r<1/3.
  T_m(j,r)=split(m*(j/3+r) mod1).
  T_9∘T_11=T_99=T_11∘T_9.
The splitter/assembler round trip is exact on rational phases. Coarse
C3 sector alone fails signed-query adequacy: x=5/12 and y=7/12
occupy the same middle sector but have opposite sine orientations.
This is an instance of repo-owned NonFactorabilityWitness:
postcomposition/recharting the coarse sector cannot repair the
collision. Retaining r makes the state adequate for the exact phase
query, *provided it can be computed*. This last cost remains the
central unresolved algorithmic requirement.

This is explicitly separate from a source-specific analytic proof for
alpha=1/(2*pi), or an efficient residual update through 99^(n*n!).
The multiplication commuting square is exact; neither cheap signed
computation nor original 9999! sign is claimed. Local Python fixture
requires execution and the new Agda adapter is not kernel checked.

## 2026-10-26 correction: actual recursive residual/refinement owners

The PRIMARY owner is DASHI/Core/ConsumerIndexedResidualRefinementExact.agda:
declare consumer F, test coarse O for sufficiency, exhibit an F-relevant
collision, attach typed residual R, and show joint (O,R) adequacy.
Its necessity theorem requires every adequate observer to distinguish
each consumer-relevant collision. Source precedents: Blackwell 1953,
Cousot--Cousot abstract interpretation 1977; mathematical formulation
is DASHI's and not attributed to those sources.

DASHI/Core/BidiResidualApproximationExact.agda additionally owns
monotone hidden-state fibre refinement and constraint propagation.
DASHI/Codec/TriadicPAdicCodec and
Docs/TriadicPAdicCodecFormalisation.md own ternary sheets,
support/sign masks, zero as fixed point, and prefix refinement.
DASHI/Biology/SelfIndexingHyperfabricTetrationExact.agda owns
retained residualAt across tower morphisms.
DASHI/Core/IntersectionalNonFactorability.agda is a SECONDARY
nonfactorability/no-postprocessing donor, not the original residual
construction. Preserve Kimberle Crenshaw's conceptual source credit
without attributing the residual mathematics to her.

Pickover specialization: F = terminal orientation query on exact
analytic e^(iN). O = C3 coarse sector. R = within-sector phase
coordinate or a smaller separately certified sufficient witness.
An exact (O,R) reconstruction is algebraically adequate, but still
requires proof that R's producer is efficient for N=99^(9999!).
The source's consumer-relative necessity theorem is stronger and
better targeted than a generic assertion that all coarse encodings
must lose information.

## 2026-10-26 jCoarse/jFine and consumer-admissible MDL/Pareto extension

EXISTING PRIMARY OWNER: DASHI/Biology/JCoarseFineConsumerReductionBridgeExact.agda
imports CoarseFineRelativeFibreExact and ConsumerRelativeReductionKernelExact,
proving that jFine is a relative factor over jCoarse, that absolute depth
splits into coarse+fine depth, and that fine-sensitive consumers defeat
coarse-only reduction. The analytic observer counterpart is
DASHI/Moonshine/JInvariantAnalyticJCoarseFineObserverExact.agda:
finite structured j observation plus a Fricke equivariance interface,
without an unjustified inverse to analytic modular points.
This is the precise prior art, NOT a fresh coarse/fine analogy.
Avoid identifying the finite J model with the real circle phase.

COST/OPTIMISATION OWNERS: Core/AdmissibleConsumerMDLHyperfabricExact.agda
requires hard admissibility and consumer sufficiency BEFORE minimising MDL;
Core/RecursiveParetoFrontierLiftingExact.agda keeps separate cost axes and
lifts only residual-relevant coordinates. P-vs-NP PR #1129 distinguishes
representation description, materialisation and actual runtime; PR #1040
demonstrates that identity observers can be efficient/lossless. This is a
cost model and model-search heuristic, NOT a P≠NP theorem or a bound on
Kolmogorov complexity of pi or the original target.

Acceptance coordinates for an eligible signed-phase certificate:
(1) description bits under a fixed stated coding convention,
(2) producer time/bit complexity, (3) verifier cost,
(4) retained residual size, (5) refinement/sensitivity coverage.
A candidate with insufficient signed-query information is INELIGIBLE even
if arbitrarily concise. A candidate dominated on every cost coordinate
is Pareto-pruned. New runnable fixture
scripts/check_pickover_jcoarse_jfine_mdl_pareto.py demonstrates collision
in the middle C3 sector and the eligible frontier on ILLUSTRATIVE
cost values. These costs are not measured physical timings.

The actual target is to synthesize a rigorously analytic adequate
jCoarse/jFine-compatible retained residual that survives factor-fibred
99^E jumps with a sublinear producer+checker. Neither a short description
of E nor high-dimensional carrier cardinality automatically implies this.
No new real-phase sign or kernel verification receipt is claimed.
