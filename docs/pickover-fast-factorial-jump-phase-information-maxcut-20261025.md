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

## 2026-10-26 verified source ownership audit: analytic J, Kolmogorov, RSA

Do NOT record the analytic jCoarse/jFine seam as unimplemented.
JInvariantAnalyticJCoarseFineObserverExact already supplies the analytic
ModularJFrickeSystem -> finite JTwoPlusNine observer, observer fibre,
Fricke intertwiner (as a field of its record), and associated local27
projection. JInvariantAnalyticObserverSeamCompilerBridgeExact compiles a
supplied observer with scale recognizer into a seam. Validation source
JInvariantAnalyticJCoarseFineObserverValidation.agda records explicit
regression theorems for Fricke, observed fibre and local27. These are
existing formal definitions with prior repository testcheck history,
not a newly needed generic observer. Distinguish that from an actual
constructed Pickover sine sign observer on the real circle, which is
not evidenced in these source files. Also
RiemannG2PhaseResidualRealizationExact.agda explicitly separates exact
finite residual-localization from an analytic literal cosine equality
requiring an inhabited LiteralPhaseModulationWeld.

Native complexity accounting is already present in
SelfIndexingHyperfabricTetrationExact.WeaveComplexity:
programLength, executionLength, normalFormLength, typeWitnessLength,
residualWitnessLength. It is a typed *precursor* to machine-relative
MDL/Kolmogorov, not a computed Kolmogorov optimum or an unconditional
running-time bound. Pair with AdmissibleConsumerMDLHyperfabricExact's
eligibility gate and RecursiveParetoFrontierLiftingExact's multiaxis
dominance before materializing fine fibres.

RSA reuse: RSA260C3OrbitReducerHyperfabricExact explores structured
C3 orbit candidates, but explicitly demands operator co-requirement
closure and final MP=PM rather than promoting candidate symmetry.
RSA260BidiFineIncidencePredictorExact supplies fixed-preparation
family-level fine-incidence predictors and explicitly disclaims complete
instance-level prediction. This is an excellent model for testing
whether C3/jFine coordinates predict the *specific* phase residual:
hold observer acquisition fixed, measure discriminators on controlled
families, use independently certified sine witnesses, and report
counterexamples and costs. RSA factorization, C3 candidate orbit
reduction, and Pickover real angular reduction are separate domains;
no RSA complexity-to-sine theorem follows merely by analogy.

MAX-CUT acceptance requires: existing analytic observer instance
for x={99^(9999!)/(2*pi)}; a signed consumer factorisation through
its retained fine coordinate; exact phase-power transport;
a measured/proved *producer and checker* complexity bound; a concrete
verified Agda kernel execution receipt for the final instance.
None is witnessed by the inspected source merely through general
typechecked parameterized records. Negative controls remain active.

## 2026-10-26 measured certificate-cost Pareto, not just illustrative costs
scripts/check_pickover_actual_certificate_precision_pareto.py performs
independent *integer-only* Machin π enclosure and tests the first decimal
precision (searched from 10 digits) whose floor bounds agree for
N=base^(n!), bases 10 and 99, n=1..5. Local execution passed.
Actual receipts: base10: n=1,2,3 at 10 decimal digits; n=4 at 26
digits; n=5 at 123 digits. Base99: n=1,2 at 10 digits;
n=3 at 15; n=4 at 51; n=5 at 245. Corresponding arctan term
counts are 8,8,8,22,111 and 8,8,13,45,224 respectively.
This is a directly measured small-family producer-work baseline.
The floor parity is computed from certified bounds, not hardcoded.
The precision is first success *under this specific scaled Machin
implementation and search range*, not an information-theoretic minimum.
This witness works for these instances; still no evidence of a
sublinear general factorial remote-sign producer.

RSA C3-orbit/fine-incidence and jFine semantics motivate searching
candidate features but MUST be measured against the above certified
real signs, rejecting collisions. Reuse
SelfIndexingHyperfabricTetrationExact.WeaveComplexity and
AdmissibleConsumerMDLHyperfabricExact as resource and eligibility
owners rather than equating short program length with short runtime.
The prior analytic jCoarse/jFine Fricke and modular-point machinery
is genuine typed prior art; it does not by itself supply an exact
real-circle sine sign at 99^(9999!).

## 2026-10-26 BT-tree cross-pollination and geometric no-go

BT means Bruhat--Tits, not a generic balanced-ternary tree.
Source donors: Physics/Closure/BruhatTitsBraidKPReductionReceipt.agda,
YMBTPathCountingKPThresholdReceipt.agda and
scripts/ym_bt_tree_spectral_gap_harness.py. The PGL2(Q3) BT tree is
4-regular; once an incoming oriented edge is chosen its forward
branching is 3. The boundary is P1(Q3), with affine Z3 residue
cylinders refining by mod 3^d and exactly three children per cylinder.
This geometry is directly relevant to consumer-indexed jFine residual
refinement, but there is NO natural identification of this totally
disconnected p-adic boundary with the real circle R/2πZ.

New executable scripts/check_pickover_bt_tree_refinement.py audits exact
prefix/child coherence for depths <=5, and shows that every power 99^E
vanishes mod 3^d when 2E>=d. Consequently the known opposite-real-sign
witnesses 99^9,99^18 have the SAME 3-adic cylinder for all d<=18
(and in the targeted tested 1..12 range). Tree refinement ALONE cannot
recover a real sine orientation; any claimed breakthrough must supply
an explicit mixed Archimedean/3-adic seam with an efficient residual.
This is a valuable exact non-descent negative control, not a criticism
of the BT geometry or the retained-fibre strategy.

Concretely propose a mixed state
  S=(BT affine end prefix, jCoarse, selected jFine, real residual witness).
Demand: local fibre refinement, factor action T_a*T_b=T_ab,
signed-query adequacy, proof-relevant real-circle bridge, and
five-coordinate WeaveComplexity/consumer-MDL Pareto costs.
Do not count p=7 Yang Mills KP/spectral-gap receipts as analytical
sign proofs, and do not read p-adic closeness as Euclidean closeness.
The original sign sin(99^(9999!)) remains OPEN.

## 2026-10-26: actual fast sine / RSA tractability cut
Added scripts/check_pickover_fast_sine_complex_power.py. It computes
sign(sin(N)) for accessible huge integers N *without evaluating pi*:
start with exact Taylor rational brackets for cos(1)+i*sin(1);
evaluate (e^i)^N by binary complex powering, fixed-point rounding to
S=10^digits, and integer error ticks that upper-bound exact complex
distance. Every multiplication rounds at <=2/S complex norm error;
the transported error bound is e_new=e1+e2+ceil(e1*e2/S)+2 ticks.
Abort a precision trial as soon as the bound becomes vacuous.
Certify sign if |imaginary fixed-point integer|>error ticks.
Independent local Python replay passed for k=1,2,6,24,120, bases 10,99:
base10 precision 20,20,20,50,200 and signs -,-,-,-,-;
base99 precision 20,20,20,50,350 and signs -,-,+,+,-.
For 99^120, 1195 finite complex multiplications and 350 decimal
fixed-point digits sufficed. This beats *repeated sine evaluation*
and avoids computing pi entirely, but not the asymptotic precision
barrier: N=99^(9999!) requires ~1.9956*9999! decimal digits
for generic error-propagation precision. The symbolic operation count
does not bound the bit-width of each intermediate.

This exact-power method is classical de Moivre/exponentiation by
squaring, with DASHI-specific rigorous error ticks and source-level
consumer-MDL benchmarking. The local replay reconstructed the same
algorithm but no direct exact-head Actions or Agda kernel receipt.
RSA parallel: seek a blockwise arithmetic phase certificate or orbit
structure that avoids all-N bit precision, measuring end-to-end
producer/checker complexity; don't mistake C3 orbit candidates for
verified real-sine invariant. A 3-adic internal state is permissible:
only the terminal *correctness theorem* must connect to ordinary sin.

## 2026-10-26: shift-ladder / FFT-SOTA / topology / Shor BIDI correction

Implemented scripts/check_pickover_bit_shift_cocycle_ladder.py:
exact finite Gaussian-ring binary shift (MSB-to-LSB) and modular-power
ladder, factor 9/11 commute; comparison with nonadjacent signed digits
(NAF) as a possible selected-multiply reduction. The 9999! exponent
is stored as a ~118445-bit compact *E*, but the true phase exponent
N=99^E has >6E bits. A binary expansion of N therefore requires
Theta(E) shifts, even with no expansion of N. This distinguishes
fast 99^E description from fast (e^i)^(99^E) execution. NAF helps
popcount/selected multiplication but cannot evade the length of
the binary ladder. Bitshift is an exact algorithmic technique, not
an independent real sine certificate or p-adic shortcut.

State of the art baseline: classical exp by squaring / Chebyshev-angle
doubling plus fast integer multiplication with FFT/NTT and efficient
Payne--Hanek argument reduction. Our Python fixed-point complex
powering is *not* shown better than SOTA; its advantage over naive
sin repeated evaluation is real but not a claim against FFT, GMP,
MPFR, or fast bit-complexity transcendental methods. See Brent and
Zimmermann, Modern Computer Arithmetic, especially §§3.4, 4.3.
A large argument still needs deep bits of 1/pi or equivalent phase
information unless a proved special-property shortcut is identified.

TOPLOGICAL target: universal cover R -> R/2pi Z, deck group Z,
and terminal sign as two open semicircles with zero boundary.
For z=e^(iN), sign(Im z) does not require full lift winding,
but an arbitrary C3 root-of-unity label is insufficient.
Construct a *consumer-relative signed phase cocycle* over rooted
BT/Z3 cylinder tree with a real-angle semantics or direct theorem
identifying its signed consumer. A noncontinuous interpretation or
additional analytic residual is permissible, but exactly what
must be proved, not inferred from the 3-adic tree topology.
Use existing jCoarse/jFine, ConsumerIndexedResidualRefinementExact,
RiemannG2PhaseResidualRealizationExact and BidiResidualApproximationExact.

RSA/Shor actual owners inspected: Crypto/ShorReversiblePowModOracleWeldExact
proves the same RSA powMod observable coincides definitionally with the
order-finding hidden-period oracle; ComputerScience/
RSA260BidiConsumerHypergraphRoadmapExact demands exact replay and
consumer-sufficient action coordinates; Core/
ActiveBidiDiscriminatorLoopExact contains explicit two-way refinement
stages. For Pickover a Shor-type speedup requires a specified modular
or other periodic oracle *plus* a proof that its hidden structure
determines ordinary sine orientation. The ordinary finite C3 action
does NOT furnish that. No quantum advantage or sign theorem claimed.

## 2026-10-26 369 signed-circle versus actual ternary Q9

The user's 3->9->27 observation has an EXACT existing source owner:
DASHI/Foundations/TernaryEndomorphismPhaseQuotientExact.agda proves
27 ternary endomorphism tables divided into nine free C3 output-phase
orbits (27=3*9, with 2 reversible and 7 collapsing normalized codes).
DASHI/Foundations/PhaseQuotientNonaryGroupSeparationExact.agda proves
Q9=T*T as C3*C3 is not group-isomorphic to cyclic C9, despite a
lossless nine-address chart. Preserve this non-identification when
embedding cyclic nine *circle intervals* into the 369 presentation.
The circle also has two zero boundaries (0,pi) and two open sign
chambers; an up/middle/down classifier must be explicitly defined.

In scripts/check_pickover_369_signed_circle_observer.py, exact rational
tests show nested circle 3/9/27 sectors reconstruct exactly by base-three
address truncation. But x=17/36 and y=19/36 lie in the same middle ninth
while sign(sin 2*pi*x)=+1 and sign(sin 2*pi*y)=-1, and after 99th powering
their signs are opposite again. Thus nine-circle-sector label alone
cannot supply the signed answer or a well-defined 99-power transport.
Need retain fine within-sector coordinate (or a consumer-sufficient
smaller symbolic certificate). Import repo's consumer-indexed residual,
JCoarseFineConsumerReduction, nine-phase quotient group separation,
BIDI and proof-carrying analytic phase semantics. This is a local
signed-circle model, not an assumption that Q9 and C9 are one group.

Search target: construct a *consumer congruence for the full 99-power
semigroup*, prove its signed-decoding soundness for the concrete
e^(i*99^(n!)) orbit, and demonstrate an efficient direct jump on
the compressed quotient using bit/FFT or Shor/RSA inspired period
reduction with exact runtime and certificate cost. Do not identify
finite C3 identities with the real exponential without a weld.


## 2026-10-26 signed-zero + genuine 3x3 torque grid + 27-cube MAX-CUT

FIRST PRIOR ART, not a newly invented 369 language:
* DASHI/Foundations/Base369CirclePhase and Base369TriadicPhaseTower:
  cyclic circle address refinement C3 -> C9 -> C27;
* DASHI/Foundations/PhaseQuotientNonaryGroupSeparationExact:
  Q9=(C3)^2 != C9 as a group, though both have nine coordinates;
* MERGED torque PR #1164, Physics/Foundations/TorqueTrialectic369Exact:
  physical 3x3 ordered (lever,force) operator sheet, 27 (output,lever,
  force) bracket voxels, Levi-Civita signed orientation, reversal
  conjugates C3 Fourier phase; ContinuousSO3Torque369BridgeExact
  distinguishes finite classifier from genuine continuous SO3;
* Foundations/SignedZeroTernaryOrientationExact, Biology/
  OrientedZeroWaveTransitionExact and OrientedZeroJetTransitionExact:
  +/-0 directed arrival, undirected neutral, crossing/reflecting jets;
* Analysis/PickoverBase99SignedTailExact and
  scripts/check_pickover_phase_reopening_exact.py ALREADY supply a
  base99 first-nonneutral (49) digit signed continuation with exact
  seven factorial witnesses. Do not reattribute that result as new.

NEW EXACT RATIONAL SIGNED-CIRCLE SPECIALISATION:
Let x in [0,1), p=floor(9x), r={9x}. This p is two *ordered*
base3 trits (3x3 grid), not a claim Q9 and C9 have equal group law.
Then
  {99x}={11r},   x=(p+r)/9.
For c=floor(27x)=3p+b, t={27x}, b in {0,1,2},
  {99x}={11(b+t)/3},  x=(c+t)/27.
These are SAME-OBJECT exact arithmetic equalities. The first two
ternary address digits are shifted out by 99=9*11. The retained
fractional tail and integer carry through factor 11 determine the
new phase. Finite grid/cube address alone does NOT descend to a
well-defined 99-action. The full residual is an adequate carrier;
finding an efficiently producible shorter signed residual is OPEN.

CENTRAL SIGNED-ZERO REFINEMENT:
At every depth d, the central all-ones ternary address is
  h_d=(3^d-1)/2,   digits3(h_d)=(1,1,...,1).
Real coordinate h_d/3^d =1/2-1/(2*3^d) tends to +1/2 from below;
the same integer h_d satisfies 2*h_d+1=3^d and converges to -1/2
in Z3 with v3(h_d+1/2)=d. Numeric rational -1/2 also occurs as
Re(zeta3), but a rational shared across places is NOT an equivalence
between real/3-adic/complex phase dynamics.
For 0<r<1, let x=(h_d+r)/3^d. Then
  x-1/2=(r-1/2)/3^d
and sign(sin(2*pi*x))=sign(sin(2*pi*r)); at r=1/2 both vanish.
The central 3x3 grid cell (11) and central 27 cube address (111)
are therefore the exact self-similar half-turn decision fibre.
The first non-central ternary digit (0 or 2) decides the real
circle sine sign on x in (0,1)\{1/2}; all-ones is undecided
until a noncentral digit appears. x=0 is a separately checked zero.

SIGNED-ZERO GERMS AND TORQUE CROSS-POLLINATION:
Zero sites at x=0,1/2 have four one-sided germs.
At x=0, incoming from negative carries negative sine orientation,
outgoing positive is positive. At x=1/2 the signs reverse. Since
99 is odd and the real circle map x->{99x} has positive local
slope 99, BOTH zero sites and their local one-sided germs are
fixed by this map (for sufficiently small local perturbations).
The determinant/oriented-area analogy matches torque's sign
reversal and C3 conjugation, but the finite torque bracket
orientation is NOT the analytic sine until a proof of semantic
identification is provided.

TOPOLOGICAL NO-GO WITH AN EXPLICIT SHARP GROWTH WITNESS:
For any sign word w of length d, choose terminal y=1/4 and
compose inverse branches
   I_+(y)=(1+y)/99,   I_-(y)=(60+y)/99
in reverse word order. Both are exact branches of T99:x->{99x};
I_+ maps into the positive semicircle, I_- into the negative.
Thus all 2^d binary sign itineraries of length d occur on the
real circle. A deterministic GLOBAL finite quotient with a
decodable sign at EVERY future iterate would need >=2^d states
for every d, impossible for fixed finite size.
This NO-GO applies to universal fixed-state quotients only.
It DOES NOT exclude a special-source orbit reduction for the
single transcendental seed alpha=1/(2*pi), nonuniform certificates,
infinite retained fibres, or a target-specific fast arithmetic jump.

LOCAL CHECKS: scripts/check_pickover_369_torque_signedzero_cocycle.py
has exact rational regression of grid->cube, both 99 cocycles,
all-ones/dual-metric centre, signed-zero germs, >=512 distinct
length-nine itineraries, and first-noncentral-digit decisions.
A structurally typed Agda adapter
DASHI/Analysis/PickoverSignedZeroTorque369GridExact.agda
reuses EXISTING merged torque and signed-zero proofs and
specialises ordered 9/27 projections and orientation reversal;
it does not claim analytic sine correctness. Agda kernel
exact-head check is pending. The existing base99 first-digit
program remains the independent older result.

FACTORIAL-SCALE CRITICAL PATH:
  alpha={1/(2*pi)}; E=9999!
  T99^E(alpha)= {11^E * {9^E * alpha}}.
An exact shift representation reduces no arithmetic by itself:
two E-indexed ternary digits of alpha are still potentially needed
to locate the shifted tail, and factor 11^E adds carries.
Find and PROVE either (A) an efficient query-specific tail-digit
oracle, (B) a special-orbit compressed phase cocycle, or (C) a
different exact terminal sign certificate. Then discharge
producer/checker bit-complexity using repo-native MDL/Pareto BIDI,
not a bare representation-size argument. The target
sign(sin(99^(9999!))) remains OPEN.


## 2026-10-26 ABC six-permutation / twisted C3 signed-cocycle max-cut

### Repo ownership, including recent PR review
* Original established mathematical S3: Dixon & Mortimer (1996),
  Permutation Groups. DASHI/Foundations/TernaryPermutationS3LawsExact.agda
  proves the *six symbol-permutation* group; the six-position action
  below uses the same abstract S3 but permutes POSITION indices in ABC.
  Preserve the distinction between position and symbol actions.
* TernaryHypervoxelPermutationTransportExact supplies depth-stable
  diagonal S3 alphabet transport, with Nekrashevych (2005) precedent.
* HexTruthS3CarrierBridgeExact proves that the nonabelian S3 group
  cannot inherit cyclic HexTruth C6 multiplication, despite a
  lossless six-label carrier chart.
* Reasoning/TrialecticGrothendieckTransitionCocycleExact supplies
  proof-relevant AB->BC->CA->AB C3 transition 2-cell.
* MERGED torque PR #1164 supplies the existing ordered ABC 3x3->27
  Levi-Civita/C3 phase and reflection law.
* Recent NS NSTriadKNTriadS3RealityActionRound35Exact supplies a
  six-permutations x two-reality action, but orbit cardinalities can
  shrink at stabilisers. Do not equate physical NS Fourier reality
  with Pickover sine. Source precedents Leray and Constantin/Foias
  remain native to the donor lane.
* Recent PR #1249 is useful for the exact signed-zero/wave owner and
  for distinguishing P3^3 (54 edges) from cyclic C3^3 (81).
* Recent PR #1250's action-first criterion is reused: a candidate
  orbit or finite chart is not a proved signed-phase action.
* Recent PR #1261 supplies stronger D4h point/lattice symmetry as a
  candidate geometry but is not promoted to a sine invariant.
* Recent PR #1266's revisable observer/signed-consumer no-go informs
  the collision/counterexample and attribution plan; no forced ESD
  import or new universal ontology is implied.
* PR #1244 has independent equivariant C3 quotient/character
  obstructions on abstract horned group boundaries, not a source
  for the ordinary sine phase itself.

### New exact mathematics on signed ternary phases
Represent a real circle coordinate with all three leading trits:
  x=(9A+3B+C+r)/27, A,B,C in {0,1,2}, 0<r<1.
For a positional S3 permutation sigma and v(A,B,C)=9A+3B+C:
  delta_sigma(u) = v(sigma u)-v(u).
This is an additive 1-COBOUNDARY, not an assertion of a nontrivial
group cohomology class:
  delta_{sigma tau}(u)=delta_tau(u)+delta_sigma(tau u).
It preserves the real phase after restoring the rational correction
delta/27. Under T99:x->{99x}:
  kappa_sigma(u) = (11 delta_sigma(u)/3) mod 1
                 = (2(C_sigma-C) mod3)/3.
The target correction takes values in C3 and satisfies the corresponding
S3-action cocycle law. The 99-map consumes two leading ternary trits,
retaining the last digit C and fractional tail r:
  T99(x)={11(C+r)/3}.
This directly binds the 3x3 grid to the 27-cube. However the *full*
real x -> phase relationship still contains r; kappa alone is NOT a
sign-sufficient quotient.

If A,B,C are all distinct, the SIX positional permutations map
bijectively to pairs (permutation parity in C2,
post99 correction in C3). This is a SIX-LABEL CHART, NOT
an isomorphism of groups: S3 is nonabelian C3 rtimes C2, whereas
C2 x C3 is abelian. On degenerate voxels there are stabilisers:
under ABC-position S3, 27 states form 3 size-one, 6 size-three and
1 size-six orbits. The Levi-Civita torque labels are
3 positive, 3 negative and 21 zero. The independent value
complement C2 (A,B,C)->(2-A,2-B,2-C) commutes with position
permutations, and makes SIX orbits on 27 (4 of size6,
one size2, one size1), not uniform twelve-site orbits.
At real fractional tail r in (0,1), the complementary map
also sends r->1-r and x->1-x. It conjugates sine orientation
and negates the C3 carry cocycle; this agrees with
the independently proved signed-zero germ/reflection owner.

EXPLICIT NEGATIVE CONTROL:
ABC=012 and ABC=120 are related by an EVEN 3-cycle; both have
positive torque orientation, but with r=1/2 their ordinary
real circle sine signs are OPPOSITE. Therefore torque/S3
orientation parity alone cannot descend the real-sine consumer.
The weighted delta cocycle is essential.

Rational and carry checks are in
scripts/check_pickover_abc_s3_signed_cocycle.py;
the local exact run passed all six permutations, all 27 cubes,
S3 composition/cocycle law, four fractional tails, 27/12
orbit-stabiliser counts, and depths 1..7 of the bounded
p=3 multiplicative x11 carry transducer. This transducer performs
v_{j+1}=floor((11*d_j+carry_j)/3) with <=11 possible carry
states, and reconstructs 11n exactly on finite trit words;
it is a 3-ADIC finite-word algorithm, not automatically a cheap
real fractional tail oracle.

The Agda source bridge
DASHI/Analysis/PickoverSignedZeroTorque369GridExact.agda now
imports merged torque, proves the cyclic ABC rotate^3,
reflect^2, reflect-rotate-reflect=rotate^2 relations,
and proves cyclic-rotation torque orientation invariance by 27
explicit exhaustive constructor reductions. Existing torque
source proves odd reflection negates orientation and conjugates zeta.
New source remains kernel-pending; user requested no CI focus.

### Analytic REAL seed, no synthetic-substitute promotion
NEW scripts/check_pickover_abc_real_seed.py reuses the existing
Machin 1706 exact rational pi enclosure and verifies REAL
x_n={99^(n!)/(2*pi)} for n=1..6:
  (n,E,ABC,sign) = (1,1,202,-), (2,2,212,-),
  (3,6,001,+), (4,24,022,+), (5,120,222,-),
  (6,720,012,+).
Each has exact C3 carry-cocycle endpoint verification; these six
have first noncentral digit already at depth1 and are therefore
NOT adequate as examples that REQUIRE a deep jFine.

The more discriminating actual-power probe in
scripts/check_pickover_abc_central_real_collision.py
certifies x_k={99^k/(2*pi)} using exact Machin bounds:
  k=7: 110 => positive, depth3
  k=13: 112 => negative, depth3
  k=32: 1112 => negative, depth4
  k=108: 1110 => positive, depth4
  k=151: 1111112 => negative, depth7
  k=153: 1111112 => negative, depth7.
In particular x_108 and x_151 BOTH have central 27-cube prefix
111 but DIFFERENT real sine signs. This is a genuine
source-specific counterexample to coarse 27-centre sufficiency
on the actual orbit family. The consumer-indexed jFine refinement
must reopen the next digit (and sometimes several more digits).
These regressions passed in local integer/rational Python; neither
sign is assumed by comparing arbitrary rationals.

### Critical path to the target
Use the existing S3 ABC group, its C2 orientation parity, the
C3-valued *address-dependent* 99-action correction, and the
consumer-indexed signed-zero BIDI refinement as one source-native
search engine, not a new physical torque interpretation.
But finite S3/C3 and p-adic carry machinery, while efficient,
cannot itself provide the needed real tail r at the astronomic
location alpha=1/(2*pi) shifted by 99^(9999!).
The only unclosed decisive advancement is a source-specific
analytic digit/tail certificate or a different exact
sign oracle with affordable producer+checker bit cost. No
terminal sine sign or RSA/Shor-type hidden period is claimed.


## 2026-10-26 BIDI max-cut: admissible 6-line glue, self-indexed 9^^n, exact fast rational-seed oracle

SOURCE OWNERS (do not re-invent as new finite representation):
* DASHI/Reasoning/RelationalBranchCobordismGeometry.agda and
  TypedHyperfabricPantsGluingBridgeExact.agda: 3+3 six-line pairing/gluing
  is admissible only with an inhabited matching interface (type,
  capacity, phase, provenance); 6 is not automatically the cyclic C6
  group or nonabelian S3 as a group. WavePantsBundleGluingAdapterExact
  has a concrete matching channel and records general sheaf promotion
  as unpaid.
* DASHI/Physics/Foundations/TorqueTrialectic369Exact.agda and
  TernaryPermutationS3LawsExact.agda: ordered 3x3 operator sheet,
  S3 ABC permutation orientation, 27 bracket-cube carrier, retained
  ordered comparison+synthesis; prior tests and latest ABC phase
  cocycle independently check the phase carry under ×99.
* DASHI/Biology/SelfIndexingHyperfabricTetrationExact.agda:
  I_0=unit, I_(n+1)=(I_n -> Fin9), |I_(n+1)|=9^|I_n|;
  selfIndexedSiteCount n = nineTetration n.
  This is genuinely tetrational and NOT merely 27^n, 3^n or 9^n.
  The resident Hyperfibre record has transport AND residualAt;
  WeaveComplexity separates program, execution, normal form, type
  and residual witness lengths. Source: repo-owned design.
* SelfIndexedParetoHyperfabricTetrationExact.agda:
  one ternary objective profile across nine axes has 3^9=19683
  possible profiles, cardinally equal to the three-voxel hyperfabric,
  without claiming identity of their semantics.
* Core/ActiveBidiDiscriminatorLoopExact.agda:
  live hypotheses -> collision -> discriminator -> independent
  consumer check -> residual refinement -> selectively reopen.
* Crypto/ShorReversiblePowModOracleWeldExact.agda:
  SAME-OBJECT reversible modular-power hidden-period semantics,
  not an automatic quantum oracle for sin of an integer.

NEW PROOF-CARRYING POSITIVE CONTROL (EXACT, executable):
scripts/check_pickover_tetrated9_bidi_periodic_oracle.py
uses rational phase x=a/q, with gcd(99,q)=1 and a VERIFIED period t:
99^t = 1 mod q. For E=9999!, n any Nat,
  e = n! mod t,  r = a * (99^e mod q) mod q.
Then, by modular congruence, r/q is exactly
 {a*99^(n!)/q} and the sign of sin(2*pi*r/q) is
  positive if 0 < 2r < q, negative if q < 2r < 2q,
  zero at r=0 or (when q is even) 2r=q.
The script verifies each period by pow(99,t,q)==1, and
compares the compressed oracle to direct modular powering on
factorials n=1..8. It computes E mod t through exactly n-1
bounded-modulus multiplications, hence WITHOUT building E or 99^E.
No universality/complexity-class claim.

FULL TARGET-SIZED RATIONAL FINITE-SEED RECEIPTS:
  q=101,  a=1,  t=100:   e=0,    r=1,     sign=+
  q=20123,a=1,  t=20122: e=5752, r=18371, sign=-
  q=20183,a=1,  t=20182: e=4834, r=2114,  sign=+
  q=200,  a=100,t=80:    e=0,    r=100,   sign=0
  q=200,  a=99, t=80:    e=0,    r=99,    sign=+
  q=200,  a=101,t=80:    e=0,    r=101,   sign=-
These are EXACT signs of sin(2*pi*a*99^(9999!)/q), NOT
sign(sin(99^(9999!))). The last three certify a signed-zero
half-turn with approaches from either side after an odd-period
factorial jump. Run source tested locally in a materially equivalent
copy; exact-head GitHub Actions / Agda receipts not claimed.

BIDI REJECTIONS (positive controls + falsifiers):
* For q=20123, the source-seed values a=1 and a=6 lie in
  the same 3/9/27/81/243 cell at time zero but have opposite
  signs after the factorial jump, as certified by modular
  period arithmetic. This rejects all those fixed-depth
  coarse-only signed consumers.
* q=20123, nearest rational a=3203 to 1/(2*pi), certified
  as such with existing Machin rational bounds. The rational
  99^(n!) surrogate signs n=1..4 are [-,+,-,+], whereas
  the actual exact Machin real-seed signs are [-,-,+,+].
  Thus even an initially CLOSE finite-period surrogate is
  NOT an analytic same-object oracle. It fails at n=2.
* A general rational seed is not the actual irrational
  alpha=1/(2*pi). A periodic finite-state modular reducer is
  not promoted to the original sine-sign certificate by
  representational similarity, an S3 cocycle, an ABC diagram,
  or a cost saving measured on other seeds.

CONDITIONAL POSITIVE COMPLETION THEOREM:
Given an independently source-validated arithmetic phase state for
alpha=1/(2*pi) with (i) certified same-object powering,
(ii) an effectively computable exponent reduction or compressed
orbit jump, (iii) signed-decoding soundness for the terminal
consumer, and (iv) measured bit cost, the exact finite protocol
here makes sin(99^(9999!)) a tractable query. In the rational
periodic specialization all four obligations are discharged
relative to *that rational source*, thereby proving tractability
is possible with this architecture in the appropriate domain.
The outstanding bottleneck is SOURCE ADEQUACY of a shortcut for
the actual irrational alpha, NOT the existence of another tower
representation or abstract residual record.

RESEARCH PARETO/BIDI RANK:
A. Search certified analytic/algebraic recurrence for far digits
   of 1/(2*pi) at factorial power positions (high value, open).
B. Search source-specific phase cocycle/action with inexpensive
   verified signed consumer (high value, open).
C. Explore RSA/Shor order-finding only when a genuinely periodic
   actual phase observable is constructed, not by fiat.
D. Retain Machin and fixed-point exp(i) powering as independently
   certified small-case controls.
E. Do not materialise I_9: 9^^9 is a CAPACITY/TYPE theorem.
   Construct a costed on-demand evaluator for the selected fibre,
   and require a paid correctness and depth-independent cost theorem.
