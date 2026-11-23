# Constructive constants and actual Klein-j max-cut — 18 November 2026

## 23 November 2026 — Bishop fast-π source consumer: RH atomic biharmonic rational-angle square

The original constructive constants/fast π PR #1529 provides the rational certificates and split-tree arithmetic, **not** the RH analytic-zero theorem. New cross-programme consumer is in [RH PR #1533](https://github.com/chboishabba/dashi_agda/pull/1533), `Docs/proofs/RHFourWindowBishopPiNineDOFCommutingSquare20261123.md`, with source-written `DASHI/Analysis/RHFourWindowBiharmonicFiniteCubeExact.agda` and local SymPy checker `scripts/check_rh_bishop_pi_biharmonic_h05_square_20261123.py`. The actual finite H05 cube owner remains TOE #1291, ported byte-identically into RH branch for a real dependency rather than reinvented.

The historical Machin/constructive Bishop real `pi_B` has the **actual-source rational** bracket (from `DASHI/Foundations/BishopMachinPiRationalWindowExact.agda`):
```text
281476/89625 < pi_B < 589067/187500,
p* = 93841671/29875000,
delta* = 49013/89625000,
|p*-pi_B| < delta*.
```
The original Lean RH four-window atomic projector collapses `(-40/117,0,160/351,-40/351)=(40/351)(-3,0,4,-1)` to the **negative squared centered discrete Laplacian** `-(20/351)(T+T^{-1}-2)^2` on the now-evenly-spaced surviving centres `0,h,2h`. The **finite algebra** is valid for any positive real h, independent of π and any π approximation:
```text
F_h(q) = -(320/351) sin(h q/2)^4.
```
Substitute rational `h=p*/2`, q=4: exact `F=-(320/351)sin(p*)^4`. **ONLY IF** a source-checked semantic identity `pi_B = Lean.Real.pi` is supplied, sine 1-Lipschitz and `sin(pi)=0` give the fourth-order explicit bound `|F|<= (320/351)*(delta*)^4 < 8.16e-14`. This is a certified rational angle control *conditional on the same-object π equality*, not a finite Fourier zero at rational h, and not an actual ζ(s) zero.

The existing `DASHI/Interop/BishopMachinPiLeanSemanticReceiptExact.agda` states `leanKernelReceiptObserved=false`, `agdaKernelReceiptForLeanTheoremObserved=false`, `serializedCrossProverSameObjectWitnessObserved=false`. This aligns with this π programme's **existing open Bishop π-period identity, classical/Lean semantic transport and kernel receipt**. The binary P/Q/B/T split tree, Chudnovsky evaluator, rational certificates and benchmarking do not substitute for these proofs; retain them as original algorithmic producers. No new π algorithm or CM/Klein-j analytic theorem claimed here.

Next π-facing weld: original Bishop Machin π source equal to classical Real.pi via same analytic trigonometric period/atan identity with constructive error and an independently kernel-checked semantic receipt. Then use the existing rational-width intervals to transport exact angular source coordinates and spectral notch errors through a nonidentity refinement face. The RH programme's actual ζ-zero signed `FarExact`, μ, and local slack remain independent/unproved. Keep CM/j max-cut roadmap and all existing negative controls unchanged.

---

## Exact repo owners reused; no new carrier
- DASHI/Physics/Closure/TriadicEisensteinTransformationTheorem.agda:
  all-SL2(Z) transformation from finite lattice-index bijection,
  plus summand/reindex/factor hypotheses of the analytic model.
- DASHI/Analysis/SetoidEisensteinTransformationExact.agda:
  original transformation transported to setoid equality.
- DASHI/Moonshine/EisensteinDiscriminantWeight12Exact.agda:
  D = E4^3-E6^2 transforms with weight 12.
- DASHI/Moonshine/DeltaNormalizedWeight12SameObjectExact.agda:
  normalized Delta and eta^24 boundary; pinned Lean parity is not
  an Agda kernel proof of the analytic identity.
- DASHI/Moonshine/JInvariantAnalyticNormalizedKleinAdapterExact.agda:
  original standard-j is E4^3/normalizedDelta.
- DASHI/Moonshine/JInvariantBishopLatticeEisensteinSameObjectCompilerExact.agda:
  q-series / lattice-sum equality and concrete summation are still
  explicit missing fields.
- DASHI/Foundations/BishopNatSquareRootRegularFloorExact.agda and
  BishopNatSquareRootSemanticSquareExact.agda:
  original Nat square-root and semantic square identity. Do not
  replace with a second constructed real.

## New Agda proof surfaces (COMPILER-PENDING)
1. DASHI/Moonshine/JInvariantEllipticFixedPointCompilerExact.agda
   derives E6(i)=0 and E4(omega)=0 from the ORIGINAL Eisenstein
   transformation theorem and explicit fixedpoint/nontrivial-factor
   cancellation inputs. Neither E4/E6 modularity nor the desired
   vanishing is assumed as a field.
2. DASHI/Moonshine/JInvariantEllipticStandardJValuesCompilerExact.agda
   composes the original normalized standard-j quotient to derive
   j(omega)=0 and j(i)=1728 with explicit field-cancellation,
   normalized-1728 and nonzero-discriminant witnesses. Neither j-value
   is accepted as a hypothesis, and none is asserted unconditionally.
3. DASHI/Foundations/HypergeometricBSplitIntegerMergeExact.agda
   integer four-tuple P,Q,B,T merge, associativity ring lemma,
   structural split tree and tree rotation identity. Finite
   rational-prefix semantic correctness and Bishop limits remain open.
4. DASHI/Foundations/BishopPellLucasIntegerInvariantExact.agda
   Pell norm-one squaring/doubling theorem and D=2,3,6 integer seeds.
   The existing Bishop sqrt is not redefined. Rational interval
   soundness, dyadic precision and same-real uniqueness remain open.

NO AGDA COMPILER IS INSTALLED HERE. These files are mathematical
source implementations, not kernel-accepted theorem claims.

## Exact independent SymPy checks, completed locally
- Six Legendre/anharmonic orbit maps preserve
  256*(1-lambda+lambda^2)^3/[lambda^2*(1-lambda)^2].
- lambda=1/2 yields exactly 1728.
- lambda=(1 +/- sqrt(-3))/2 yields exactly zero.
- At elliptic points: i^6=-1; (omega+1)^4 !=1.
- Exact -640320^3 integer equality holds, but NOT the
  analytic CM singular-modulus identification.
- Apéry product ratio must be k/[2(2k-1)] for k>=2,
  before multiplication by its 1/k^3 coefficient.
  The proposed k/[4(2k-1)] was wrong by a factor of 2.

The Legendre evaluation still requires the original analytic
lambda(i)=1/2 and lambda(omega) satisfying
lambda^2-lambda+1=0 to become an actual j(tau) theorem;
the E4/E6 fixedpoint approach avoids those lambda identities.

## Generic hypergeometric reference
scripts/check_bishop_generic_hypergeometric_pell.py tests the integer
four-tuple split against independent exact rational finite prefixes
for atan(1/5), exp(1), log(2), and Apery zeta(3), including
nonzero-start indices and explicit 24-prefix negative controls.
This is finite arithmetic, not equality of the original Bishop
Cauchy limits or global series-to-function identification.

Pell recurrence P'=P^2+D*Q^2, Q'=2*P*Q and
P^2-D*Q^2=1 gives rational brackets [DQ/P,P/Q] of exact
width 1/(PQ). Exact independent tests for D=2,3,6 pass.

Nine-run median isolated local benchmarks, comparing Pell integer
recurrence with a dyadic integer-isqrt enclosure at comparable
*width*, not comparing against Agda's existing Bishop implementation:

| D | Iterations | Certified bits >= | Pell ms | dyadic isqrt ms |
|---:|---:|---:|---:|---:|
| 2 | 5 | 160 | 0.0020 | 0.0068 |
| 2 | 7 | 648 | 0.0047 | 0.0207 |
| 2 | 9 | 2601 | 0.0193 | 0.1259 |
| 3 | 5 | 118 | 0.0019 | 0.0058 |
| 3 | 7 | 483 | 0.0044 | 0.0172 |
| 3 | 9 | 1942 | 0.0156 | 0.0856 |
| 6 | 5 | 208 | 0.0020 | 0.0072 |
| 6 | 7 | 843 | 0.0053 | 0.0256 |
| 6 | 9 | 3383 | 0.0248 | 0.1788 |

These are tiny run-times and subject to Python timer noise;
no claim of a measured advantage over the repository's own square
root producer is made. The recurrence uses n+1 Newton iterations
starting at 1 for D=2, not 2^n Newton iterations.

## Analytic CM value at discriminant -163 remains separate
The exact integer -640320^3 is the known class-number-one
singular modulus, but proving j((1+sqrt(-163))/2) equals it
requires:
1. a literal imaginary quadratic point in the original Bishop
   upper-half-plane carrier;
2. CM/degree-one class-polynomial evaluation (or equivalent);
3. q/lattice series same-object and j normalization;
4. identification and exact polynomial/root witness;
5. pinned kernel acceptance.

Do not promote a stored integer or numerical q-series agreement
to a same-function j theorem.

## Primary references
- J.-P. Serre, A Course in Arithmetic, Springer 1973,
  DOI 10.1007/978-1-4684-9884-4.
- T. Miyake, Modular Forms, Springer 2006,
  DOI 10.1007/3-540-29593-3.
- J. H. Silverman, Advanced Topics in the Arithmetic of Elliptic
  Curves (CM background).
- Notes on Hilbert class polynomials and -163:
  https://flintlib.org/doc/acb_modular/class-polynomials.html
- Existing DASHI primary-source/attribution ledger:
  JInvariantSourceAtlasExact.agda.

## Acceptance next
A. Run pinned agda --safe on the four new modules; fix ALL type errors.
B. Discharge concrete S/ST fixedpoint and complex factor cancellation.
C. Construct concrete E4/E6 q-series/lattice same-carrier input and
   analytic discriminant nonvanishing, then instantiate j(i),j(omega).
D. Separately prove the -163 class polynomial same-original j identity.
E. Connect finite hypergeometric and Pell accelerators to the
   existing Bishop reals through exact prefix + setoid uniqueness.
No part of YM.REAL R2-R6 is claimed closed by this work.


## 18 Nov max-cut continuation: CM -163 short integer certificate

New source work after the first ledger:
- scripts/check_cm163_dyadic_j_integer_certificate.py:
  exact outward dyadic q-series enclosure at 128/160/256 bits and
  full reduced-form enumeration. At 128 bits j is enclosed to a
  half-integer interval around -640320^3; at 256 bits width is
  approximately 1.45e-31. The acceptance path uses NO floats.
- DASHI/Moonshine/JInvariantCM163DyadicHalfIntegerExact.agda:
  --safe integer endpoint inequalities, NO analytic-producer promotion.
- Docs/proofs/JInvariantCM163CertifiedIntegerMaxCut20261118.md:
  complete reduced-form a<=7 proof and exact tail bounds.
- DASHI/Moonshine/JInvariantEllipticProofRelevantKleinWeldExact.agda:
  uses JInvariantProofRelevantKleinJExact's actual proof-relevant
  quotient. CertifiedPoint includes a same-source normalized-Delta
  nonzero witness; the original standardJ equivalence is definitional.
  In particular, no totalized quotient without point-level safety
  enters the public special-value consumer.

This changes the preferred -163 proof path: compute h(-163)=1
from reduced forms, appeal to the classical CM *integrality* theorem,
and combine with a rigorously bounded q-series interval smaller than
one integer. No explicit enormous class-polynomial coefficient
calculation is required to establish the classical result.

The CM theorem, same-carrier q/Delta/E4/E6 identification, actual
Bishop pi period and all newly source-written Agda modules are
still formal Agda validation/proof obligations. Numeric source
passes do not automatically discharge these.


## 20 November 2026 — controlling max-cut update (supersedes older gate lists)

Audited master 116cd7de01b8a0da03703b3bb8db79c67fd15b50 and PR #1529
head 41dae3b4ac39cec95da028d753db9cf365b3d863 before this packet.
Do not reopen source owners simply because they are absent on an older
research branch. Integrate their dependency closure, preserving provenance.

### K05: concrete total-degree route, no infinite derivative interchange

Use BishopMachinOriginalCayleyFormalSeriesExact and
BishopMachinCayleyEquationForcesCoefficientsExact on the original rational
complex carrier. BishopMachinExistingCayleyReuseExact already proves the
rational phase composition; BishopMachinOppositeCayleyConventionExact
already handles conjugate convention. The terminal consumer is
BishopMachinTwoPointCayleyCompositionExact. Only the two original Bishop
atan evaluations are inputs. The earlier derivative route is optional.

Put Y=iX. Then 2i atan(X)=2 sum_{k odd >=1} Y^k/k. In the formal
factorial exponential composition let c_n denote the coefficient of Y^n.
Finite polynomial differentiation and product rule give
n c_n = 2 sum_{k odd,1<=k<=n} c_(n-k), c_0=1.
Induction gives c_n=2 for n>=1: at n=2m the sum has m terms each 2;
at n=2m+1 the sum has m terms each 2 and the constant 1.
Thus (1-iX) F=1+iX coefficientwise. This matches the existing
Cayley owner, not a new series definition.

For rho=3/4 the *absolute* nested sum at rho is bounded by
exp(2 rho/(1-rho^2))=exp(24/7)<exp(4)<81 (e<3 by factorial tail).
At any |t|<=1/2, the portion with total degree >N is bounded
by 81*(|t|/rho)^(N+1) <=81*(2/3)^(N+1).
This bound follows termwise on every finite rectangle of the nested
sum: a monomial of degree d>N contributes at most (|t|/rho)^(N+1)
times its positive weight at rho. No new derivative interchange,
integration theorem, or unrestricted summation axiom is required.
The original rectangular partials containing every monomial of
degree <=N differ from that finite total-degree polynomial by at
most this bound. Original factorial-exp convergence and continuity
at the original atan limit, plus native Sequence uniqueness, suffice
once these finite combinatorial bounds are transported. The geometric
Cayley tail is <=2 |t|^(N+1)/(1-|t|).

Committed scripts/check_cayley_composition_tail.py at
061c8fdbddf028ac6bfe84f96e1a0d08550618f7. Local execution:
independent nested factorial convolution equals recurrence and canonical
coefficients through degrees 0,1,2,8,16,32. Exact rational geometric
tail checks and 10^-40 budget at t=1/2,1/5,1/239 passed.
Selected doubling cutoffs N=256,128,32 respectively. Whole script
wall time 0.03579 seconds in this run (not a benchmark median).
This is a finite executable reference and all-degree mathematical
argument; NOT a kernel proof of formal differentiation or evaluation
transport. No claim that original Cayley equality is already inhabited.

### Reconciled producer ledger (current priorities)

| Gate | State | Actual owner / required next deliverable |
|---|---|---|
| K04d | SOURCE IMPLEMENTED on master | BishopOriginalNegativeLogTerminalFromMeshExact.originalBishopNegativeLogExponentialGap; integrate original dependency closure |
| K05.01-04 | SOURCE EXISTS | BishopRound11SignedFactorialDegreeBinomialExact, BishopK04dK05NativeProductDischargeExact, original Cayley coefficient owners |
| K05.05 | SOURCE EXISTS, derivative series only | BishopOriginalLogAtanDerivativeLimitValuesExact; derivative of limit not required by preferred total-degree route |
| K05.06 | OPEN Agda | Literal nested factorial composition coefficient recurrence and all-degree identification |
| K05.07 | OPEN Agda | finite rectangle/total-degree bound, native Sequence limit transport; reuse original exp continuity and atan tails |
| K05.08-10 | DOWNSTREAM | instantiate two original atan values, existing first-positive-zero consumer |
| J1 | SOURCE EXISTS | JInvariantBishopQFromUnitPhaseExact and JInvariantBishopTrigUnitPhaseExact; actual phase and radius inputs |
| J2 | SOURCE EXISTS | JInvariantEisensteinBishopSetoidSeriesExact and JInvariantEisensteinSameCarrierLimitKleinJExact |
| J3 | OPEN | original q/lattice equality, literal modular fixed points and local nonzero discriminant |
| CM1 | INTERFACE EXISTS | TraceOfSingularModuliBridge.CMArithmetic; actual reduced-class carrier and reduction equivalence |
| CM2 | OPEN | classical CM algebraic integrality and degree/class-number theorem on original j |
| CM3 | FINITE CERTIFICATE | existing -163 dyadic checker; analytic interval transport still open |
| CH1 | EXECUTABLE REFERENCE | scripts/check_chudnovsky_exact.py, commit 41dae3b4ac39cec95da028d753db9cf365b3d863; finite prefix and alternating tail |
| CH2 | OPEN | Chudnovsky modular hypergeometric and derivative identity, same original pi; CM value alone does not suffice |
| A1 | OPEN | exact-head pinned local Agda --safe acceptance; no compiler or Nix in current runtime |

Chudnovsky search included name and constants 13591409, 545140134, 640320
in the indexed Agda/Lean defaults; no older concrete implementation
recovered, not an exhaustive historical-branch exclusion.
Keep YM.REAL independent; no physical or Clay gate promotion.
Attribution: original Bishop/Bridges and Murray/Csimma; Machin, Cauchy,
D. V. and G. V. Chudnovsky; actual DASHI owners above and
Docs/proofs/BishopK04dK05TerminalCompositionExactProof20261106.md
(the prior formal-composition strategy). This packet tightens the
finite total-degree majorant, not authorship of the classical identity.


## 20 November: native 369 / Monster reconciliation (preferred over duplicate FLM construction)

Actual existing owner JInvariant369NormalizedAnalyticRendererExact
(blob ab27df5e025df09037c1efc7a4a07bcab2a2e166):
standardRendererJValueIsStandardJ A N Q O tau = refl.
Point and scalar carriers are also definitionally identical. This is a
same-object compiler for standard j, NOT an instantiated Bishop analytic model.
Its boundary explicitly marks concrete readout and reflection alignment false.
JInvariantFormulaic369ModularReplicationExact consumes jInvariant as a field;
it proves observer invariance from that field, not its analytic inhabitant.
JInvariant369ConsolidatedNextStageExact retains independent C6 phase,
principal-level C27 and signed multiplicity; scalar j non-descent is essential.

Monster369ZetaSameObjectWeldExact (blob 21714177659928bf7ed90989b785d709751bd60a)
already identifies Fourier zeta, Monster 3B selected phase, inertia scalar,
and finite Schrodinger modulation with the same exact cyclotomic scalar.
Literal VOA eigenspace identity is definitional on an inhabited source.
Actual H_zeta/W_zeta recognition and linear multiplicity intertwiner remain open.
JInvariant369Zeta6561MonsterCrosswalkExact (blob 669c3379cc8e563e26d87617ee69aa0bcbcb7fd8)
connects 6561, 65610, 196830, 196883 and 196884 with exact finite witnesses;
it explicitly separates cyclotomic zeta from Riemann zeta and marks the
Riemann-zeta/divisor-series/Eisenstein weld unpaid here.
JInvariantLambdaOrbitBase369BridgeExact (blob a226f222f57fb192c5e32a96c968dc5c152711b6)
already owns the six lambda orbit labels, three complement pairs and orientation
involution with Base369 HexTruth. Its rational-function invariance and actual
analytic lambda identification are distinct gaps.

Reuse #1029 (consolidated 369), #1472 (selected FLM/Y443), and
docs/j369-b3-existing-voa-modular-fine-level-crosspollination-maxcut.md
for exact B3 generator orientation, finite orbifold sector action and
principal-level non-descent. Do not promote finite sector action into analytic
twisted modularity. JMDArchimedesDelta369FixedLocusBridgeExact already
consumes pinned Lean eta24/Delta/reflection receipts; retain JMD attribution
and separate Lean proof from Bishop/Agda carrier transport.

J3 split: (a) normalized renderer same-object compiler EXISTS;
(b) original analytic modular model, q/lattice equality and nonzero Delta
remain to instantiate; (c) phase/reflection readout alignment remains open.
Monster full Aut, 194 traces and FLM construction are NOT prerequisites
for evaluating the existing standard-j quotient. CM2 remains open unless
actual integral modular-polynomial or CM integrality/class-degree proof is
found. K05.06/07 remain open in Agda. No kernel execution in this packet.


## 20 November — 369 homogeneous lambda integer kernel implementation

JInvariantLambdaOrbitIntegerKernelExact.agda (implementation 7c4d817d2ffb,
integer constructor alignment 991e2223b54b) imports the original
LambdaOrbitTag and hexToLambdaOrbit. No duplicate orbit carrier.
For lambda=a/b, homogeneously j=256 Q^3/D where
Q=a^2-ab+b^2 and D=(ab(b-a))^2. Both Q and D are individually
invariant under all six existing tag transforms:
(a,b), (b,b-a), (a-b,a), (b-a,b), (a,a-b), (b,a).
Source implements 12 integer ring proofs, numerator equality,
nonzero denominator transport and HexTruth-indexed numerator/denominator
theorems. No division by zero or analytic lambda assertion.
Independent local SymPy expansion of all 12 identities PASS (41.25 ms);
Fraction regression over -32<=a,b<=32, D!=0: 24,192 orbit checks PASS
(50.68 ms). Single-run timings, not compiler timings. Agda and Nix
not available locally; exact-head kernel acceptance OPEN.
Primary mathematical attribution: classical Legendre elliptic curve
j-invariant, Serre A Course in Arithmetic (1973); original repo
JInvariantLambdaOrbitBase369BridgeExact, JInvariantSourceAtlasExact.
J3 algebraic lambda orbit subgate: source implemented, compiler pending.
Remaining: actual rational quotient/field interpretation, analytic
lambda(tau) identification with original normalized E4^3/Delta, local
apartness and selected modular fixed points; K05.06/07, CM integrality,
CH2 and local pinned acceptance unchanged. Do not confuse this
homogeneous integer result with concrete analytic modularity.


## 20 November — binary/ternary Eisenstein norm and S3 sign weld
New source JInvariantLambdaCyclotomicParityExact.agda, commit
7b65c67158ce7700b28d165e47f782af105bd4ac, imports original
C3CyclotomicAmplitudeAlgebraExact and LambdaOrbitBase369BridgeExact.
Q is the original rational Eisenstein norm. R(a,b)=(-b,a-b)
is multiplication by zeta; S(a,b)=(b,a) is zeta times conjugation.
Source proves R^3=S^2=I, SRS=R^2, norm invariance, and all six
normalised action representatives agree with raw orbit representatives
up to sign. V=ab(b-a) has V(Rx)=V(x), V(Sx)=-V(x).
D=V^2. Thus j=2^8 Q^3/V^2. C6 phase indexing is not the
nonabelian S3 action; exponent 3 alone does not prove symmetry.
Local independent SymPy execution: 22 scalar polynomial checks PASS,
22.26 ms single run; no Agda executable. No kernel promotion.
Prior art: Washington Introduction to Cyclotomic Fields; classical
Legendre invariant and Vandermonde sign; repository
Base369BinaryTernaryRefinement, PolynomialC3S3RationalCharacterAlgebraExact,
PolynomialVandermondeOrbitSignCharacterExact, C3CyclotomicAmplitudeAlgebraExact.
Also see EisensteinLeanJZeroCMOrderActionReceiptExact: Lean PR #69
native algebraic j=0 and CM endomorphism source, kernel pending per receipt.
This is not analytic j(omega) identification.
Next: actual rational proof-relevant quotient, integer-to-rational
embedding consistency, analytic lambda identification. K05, CM and CH2
remain open. No duplicate cyclotomic carrier or physical claims.


## 20 November — executable analytic lattice / 369 ramification weld

Current head before packet: 9a1d41677029b7c07a19fae4ab5b6849784ac045.
Executable SymPy/Fraction reference scripts/check_369_j_analytic_weld.py
committed at fc5bef5d38234827da62fed3ed3709298c24d410. Local execution
PASS: 4352 reciprocal points, 64 shells (128 weight-specific bounds),
128 Lambert coefficients, symbolic coercivity and telescoping inequalities,
Legendre ramification identity, exponential bound and normalization factors.
Single local run 0.1151 s, excluding interpreter startup.
No new Agda kernel acceptance.

### Lattice tail and same-function Fourier expansion

Reuse JInvariantBishopLatticeReciprocalShellMajorantExact
(blob b37264957cefa18cccc223ac212c9b5ab9ac02c1), whose actual
reciprocalNormSquareShellUpper already establishes |m tau+n|^-2
<= C/r^2, C=(1+x^2+y^2)/y^2, y>0.
For k=4,6, power k/2 gives |m tau+n|^-k <= C^(k/2)/r^k.
There are exactly 8r points in square shell r>=1. Thus the sum
of absolute values on that shell is bounded by 8 C^(k/2)/r^(k-1).
For r>=2 and p=k-2, (r-1)^-p-r^-p >= p/r^(p+1)
(positive polynomial cross multiplication checked in SymPy).
Summing telescopically gives tail <= 8 C^(k/2)/((k-2)R^(k-2)).
This proves ordinary absolute convergence and unrestricted bijective
reindexing; transport to original Bishop finite folds and Sequence remains open.

The actual punctured lattice G_k=sum' (m tau+n)^-k has classical
Fourier identity G_k=2 zeta(k) + 2(-2 pi i)^k/(k-1)! sum_{j>=1} sigma_(k-1)(j) q^j.
Derivation: the classical cotangent partial fraction expansion, differentiated
k-1 times, gives sum_{n in Z}(z+n)^-k =
(-2 pi i)^k/(k-1)! sum_{d>=1} d^(k-1) exp(2 pi i d z) for Im z>0.
Split m=0, pair m with -m (even k), then collect md=j using absolute
convergence. Lambert absolute convergence follows from
sum_d d^(k-1) |q|^d/(1-|q|^d) <= (1-|q|)^-1 sum_d d^(k-1)|q|^d.
Normalize G_k by 2 zeta(k); with Euler zeta(4)=pi^4/90,
zeta(6)=pi^6/945, SymPy verifies multipliers 240,-504 exactly.
The cotangent partial fraction theorem and Euler even-zeta evaluation
are classical imported mathematical facts here, NOT new kernel proofs.
Important normalization audit: JInvariantBishopLatticeEisensteinSameObjectCompilerExact
(blob 9f0be2e9e018f4dadbf786f3dcf754d16779c4f7) has e4SameObject/e6SameObject
against its model latticeSum. The concrete instance must compare E_k
with G_k/(2 zeta(k)), not the unnormalized inverse-power sum. Weight
covariance passes through the fixed nonzero normalizing scalar.

### Elliptic value math without global Delta nonvanishing

At i, S fixes i and i^6=-1, so G6=0. At omega=(-1+i sqrt(3))/2,
ST fixes omega and (omega+1)^4=omega^2!=1, so G4=0.
By normalized Fourier equality these give E6(i)=0 and E4(omega)=0.
E4(i)>1 by positive q series. At omega, q=-r, r=exp(-pi sqrt(3))
<1/128 because pi sqrt(3)>5 and exp(5)>128 (exact finite lower
bound checked). E6(omega)>=1+504r-504 sum_{n>=2} n^6 r^n >1:
the geometric ratio is bounded by (3/2)^6 r<1/2 and the tail
is <=128 r^2<r. Thus Delta is nonzero locally and the classical
normalized quotient gives j(i)=1728, j(omega)=0. No global eta
nonvanishing is required for these two points. Original Bishop
phase, normalization and quotient transports remain open.

### Binary / ternary algebra

Q=a^2-ab+b^2, V=ab(b-a), W=(a+b)(2a-b)(a-2b).
Universal polynomial identity 4Q^3-27V^2=W^2 checked exactly.
Hence j_lambda=2^8 Q^3/V^2 and j_lambda-1728=2^6 W^2/V^2,
1728=2^6*3^3. This is the classical cubic/quadratic ramification
identity. It does not identify the fine-frequency 3^9 with 2^8.
Original JFineCoarseRelativeScaleExact owns 3^9 relative scale,
3^2*3^9=3^11, and reciprocal spatial/frequency product.
10*3^9+54=196884 is exact arithmetic; not a derivation of
analytic j from representation dimensions.

### Updated acceptance cut
- Reciprocal bound: original source exists. Shell fold and convergence:
  ordinary proof + exact executable checks; native transport OPEN.
- Fourier normalization: classical proof with explicit named inputs,
  exact coefficients checked; native cotangent/Euler/phase transport OPEN.
- Elliptic special values: ordinary proof complete with those inputs;
  original proof-relevant Bishop readout OPEN.
- Lambda ramification: universal polynomial identity exact; analytic
  lambda(tau) identification OPEN.
- CM integrality, Chudnovsky same-original-pi, K05 transport OPEN.
- No duplicate analytic carrier or replacement of golden Agda by a test.
Classical sources: Eisenstein series, cotangent partial fractions,
Euler even zeta values, Legendre elliptic invariant. Original DASHI
owners above retained; no attribution of classical identities to DASHI.


## 20 November — existing five-orbit half-chart / Eisenstein coefficient weld

Prior head edb76666ce8614e7e46682bb7d0ccbdc68b2ae55.
Executable scripts/check_369_five_orbit_coefficient.py committed at
1b501306c2d52cb10ce5745444f39089fa341fa4; locally executed exact source
PASS, 0.224091847 seconds excluding interpreter startup. 13 Delta
coefficients agree with q product (1-q^n)^24; independent quotient
recurrence gives j Laurent prefix 1,744,196884,21493760,864299970.
First four already owned by MoonshineModularFormCoefficientExact and
JInvariantOEISExactPrefixSameObjectSnowballExact; q^3 already recorded
in YMT7RademacherActivityIdentificationReceipt and
scripts/monster369_oeis_acquisition_snapshot.py. Do not claim novelty
for these coefficients. This script incorporates the previous uncommitted
coefficient regression and checks the fifth prefix value explicitly.

Reuse actual Monster196884FibreInterferenceExact: fineChartCount is
HalfChartNineRingQuotientExact.unfoldedCount=10; finePhaseFieldCount is
EisensteinNineRingInterferenceExact.nineAddressFieldCount=19683;
coarsePhaseSymmetryCount=6, coarseAddressCount=9. Its factorizedIdentity
already gives (5*2)*3^9+(3*2)*9=196884. New independent arithmetic
connection: E4^3/Delta coefficient q^1 = 179280+17280+324
=54*(3320+320+6)=54*(1+5*3^6). Thus modular coefficient arithmetic
agrees with existing typed count from independent inputs. With the known
3B trace 54, the C3 balanced character regular multiplicity is
(196884-54)/3=65610=2*5*3^8; after removing conformal line trace is 53.
Reuse Monster3BC3RepresentationRingEvaluationExact. Trace 54 is an
independent input from existing 3B owner, not derived from identity coefficient.

Actual NineSheet quotient by central inversion in
Monster369SignedPairNineOrbitExact has one singleton and four pairs;
SymPy verifies permutation P, complementary projectors (I+P)/2 and
(I-P)/2, ranks 5 and 4, idempotence, mutual orthogonality and commutation
with D4 quarter turn and axis reflection. HalfChartNineRingQuotientExact
owns separate Half5 x Orientation2=10 and gluing of the two base endpoints
to Quotient9. Base369P2FiveOrbitOrientationGroupoidsExact separately
owns OrientationPolarity x NineOrbit with gauge/retained semantics.
Equal count alone does not identify Half5, NineOrbit and D4 irrep kinds.
The 10 oriented points must not be confused with 9 distinct glued states.
A chosen set-level correspondence between the two pointed five charts is
available; no actual Monster/VOA equivariant identification claimed.
The factor 5 is the rank of the even inversion projector on the nine-sheet;
this is independent of the D4 irrep count.
Attribution: Conway–Norton (1979), classical Eisenstein/eta and finite
group projectors; original DASHI half-chart, NineOrbit and 3B owners above.
AbelE8RootE4FirstCoefficientExact already welds first original Bishop E4
coefficient to generated E8 root count, and AbelE8RootTriadic243CountComparisonExact
owns 240=3*(3^4-1); retain their scope (not all-degree theta identity).

Current cut: finite coefficient and five-orbit linear checks PASS;
full analytic Bishop transport, genuine representation recognition,
CM integrality and CH2 remain OPEN. Agda kernel acceptance not attempted
in this SymPy packet. No new analytic theorem or physical gate promotion.


## 20 November — cross-PR correction: canonical Bishop analytic Route B

Actual recent PR heads inspected: Agda #1478 fb374e50e59a98e2b8a1eee215c77428c5728b68
(merged), #1022 68dfcbf05842aed9696f1640cedd6b36302f5cc8 (merged),
#1444 ed2f8e1b34b3588455d0042004e8b52db17a5777 (open),
#1497 f213b5bfb893e49ae9b29b2915257884b3b0e14e (merged).
Lean #13 3c3b00aa5177fd14fcb46c1bf976c00308212b4b and #104
dbda83aec4b6aa07746d5c692d2d99440872bda1 are merged. Source readback
rather than title-based promotion:

* Lean #13 Integration/BishopRound11MachinCanonicalBinding.lean
  (blob c23e4e42e524a5ada6a967b6daccd01646dafeeb) constructs
  canonicalBinding from encode/eval and Mathlib series convergence;
  exp/sin/cos and both atan limits are uniquely determined up to
  Bishop equivalence. This is an inhabited Lean mirror, not an
  arbitrary assumed convergence record.
* Integration/MoonshineEisensteinAgdaTarget.lean (blob
  9f0310c1e750a1a0b0662c69861293de16b18256) proves the literal
  shifted source recurrences converge to actual normalized Mathlib E4/E6,
  using E4_qExpansion/E6_qExpansion and Bernoulli 4=-1/30, 6=1/42.
  Do NOT rebuild cotangent or Euler-even-zeta identities for this route.
* Integration/MoonshineEisensteinRound11CanonicalRouteB.lean (blob
  acdb8817773460a959ef5baa93d3c89aa7e612b1) fixes concrete arithmetic
  and canonical binding. Its mapped_sourceE4_tendsto_mathlib_E4,
  mapped_sourceE6_tendsto_mathlib_E6, mapped_sourceNormalizedDelta_tendsto
  require only the source point mapping hTau, not a free source binding.
* Integration/BishopRound11MachinReplayIrrelevance.lean (blob
  c006b3e7326298f32f7c9440b3da4cfadd10ed6f) proves mapped q, E4, E6
  and normalized Delta independent of admissible binding choice.
* Integration/MoonshineDeltaFinalMinCut.lean (blob
  ffec688273e1dca65fa837a5a5d0d904ff5d9a5d0)
  contains canonicalEta24NormalizedDeltaSameObject and
  normalizedDelta_ne_zero_canonical, sixfold phase and arg-congruence
  theorems. Global nonvanishing is already a declared classical donor.
* Lean #104 Integration/BishopRound11OriginalArctanCayleyExact.lean
  (blob 1280e6f8e0053eceade3a07525a2cbf83faaf501) gives
  realArctanExponentialCayley and both original Bishop atan evaluations
  under a source binding; #13 canonical binding supplies that shape.
  Native Agda K05 remains distinct.

### Short mathematical endpoint (no second analytic j)
Let A_N be the mapped canonical source E4 partial and D_N the mapped
source normalized Delta partial. These converge to A=E4(tau) and
D=eta(tau)^24 !=0 by the existing source declarations. Eventually
|D_N-D|<|D|/2, hence |D_N|>|D|/2. Then
|A_N^3/D_N-A^3/D| <=
2 |A_N-A| (|A_N|^2+|A_N||A|+|A|^2)/|D|
+2 |A|^3 |D_N-D|/|D|^2 ->0.
This is an ordinary analytic consequence of the already declared
donors, not a new Lean or Agda proof object. The existing normalized
369 renderer is the correct downstream j consumer. Reuse eta24 global
nonvanishing instead of paying a new lattice-sum or local apartness proof
where the Lean semantic route suffices.

### Revised acceptance seam
Lean canonical mirror source and classical normalization donor FOUND;
exact-head Lean kernel receipt and generated Agda replay explicitly
false in the canonical Route B boundary. PR #13 description reports
prior local proof; no fresh receipt acquired here. Lean #104 likewise
states kernel receipt absent. A merged PR does not imply native Agda
acceptance. Native Agda transport remains OPEN; do not mark it closed
by importing the Lean receipt as an Agda proof object.
Next: concrete proof-relevant quotient transport on actual native Bishop
carrier, reuse the canonical semantic route for the classical j target,
then CM integrality/class degree and Chudnovsky identity. No new
finite coefficient evaluator required. Attribution: Mathlib owns
analytic modular series and transcendental facts; DASHI owns the
source mirror and transport, JMD owns the Delta/phase acquisition
as recorded in Agda #1022. No kernel execution in this audit.


## 20 November — existing Klein quotient owners, exact algebra regression
Reopened actual master source blobs:
- JInvariantEisensteinSameCarrierLimitKleinJExact bd864f0b3b40aa5fd0eb727acfcc77596ff845b0: e4Limit/e6Limit, limitNormalizedDelta, CertifiedEisensteinLimitPoint, eisensteinLimitKleinData and eisensteinLimitKlein. Explicit Cauchy and both nonzero witnesses remain inputs.
- JInvariantEisensteinSameCarrierLimitCompilerExact f30edb9ae3fff60aade03054c91b62ae7ab1bcd6: original finite recurrence on ConcreteComplex.ComplexPair, not vendored Bishop carrier.
- JInvariantConstructedComplexKleinJBackendExact f6de94ce3055a5572e9903a835e188a89aabbd69: quotientC F n d nz = n * inverseC F d nz.
- JInvariantProofRelevantKleinJExact 93af6fd7440a0bb47f506ffa3d73794fd3b87f74: TotalQuotientExtension explicitly requires agreement on every nonzero witness; legacyKleinJAgreesOnConstructedPoint already exists.
- JInvariantAnalyticNormalizedKleinAdapterExact 2fb21df27a4b26c8d9ede85dbbe444b968011d36: standardJInvariant, standardJReflects, standardJConjugationFixed, standardAnalyticKleinJIsStandardJ. No duplicate quotient or renderer needed.

scripts/check_klein_quotient_weld.py committed at e9d105f5dd5042d22c14b1356c83356e319801ae. Executed locally: 4 universal symbolic identities and 240 exact nonsingular homogeneous integer quotient cases PASS, 0.053072872 s (single run). Integral Legendre normalization (16Q)^3/(16V^2)=256Q^3/V^2; weight-12 scale cancellation; exact quotient perturbation identity; inverse witness uniqueness algebra u-v=u(1-dv)-v(1-du). Identities are on commutative fields with stated nonzero denominators, not an Agda proof of field authority or carrier equivalence. Existing Klein construction is not a missing abstraction. Remaining concrete cut: instantiate the native Bishop proof-relevant quotient using its own inverse laws and actual series limits, transport apartness from quantitative native certificates or verified classical semantic reflection, connect to existing normalized renderer. ConstructedComplex and vendor Bishop are not definitionally the same. Lean Route B classical target and native Agda replay stay distinct. CM integrality/class degree and CH2 still OPEN. No compiler receipt acquired.


## 20 November — native Bishop Klein consumer and CM163 relative apartness
Prior head ac5b235afca0. Actual source donors at ref:
BishopComplexNonzeroFromComponentExact ef7859e39d264f69924fbf2aef021ae1bd9b5492,
JInvariantBishopUnitDiskEisensteinCompletionExact ad240520b86b33cdfa9a2ca90facfac1a8bc8ddb,
JInvariantEisensteinBishopSetoidSeriesExact 2c0ef9515e4c1dfd278feaf6f71bc607e2a8350c.
Native reciprocal and multiplyReciprocal already exist in
BishopComplexReciprocalExact. Existing CM dyadic script blob
8581a684cfb6ba6bfbfa45adbf6bfe01e9617258 already checks disc.hi<0 and
half-integer enclosure; do not claim that result as new.

New source JInvariantBishopNativeProofRelevantKleinExact.agda
commit f796c6eb3505fa3aa0afe290c6e70353d6cca2ef directly composes
completeBishopUnitDiskEisenstein, scale by embedded 1/1728, original
reciprocalC, and ProofRelevantKleinJAlgebra. Disk data fixed in module
parameters so Point remains Set (a witness of nonzero Delta). No
constructed-complex carrier conversion. negativeDeltaWitness uses
complexNonzeroFromRealApart (inj1 negative); jFromNegativeDelta consumes
literal real component negativity. Source-written, uncompiled.

New scripts/check_cm163_delta_apartness.py commit
3f23203b7a91195ad352202e2e6dc8acff240e60 locally executed identical
source PASS 0.02353068 s. For q=-r, 0<r<2^-36 follows from pi>3,
sqrt163>12, exp(1)>2. For n>=2 sigma_k(n)<=n^(k+1), successive
majorant ratio <=(3/2)^(k+1)r<1/2. Thus u=E4-1, v=E6-1 satisfy
|u+240r|<=7680r^2, |v-504r|<=64512r^2, |u|<=241r, |v|<=505r.
Expand 1728 Delta=3u-2v+3u^2+u^3-v^2. Relative remainder
|Delta+r|/r <= K*r/1728 with K=3*7680+2*64512+3*241^2+
241^3/2^36+505^2<600000. Exact rational checks prove bound <1/2;
uniform upper value approximately 4.896e-9. Real Delta<-r/2.
This is an ordinary mathematical uniform apartness proof conditional on
original q=-exp(-pi sqrt163) and the actual series semantics. No eta
identity or high-precision subtraction needed. SymPy verifies polynomial
expansion and rational side conditions, not native order transport.
Next native gates: instantiate original q point/radius, prove real phase
and tail inequalities on original Bishop limits, apply negativeDeltaWitness.
CM class-number-one enumeration and half-integer window already exist;
CM integrality/class polynomial theorem and CH2 remain open.
No new kernel receipt, no CI. Classical series/CM attribution retained.


## 20 November — CM163 modular-diagonal root isolation (class-number-free route)

Prior head 74c4f7a36776b61f4d086e5f0df943499ec7c052.
New executable scripts/check_cm163_modular_diagonal.py commit
93407324d2a6584ee5dee99ad40e79227865cdd6. Independently constructs
the classical degree-41 modular correspondence diagonal from exact
Eisenstein/eta coefficients. No stored Hilbert class polynomial,
CM integrality theorem, or class-degree theorem used.

Mathematical proof (classical modularity and q-expansion inputs):
tau=(-1+i sqrt(163))/2 satisfies tau^2+tau+41=0. Multiplication by
tau on lattice basis (1,tau) has matrix [[0,-41],[1,-1]], determinant
41, cyclic cokernel (prime index). Thus tau gives a degree-41 cyclic
self-isogeny. Equivalently -1/tau=(tau+1)/41, so modular invariance
gives j(tau)=j((tau+1)/41), a literal factor of the correspondence.

For p=41, define
F_p(tau)=(j(tau)-j(p tau)) product_{k=0}^{p-1}
(j(tau)-j((tau+k)/p)).
The cyclic index-p sublattices are permuted by SL2(Z), so F_p is
invariant. It is holomorphic in the upper half-plane (global Delta
nonvanishing), with only a cusp pole of order 2p and leading -1.
The polynomial representation follows WITHOUT invoking CM or an
integral modular polynomial theorem: subtract multiples of powers
of j to cancel all Laurent terms through the constant, leaving an
invariant holomorphic function vanishing at the cusp. Compactness of
X(1) makes it identically zero. Therefore F_p=P_p(j), deg P_p=2p.
The integer expansion and triangular coefficient extraction prove
P_p in Z[X], leading -1. In particular self-isogeny implies monic
integer equation, but root isolation below is stronger than integrality.

Exact implementation:
Let J(q)=q*j(q)=E4(q)^3 / product_{m>=1}(1-q^m)^24,
t^p=q, H(t)=J(t^p)-t^(p-1)*J(t).
N(q)=product_{k=0}^{p-1}H(zeta_p^k t).
L=t H'/H, L_n=n H_n-sum_{i=1}^{n-1} H_i L_(n-i).
Root-of-unity filtering gives q N'/N=sum_{k>=1} L_(pk) q^k,
so N_0=1, n N_n=sum_{k=1}^n L_(pk) N_(n-k).
The normalized diagonal satisfies q^(2p) F_p=
(q^(p-1)J(q)-J(q^p))*N(q). Compute through q^82 inclusive,
requiring J through t^3322. Inverse eta product coefficients
are obtained by exact division in recurrence n B_n=24 sum_{i=1}^n
sigma1(i) B_(n-i). All arithmetic integer; polynomial calculations
and division in SymPy ZZ. Triangular leading-power subtraction
recovers full degree-82 diagonal. No floating-point acceptance.

Executed local source: degree 82, K=-640320^3=-262537412640768000
is exact root of multiplicity 2, exact division by (X-K)^2 leaves
degree 80 polynomial S. For coefficients a_i of S(K+z), exact
integer check 2^80 |a_0| > sum_{i=1}^80 2^(80-i)|a_i| proves
S nonzero for |z|<=1/2 (even complex disk). Dominance floor ratio
6593105375567751. Local wall time 8.670737622 s (excluding startup).
Existing CM dyadic half-integer window is consumed as mathematical
premise; no fresh rerun of that donor in this packet. Together with
self-isogeny relation, the enclosure identifies j(tau)=K exactly,
without class number or integrality hypotheses. This is a classical
mathematical proof conditional only on analytic modularity/q series,
compactness of X(1), and the existing enclosure's source semantics.
Attribution: classical modular correspondences/Hecke double cosets,
modular curve compactness, Eisenstein/eta product; DASHI's existing
normalized j and coefficient/interval owners. No claim of new
classical CM theorem. HeckeCorrOnX021Receipt and
TraceOfSingularModuliBridge found in search, but no concrete
Phi41 evaluator located; use the direct prime correspondence rather
than another abstract CM interface.

Revised cut: selected CM163 classical integrality and exact value
discharged by modular diagonal route; general CM integrality/class
degree remain separate, no longer on selected Chudnovsky path. Native
Bishop same-object/phase/strict apartness transport and formal
modular-correspondence identity/root isolation remain OPEN; no
Agda/Lean kernel receipt. CH2 (same-original-pi Chudnovsky hypergeometric
identity, including derivative/period constants) is the next major
mathematical cut. Do not infer CH2 from the singular modulus alone.


## 20 November — CH2 Ramanujan differential weld

New executable scripts/check_chudnovsky_differential_weld.py commit
58d337b41316a1a8051e8cef3127cc410816279b; identical local source
executed PASS, 0.252766808 s excluding startup. Uses exact SymPy rational
function cancellation and 24 factorial recurrence checks. Existing
HypergeometricBSplitIntegerMergeExact and generic evaluator retained.
Search of indexed Agda/Lean default branches for PicardFuchs,
RamanujanDifferential, EisensteinDerivative, Quasimodular found no
concrete Ramanujan system donor; not an exhaustive branch audit.

Classical analytic input (not derived by script): Ramanujan differential
identities for D=q d/dq, DE2=(E2^2-E4)/12, DE4=(E2 E4-E6)/3,
DE6=(E2 E6-E4^2)/2. Let z=1728/j=1-E6^2/E4^3, F=sqrt(E4)
with cusp branch F(0)=1. Exact algebra verifies Dz=z E6/E4,
theta=z d/dz=(E4/E6)D, and theta(F f)/F=(E4/E6)D(f)+
(E2 E4/E6-1)f/6. Three applications verify
theta^3 F=z(theta+1/6)(theta+1/2)(theta+5/6)F.
Analytic uniqueness at the regular power-series branch gives
F=sum (6n)!/((3n)!(n!)^3)*(z/1728)^n.
Universal factorial ratio follows by cancellation; 24 finite checks.
At selected CM point the cusp branch must be continued along the
negative real q segment, with E4,E6 positive and z locally invertible;
existing tiny-q majorants supply positivity, native transport open.

Define s2=(E4/E6)(E2-3/(pi Im tau)).
theta F+(1-s2)F/6=F E4/E6/(2 pi Im tau)
=1/(2 pi Im tau sqrt(1-z)) on positive real branch.
For tau163, z=-1728/C^3, C=640320, 2 Im tau=sqrt163.
Set A=13591409, B=545140134. Exact checks:
(1-77265280/90856689)/6=A/B,
144 B^2=163(C^3+1728), B>0.
Hence if s2(tau163)=77265280/90856689 then
sum (6n)!/( (3n)!(n!)^3 )*(A+B n)*(-1/C^3)^n
=C^(3/2)/(12 pi), giving Chudnovsky.
This isolates actual outstanding arithmetic to exact s2 CM value;
the value is a target, not derived here. Prior degree-41 diagonal
P41 gives j value but does NOT determine off-diagonal derivative jets.
Next: construct partial derivatives of Phi41 at (K,K) or use Masser
Phi163 derivative formula; account for double root on diagonal.
No numerical rational recognition as proof. Ramanujan analytic donor
and native Bishop transport remain open; no kernel execution.
Attribution: Ramanujan differential identities, classical hypergeometric
modular equation, Chudnovsky brothers; Masser CM derivative method
(see https://mathoverflow.net/questions/300640/how-to-compute-coefficients-in-chudnovskys-formula
and https://mathoverflow.net/questions/300385/why-does-this-quasi-modular-function-have-integral-values/300776).


## 20 November — CH2 exact s2 from degree-41 diagonal and one slice

New executable scripts/check_cm163_derivative_slice.py, commit
7a97686931c0265220c51245947dba8271af3714. Local identical source run:
diagonal 8.878331697 s, cumulative slice 31.866559174 s, total
31.910040951 s. Reuses j_unit, convolution and diagonal from
check_cm163_modular_diagonal.py. No stored bivariate polynomial or
numerical recognition. K=-640320^3 is the preceding certified CM value.

Let P(X)=Phi_41(X,X), S(X)=Phi_41(X,K), with the standard monic
symmetric modular polynomial. Compute S via the same cyclic norm
recurrence with H(t)=J(t)-K*t, J=q*j, and t^41=q. For odd p=41,
q^(p+1) S(j(q))=(J(q^p)-K*q^p)*Norm(H(t)).
The invariant function has pole order p+1, so principal-part plus
constant subtraction in powers of j recovers all 43 coefficients.
Compute norm through q^42, J through t^1722. P has 83 coefficients.
This uses 126 total polynomial slots vs 1849 dense bivariate slots;
not a measured comparison to full bivariate construction.

Taylor expansion Phi(K+x,K+y) has vanishing constant and linear
coefficients (checked in both slices). Symmetry yields c20=c02=S_2,
c30=c03=S_3, c11=P_2-2*S_2, c21=c12=P_3/2-S_3, where subscripts
denote coefficients after shifting by K. c20 !=0 verified.

At tau=(-1+i sqrt163)/2 the branch h(tau)=-41/(tau+1) fixes tau;
j(h(t))=j((t+1)/41) by S-invariance and hence Phi(j(t),j(h(t)))=0.
j'(tau) !=0 by Ramanujan Dj=-j E6/E4 and existing CM positivity.
In local coordinates x=j(t)-K, y=j(h(t))-K, write
y=alpha*x+beta*x^2+O(x^3). alpha=h'(tau)=41/(tau+1)^2,
41 alpha^2+81 alpha+41=0. Quadratic relation
c20*(1+alpha^2)+c11*alpha=0 checked over QQ[alpha].
Cubic relation
(c11+2*c20*alpha)*beta+c30*(1+alpha^3)+c21*(alpha+alpha^2)=0
determines beta. Compute kappa=2*beta/(alpha^2-alpha) by exact
polynomial inversion modulo 41 X^2+81 X+41; denominator invertible.
Remainder has degree zero:
kappa=-77859659565707/19943834790540897829879824384000.

Chain rule gives
kappa=j''/j'^2+h''/((alpha^2-alpha)*j')
=j''/j'^2+2/((2*tau+1)*j').
With D=(2 pi i)^-1 d/dtau and Dj=-j E6/E4, Ramanujan gives
D log(Dj)=E2/6-2 E6/(3 E4)-E4^2/(2 E6).
Substituting 2*tau+1=i sqrt163=2i Im(tau) gives
kappa=-(s2/6-2/3-1/(2*(1-z)))/K,
z=1728/K, s2=(E4/E6)*(E2-3/(pi Im tau)).
Thus s2=4+3*K/(K-1728)-6*K*kappa.
Exact computed result 77265280/90856689, not supplied to the
polynomial reconstruction. Final assertion verifies target and
(1-s2)/6=13591409/545140134.

Together with previous Ramanujan hypergeometric equation and
144 B^2=163(C^3+1728), this completes the ordinary mathematical
Chudnovsky derivation conditional on classical modularity, symmetric
prime modular correspondence, compactness of X(1), normalized
Eisenstein Fourier and eta identities, Ramanujan system, and exact
CM enclosure/source semantics. For continuation from cusp along
negative real q, earlier tiny-q bounds give E4>0 and E6>0 and
z is locally invertible, with |z|<1 along the segment; analytic
uniqueness gives the same normalized hypergeometric branch.
No Masser formula or general CM class-degree theorem needed.
Native Bishop/Agda theorem and kernel replay remain open; no
compiler run here. CH2 classical mathematical arithmetic gate
discharged, not native same-original-pi acceptance. Next concrete
cut: audited original Machin pi/exp/phase semantics, Ramanujan
series differentiation transport, original Bishop hypergeometric
limit and exact modular correspondence certificate transport.
Classical attribution: Hecke modular correspondence, Ramanujan
differential system, Chudnovsky brothers; this computation uses
the existing DASHI cyclic norm diagonal and a fixed univariate slice.


## 20 November — SymPy execution of original Machin/Chudnovsky semantic seam

Prior head 720199ed0c547ebe69d9a8b0df6bbde16fb4a52f.
New scripts/check_chudnovsky_bishop_semantics.py commit
45432b70f245f5a12c8cf75505254ee58091cc3d. Identical local source
executed with existing check_chudnovsky_exact.py. Exact Gaussian
phase identity, 771 Ramanujan prefix residual coefficients (three
equations, degrees 0..256), four exact interval comparisons PASS.
No compiler run; SymPy in lieu of Agda for executable algebra.

All-degree analytic argument for Ramanujan: use existing normalized
E4/E6 modular forms and Delta=eta^24 nonzero. For D=q d/dq,
D log Delta=1-24 sum sigma1(n) q^n=E2 by normally convergent
logarithmic differentiation of the product (on compact subdisks
|q|<=rho<1 the derivative sum is bounded by
sum n rho^n/(1-rho)). The weight-12 transformation of Delta
gives the weight-2 quasimodular law for E2 upon differentiation.
For a weight-k form f, Df-k E2 f/12 transforms in weight k+2
and is holomorphic including at the cusp. For E4 and E6 the
normalized constant terms therefore give
DE4-E2 E4/3=-E6/3 and DE6-E2 E6/2=-E4^2/2, using the classical
one-dimensional spaces M6 and M8. Differentiating the E2
transformation gives DE2-E2^2/12 a weight-4 modular form,
whose constant term is -1/12, hence -E4/12. These space dimensions
follow e.g. from the classical valence formula (nonzero cusp
forms have weight >=12). This is an ordinary analytic derivation
with explicit classical modularity/valence inputs, not a theorem
proved by finite prefix checking. The native Bishop transport
remains open. Existing normalized Delta and eta owners preferred.

Machin phase exact identity (5+i)^4(239-i)=i(5-i)^4(239+i).
For theta=4 atan(1/5)-atan(1/239), this gives exp(2i theta)=i.
Bounds atan(x)<=x and atan(x)>=x-x^3/3 at chosen positive x
give 0<theta<4/5<pi/2, identifying theta=pi/4 with the classical
phase convention. Existing Bishop Machin quarter-angle and first-zero
owners supply intended native transport. No numerical pi oracle.

All-precision mathematical Cauchy comparison: alternating arctan
brackets converge with width 1/((2n+1)q^(2n+1)). The Chudnovsky
weighted terms have absolute ratio <=42*1728/C<1 (C=640320^3),
strictly positive limiting sum from first alternating bracket.
Dyadic sqrt10005 brackets have width 2^-bits, and positive
denominator reciprocal interval widths tend to zero. Thus both
adaptive precision loops terminate for every positive integer d.
Using the classical Chudnovsky derivation in the preceding packet
and Machin phase identity, both enclose the same classical pi,
so they intersect for every d; union diameter <=2*10^-d. This
is not an inference from four finite runs; equality uses the
stated analytic theorem inputs, and native Bishop setoid identity
is not established by the Python checker.

Measured single-run (ms, excluding interpreter startup):
d=100: Machin 100 terms 0.225, CH 9 terms 0.105;
d=1000: Machin 1000 terms 2.327, CH 73 terms 1.076;
d=3000: Machin 3000 terms 14.741, CH 216 terms 5.232;
d=10000: Machin 10000 terms 125.069, CH 716 terms 46.374.
Matched width <=10^-d, exact intersection and union bound.
Machin cutoff conservative (not optimized); measured ratio not
an asymptotic or universal speedup. No new Kolmogorov claim.
Both use binary split; exact integer arithmetic, Fraction endpoints.
Next: source-native equality/phase/limit transport and formal
certificate replay remain OPEN, but no additional classical CM
constant is required. Classical attribution: Machin, Ramanujan,
Chudnovsky, modular-form valence formula and original repo owners.


## 20 November — Paper 9 working manuscript and cost-model cross-pollination

User-approved independent Paper 9 candidate (math.NT/math.NA/cs.SC).
Working draft `Docs/papers/drafts/Paper9ExactCMModularJetCertificates.md`
created at 5ea80fe8729f8c421c7f369fc88b4b03582c7700. Publication router
and papers index updated in this packet. Not a fourth Clay-facing core
paper; no dependence on Papers 1–8 or wider 369 physical interpretations.

Cost-model donor readbacks: EfficientRecoverableQuotientExact
050e3c36d14bfe86e77ce6ef7ccb3ccd4565e201,
ShorClassicalQuantumFibreComparisonExact
36b90475a1f76a2c16ed820741706c29949eb703,
QuantumExecutionFibreAdapterExact
e2694328b8455d51ca86a1bbac591b5f3edc03f0,
FibreProgramComplexityExact (actual path/sum/peak/head consumers),
Karp21N21PhysicalF3F4CompileWeld20261114.md
57ea16b449e2860d966f6e4086d388f7588721a2,
Karp21FRACDASHMachineMaxCut20261109.md
94a6c3fda664d3f78a7fa71731fbf400a1c1dc0d.
Reuse cost discipline, not open P-vs-NP/physical bit-machine conclusions.
Classical transition and quantum gate costs are distinct.

Draft contains the two-slice cubic-jet lemma, CM163 derivation, constructive
interval methodology, and parameterized preliminary arithmetic/time and
payload-space bounds. 126 vs 1849 coefficient slots is not a RAM or bit-time
ratio. Current p^4 arithmetic count and p^2 live coefficient-slot bound
must be combined with proved intermediate bit-height, actual bigint
temporary storage, translation/verification, and representation overhead.
Binary-split bounds parameterized by multiplication cost and d; no
unit-cost unbounded integers. Numeric p versus log(p) explicit.

Next publication gates: independently rerun historical committed scripts and
receipts; instrument bitwidth, operation counts, peak payload/RSS,
serialized certificate and verification cost; generalize additional CM
discriminants; baseline and bibliographic novelty comparison. Local SymPy
in lieu of Agda for computational packet. No fresh execution or kernel
receipt in manuscript-authoring turn. Keep draft updated with actual
results as they land.


## 20 November — independent replay and preliminary uniform bit-height lemma

Local Python 3.13.5, SymPy 1.14.0. Exact Git blob readback at
7d5be142d881f810740b5f8de4cf858e7cffc905 matches five mounted scripts.
The local check_chudnovsky_exact.py initially lacked the committed
positive precision assertion; restored it and verified blob
eb58d9dd1d0a2e0d62e9ef16a0ad1ee9703e0e6b before rerunning.
Exact-source results: CM163 delta apartness PASS (0.02539 s),
hypergeometric differential weld and 24 ratios PASS (0.19618 s),
degree-82 diagonal root isolation PASS (9.0771 s internal,
10.41 s process elapsed, max RSS 130884 KiB via GNU time).
Root K multiplicity 2, dominance floor 6593105375567751.
Gaussian phase, 771 Ramanujan coefficients, 4 matched intervals
PASS after dependency correction. Single-run Machin/CH milliseconds:
100: 0.229/0.174; 1000: 2.255/1.068; 3000: 16.281/5.027;
10000: 119.085/48.259. CH standalone seven-run medians in ms:
0.051575, 0.744255, 5.472865, 33.064358.
Full derivative slice replay timed out (120 s limit) after diagonal
stage printed 9.2683 s; prior 31.910 s receipt NOT independently
reproduced. Dyadic enclosure not rerun in this packet. No CI/kernel.

### Uniform bit-height bound for the integer construction (proof candidate)

Let b=max(1,bitlength(|K|)), M<=2p^2. J=q*j has nonnegative integer
coefficients. On q=1/2, E4<=1+240 sum n^4/2^n=36001<2^16.
The inverse eta product has logarithm <=24 sum 2^-n/(1-2^-n)
<=48; exp(48)<2^96. Hence J(1/2)<2^144, and J_m<=2^(144+m).
All positive inverse-eta recurrence partial sums are bounded by
their final numerator; nonnegative convolutions likewise. For either
H construction, |H_m|<=A^m for m>=1 with A=2^(b+150).
The formal inverse coefficients obey |[t^m]1/H|<=2^(m-1) A^m
for m>=1 by ordered compositions (constant coefficient 1).
Absolute sums of the products in the logarithmic derivative recurrence
are bounded by O(m (2A)^m) using that same inverse majorant.
Consequently all L recurrence terms and partial accumulators have
O(M(b+1)) bits. For N, its p-factor product gives
|N_n|<=A^(pn) binom(pn+p-1,p-1)<= A^(pn) 2^(pn+p).
The recurrence intermediates L_(pi)*N_(n-i), their sums and exact
division numerators retain O(pn(b+1)+p+log(n+1)) bits.
Normalized correspondence products inherit O(p^2(b+1)) bits.

For the triangular extraction, [q^k]J^d <= 2^(144d+k)
binom(k+d-1,d-1) for d>=1, so all power table entries for d,k<=2p
have O(p) bits. At each leading-coefficient elimination the maximum
absolute residual can grow by at most 1+max coefficient of J^d,
i.e. a factor 2^O(p). Across at most 2p+1 eliminations this adds
O(p^2) bits. Thus B_max=O(p^2(b+1)) for the actual integer series
and triangular reconstruction, including scalar accumulators.
This does not yet cover SymPy's general internal shift/exquo/invert
temporaries, allocator overhead or a physical tape simulation.
The existing O(p^4) scalar operation and O(p^2) payload slots
then imply O(p^4(b+1)) live integer payload bits for that stage.
With schoolbook arithmetic, a conservative construction time bound
is O(p^8(b+1)^2), not a bound polynomial in log p.
General proof should be reviewed, and actual operand instrumentation,
full derivative replay, dyadic replay and allocator accounting remain open.


## 20 November — GMP/Newton exact construction and complete CM163 replay

Prior head 3b32bcb374cfd52cc2fe0e824f6b05d04f9f6cce.
Scalar defaults preserved in check_cm163_modular_diagonal.py and
check_cm163_derivative_slice.py, with explicit optional logder_fn hooks
(commits 50d40405b26dbf2620270c7f5b18b8206250f932 and
2f8b5e594e95a4b487d376e701c19fd909445c27).
New check_cm163_fast.py fc51d0f1636bcc2cc7b71f95225304aa2a86ed08
uses native GMP signed Kronecker multiplication via ctypes (Linux GMP
ABI), Newton inversion of H with constant coefficient 1 and exact
checks H*G=1 and H*L=tH' modulo the requested truncation.
For operand coefficient counts m,n and maxima U,V, choose byte-aligned
radix R>2 min(m,n) U V. The signed coefficient of the true product
lies strictly inside (-R/2,R/2). Evaluating at R, multiplying
integers and centered digit extraction with carry recovers each
coefficient inductively. Truncation uses the low bits of the product.
Newton identity 1-HG_new=(1-HG)^2 gives doubling and uniqueness of L
from H*L=tH'. This proves equality to the scalar recurrence for
unit H, not a claim of independent analytic modularity.
The original other construction and derivative consumer are unchanged.
64/64 signed convolution and 64/64 inverse/logder scalar comparisons,
8/8 complete polynomial comparisons at p=3,5,7,11 passed locally.
An initial proof-of-concept run timed out with large Python modulo;
using a bit mask resolved the truncation issue. Final code uses explicit
hooks, no dynamic source substitution. A separate unmodified scalar
replay also completed, 33.01158858 s while concurrently running other
tests; do not use that as a controlled speed benchmark.

Sequential reproduction runner check_cm163_backend_parity.py
9adb75153854c4a8a019c6a05f8e8fb3b6313940 runs independent subprocesses
and checks exact byte equality of both unshifted polynomial arrays
serialized as signed hexadecimal JSON, not just hashes or final s2.
Executed locally with Python 3.13.5, SymPy 1.14.0, GMP 6.3.0,
Linux x86_64 glibc 2.41, Intel Xeon Platinum 8573C.
All exact source blobs matched: diagonal add8e35866aa1e9f379b4a57059c4487e4c7241c,
slice 0c1f7d04618943d6b9941f433ceed8c5cd9fd590,
fast 6c1a051c2832d9afd549680b3a6401383023989e,
runner d737ef34938ee5c1557e08ee322f785c5d2ec7d8.
Both full p=41 runs PASS, s2=77265280/90856689 and
kappa=-77859659565707/19943834790540897829879824384000.
126 output coefficient slots, aggregate signed-magnitude payload
241632 bits (one sign bit per slot), max output coefficient 3371 bits,
61113 serialized bytes; full byte-for-byte coefficient parity PASS.
Measured single sequential run (seconds; imports excluded):

| Backend | Diagonal | Construction total | Complete incl. derivative/serialization | Peak RSS KiB |
| --- | ---: | ---: | ---: | ---: |
| Scalar | 8.899486372 | 31.606400973 | 31.649009698 | 143412 |
| GMP/Newton | 4.252409969 | 16.159672922 | 16.208337047 | 533716 |

Speed ratio 1.95x; RSS ratio 3.72x. 52 packed multiplication calls
on the fast full construction; maximum packed operand 204771028 bits.
This is distinct from maximum individual coefficient width, final
certificate size or live integer payload. Resource receipt:
Artifacts/paper9/cm163_backend_parity_20261120.json (commit 684059f458297ed9dbb7e158d83f895cc4bfec45).
Reproduce: python scripts/check_cm163_fast.py for regressions and
full fast derivative, then python scripts/check_cm163_backend_parity.py
for sequential full exact comparison. No CI/kernel required.
Historical derivative result now independently reproduced. Dyadic
enclosure replay remains open; P9.03 partial for entire suite.
P9.04 partial (packed counts/operand width and output coefficient
heights, not every scalar intermediate); P9.06 measured two backend
RSS and serialized slice size, not a general memory theorem or
full certificate size. No claim of an unconditional speedup, statistical
benchmark, smaller peak memory, or asymptotic improvement for all stages.
Next: block or height-adaptive packing/CRT, charge repacking and all
GMP/Python temporary buffers, preserve exact parity; retain scalar
backend for memory-constrained runs. Generalization and external
baselines remain open. No new formal analytic or kernel closure.


## 20 November — codec-inspired support-window Newton backend

Implemented scripts/check_cm163_window.py at commit
245dd9739108f80b296f304316642355b8026601, exact local Git blob
f5f578445d1ac1bfa4f46a0de62f72cc9320428f verified after connector write.
Reuses original GMP mul and unchanged diagonal/specialized polynomial consumers.
Donor inspiration: TriadicResidualMaskSignCodec, TriadicExplodedTransformCodecFormalism,
BalancedTritBitFibre, DNACarrierFibre, DNAProductionCodec and the actual
run_triadic_flagship_benchmark.py. These are structural analogies, not a claim
of literal ternary entropy coding or DNA execution.

For H(0)=1 and HG=1 mod t^m, define r=-[t^m,...,t^(k-1)]HG,
k=min(2m,N). Then G_new=G+t^m*(G*r mod t^(k-m)); the known
prefix stays unchanged. Partition operands into blocks of 256 coefficients.
Omit all-zero blocks and pairs outside requested output window; choose
forward or reversed truncated multiplication according to the shorter
local output prefix. Reversal is exact since rev_(a+b)(AB)=rev_a(A)rev_b(B).
Accumulate each pair at its exact index offset. Existing GMP mul chooses
a safe local signed radix per pair. If individual coefficient heights
are bounded by B, a packed operand uses O(s(B+log s)) bits for block
size s, rather than O(M(B+log M)) for a uniform full operand; source,
output, copies, allocation and multiplication workspace are separate.
No global peak-memory theorem asserted. The 256 block length is a
selected experimental constant, not an optimized parameter.

Local Python execution: 128 random signed window comparisons against
scalar convolution; 128 logder comparisons against dense fast backend;
8 full small-prime polynomial comparisons against scalar (p=3,5,7,11).
All PASS. Full degree-41 window derivative run PASS with exact H*G=1
and H*L=tH' at full truncation, kappa and s2 unchanged.
Window diagonal 5.738555279 s, cumulative construction 18.666320395 s,
total derivative 18.706544707 s, max RSS 223188 KiB, 579 packed calls,
max operand 22816464 bits. This process included small regressions.
Separate window construction/serialization run 18.577457777 s,
RSS 221560 KiB, saved signed hexadecimal coefficient arrays.
Fresh dense fast runner: diagonal 4.524124461 s, construction
17.555023721 s, total 17.608450256 s, RSS 521212 KiB,
52 calls, max operand 204771028 bits.
Byte comparison of both complete serialized arrays PASS (126 slots).
Fresh scalar comparison attempt exceeded 120 s tool limit (after window
construction); do not claim direct fresh scalar p=41 comparison in this
packet. Transitive scalar parity uses previous recorded dense/scalar
receipt. These single process observations are not a controlled
statistical benchmark. Historical scalar timings retained as historical.

P9.M1-M4 implemented together; no ablation yet. Largest packed operand
8.97x smaller; full-run RSS 57.2% smaller vs fresh dense run, with roughly
6% construction-time overhead. Different process scopes explicitly noted.
Next: geometric predictor as exact factorization or quotient, not merely
subtracting a large leading power; triadic/height-adaptive block sizes,
ablation and repeated sequential memory/runtime measurements, then CRT.
Native ternary coding, FRACDASH execution, dyadic enclosure replay and
additional CM discriminants remain OPEN. No Agda or CI execution.


## 20 November — bounded residue SWAR-inspired execution and deterministic CRT

Source commit ab90beec7eeadb73489bfc5ecad253cd53086b05:
scripts/check_cm163_residue_swar.py, local and committed Git blob
2feac81f52f2b9b941444e2e8b3e260004a0e4f2. Dependencies checked locally:
fast 6c1a051c2832d9afd549680b3a6401383023989e,
diagonal add8e35866aa1e9f379b4a57059c4487e4c7241c,
derivative 0c1f7d04618943d6b9941f433ceed8c5cd9fd590.
Python 3.13.5, SymPy 1.14.0, x86_64. No CI/kernel run.

Reuse provenance: TriadicSupportMaskSWARExecutionExact has a receipt for
eight independent byte lanes and 8^8 exhaustive packed words;
TriadicSignCompactionSWARExecutionExact has eight lane factorized encode
and 27^5 core product receipt; TriadicCodecSWARPortableKernelCrossPollinationExact
separates representation from execution; RSA260TriadicSWARExecutionRoadmapCrossPollinationExact
supplies bounded ABI / scalar oracle / exact source / lane execution /
domain parity pattern. This new backend uses GMP Kronecker coefficient
lanes and serial residue rings, NOT fixed-word hardware SWAR or SIMD.
No claim of reusing the actual C byte-popcount kernel for big-integer multiplication.

Reduce every coefficient mod r after each convolution; use carry-isolated
packing via original fast.mul. For operand sizes m,n and residues <r,
the signed radix bound R>2 min(m,n)(r-1)^2 suffices. For b_r=bitlength(r),
packed operand size O(M(b_r+log M)) rather than O(M B_max).
Use Newton active residual update and check HG=1, HL=tH' in every ring.
Norm division by k is modular inversion, legal because moduli are powers
of distinct small primes >82 (trial division establishes primality).
Reconstruct only the two final polynomial vectors by incremental CRT,
not the high-height intermediate inverse series. J generated once using
original exact j_unit; both slices use prefixes of that same series.

Deterministic height proof (not historical output width):
Let n be slice degree, H finite truncated input in t with t^p=q, g the
normalized prefactor in q, J the unit series truncated to degree n.
Define Q=g*Norm(H), whose first n+1 coefficients agree with the original
construction. Norm is invariant under t -> zeta*t, a polynomial in q,
and on |q|=2^-p its magnitude is <= (sum_i |H_i|2^-i)^p.
For formal coordinate w=q/J, residue change of variable gives the recovered
coefficient c_d=[q^(n-d)] Q J^-d (1-qJ'/J), 0<=d<=n:
take the residue of w^(d-1) P(1/w) dw and substitute w=q/J.
Only first n+1 coefficients enter. Exact dyadic inequalities in code prove
|J-1|<=1/4 and |qJ'|<=1/4 on the circle; hence |J^-d|<=2^d and
|1-qJ'/J|<=2. If H_abs<=2^h and g_abs<=2^a from exact coefficient
sums, Cauchy gives |c_d|<=2^(p*h+a+1+d+p(n-d))<=2^E,
E=p*h+a+1+pn. For both CM163 inputs computed E=5086.
CRT product strictly >2^(E+1) makes centered reconstruction unique;
no reliance on historical coefficient list or probabilistic stopping.
The optional reference argument only compares after reconstruction.
This is a mathematical bound conditional on the existing slice construction;
no fresh proof of classical modularity is asserted. The dyadic checks
are specific to p=41, not a uniform small-prime theorem.

Observed separate live local runs, including original J generation,
all modular inverse/logder checks, CRT, byte serialization, optional
reference equality and exact derivative consumer:
| Target modulus bits | CRT rings | Final product bits | Time s | RSS KiB | Largest packed operand bits | Packed calls |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 768 | 7 | 5396 | 6.693572904 | 143340 | 5245493 | 1246 |
| 384 | 14 | 5413 | 6.625785951 | 137292 | 2689990 | 2492 |
Both PASS all 126 exact coefficients against the existing local
cm_fast_coeffs.json, and kappa=-77859659565707/19943834790540897829879824384000,
s2=77265280/90856689. First output file also independently cmp-equal to
the reference. J/setup times 3.090534929 and 2.898582786 s.
Reproduce without a reference:
python scripts/check_cm163_residue_swar.py --bits 384 --output coeffs.json
Reference optional: --reference existing signed-hex JSON.
Reported historical scalar 31.649 s /143412 KiB and dense 16.208 s /
533716 KiB are separate prior runs, not controlled fresh comparisons.
384 target is ~134.07 MiB RSS, ~76x smaller largest packed operand than
historical dense; runtime ~6.63 s. Only two single observations; no
statistical, general peak-heap or hardware-throughput claim.
P9.M7 deterministic streamed CRT implemented and full CM163 parity PASS.
P9.M5 geometric compression remains open and is no longer prerequisite.
P9.M10 fixed-width SWAR lane reduction / SIMD implementation OPEN:
derive overflow-safe packed modular add/sub/mul, compile scalar oracle,
exhaustively test feasible domains and compare full same-source residues.
Next optimize shared J construction (~3s), width/block ablations,
native fixed-width lanes and generalization; charge all intermediate
storage/CRT reconstruction, retain original scalar and dense oracles.


## 20 November — fast shared J and native fixed-width SWAR primitive gate

New scripts/check_cm163_fast_j.py commit b808d8f511b0cf1e36a9f3ca4eeecd60ca66ef11
blob b3b0e21af92c80c38e26ccba811514f7b6ab1bef.
Use Euler pentagonal theorem P=prod(1-q^m)=1+sum_{k>=1}(-1)^k
(q^(k(3k-1)/2)+q^(k(3k+1)/2)), exponentiate P^24 by repeated squaring,
invert by active-residual Newton, multiply by E4^3. Attribution Euler and
classical eta normalization; no claim of new series identities.
Exact checks P^24*inv=1 and P^24*J=E4^3 modulo q^(n+1).
All 3323 coefficients at n=3322 agree with original scalar j_unit.
One same-process comparison, fast first: 0.202099954 s vs 2.824831598 s;
34 GMP calls, maximum packed operand 3721676 bits. Six smaller prefixes
(0,1,2,10,31,64) also PASS. No statistical claim.

Earlier experimental injection of j_unit into unchanged CRT consumer
completed in 3.442226512 s, RSS 137748 KiB, 126 exact coefficients equal.
Committed explicit --fast-j option in check_cm163_residue_swar.py at
45b4c6bee64889f152c951d33905ec46c2957450, blob cc611e4540eaa07cda9062425ad42382672ecb76.
Exact committed source replay (verified local blob):
python scripts/check_cm163_residue_swar.py --bits 384 --fast-j --reference cm_residue_coeffs.json --output cm_fast_j_coeffs.json
J/setup 0.212358979 s, total 3.541941401 s, RSS 138372 KiB,
14 CRT rings, modulus 5413 bits, certified E=[5086,5086],
2526 packed calls, max operand 3721676 bits. All 126 coefficient
bytes match previous local residue arrays, same kappa and s2.
Reference optional; not used for stopping or reconstruction.
The fast-j option leaves scalar default unchanged. Historical scalar
31.649 s comparison is cross-run only; latest exact committed replay
~8.94x historical speed, RSS ~135.13 MiB.

Native SWAR primitive source scripts/check_cm163_swar_lanes.c commit
95dedf01e3e0eb23560ec978de89f82d55de47d8, blob
dcfd038bee6d26385a6f0cf71b36aa154de38446.
Four 16-bit lanes in uint64_t, 14-bit residue payload, common modulus
2<=p<=16384, inputs canonical. Addition: s=a+b <2p per lane, guard
bit 15 prevents cross-lane borrow in (s|GUARD)-p; guard predicate
selects s or s-p with a replicated full-lane mask. Subtraction uses
a+(p-b), whose maximum <=2p-1 and hence still below guard.
Multiplication uses 14 bounded double-and-add iterations, bit selection
via disjoint full-lane masks. This proves lane isolation under the
stated preconditions; no hardware SIMD or constant-time claim.
Compiled locally gcc -std=c11 -O3 -Wall -Wextra -pedantic.
Executed 6889 exhaustive scalar pair cases p=83 embedded in four
correlated lanes, plus 100000 pseudorandom four-lane words p=16381;
all 4 lanes x 3 operations checked per case. Not exhaustive over all
independent four-lane words. This C primitive is NOT integrated into
the 384-bit CRT backend; no end-to-end native SWAR speed claim.
P9.M10 primitive PASS, full modular-polynomial SWAR backend OPEN.
P9.M11 shared J generation PASS. Dyadic replay and other CM cases
remain open.

External SOTA/novelty boundary: compare Sutherland, On the Evaluation
of Modular Polynomials (2013), https://mathweb.ucsd.edu/~kedlaya/ants10/sutherland/paper.pdf;
Evaluation of Modular Polynomials from Supersingular Elliptic Curves
(2025), https://portal.fis.tum.de/en/publications/evaluation-of-modular-polynomial-from-supersingular-elliptic-curv/;
Hemmecke, Paule, Radu, Computer-assisted construction of Ramanujan-Sato
series for 1/pi (2026), DOI 10.1007/s11139-026-01352-2;
FLINT polynomial algorithms https://flintlib.org/doc/algorithms/polynomials/overview.html.
Existing efficient evaluation, CRT and automated series derivation
preclude novelty claims for those techniques alone. Our proposed scope
is direct certified CM cubic jet with two slices and exact height bound.
SOTA not established: no matched external execution baseline yet;
PARI/Sage/FLINT not installed in this local environment (gp absent,
no libflint in ldconfig). Need cold/warm matched outputs, exact height
guarantees, identical hardware, repeated time and RSS, general levels
and comparison against direct derivative/jet methods as well as full Phi.
No new Agda/CI run.

## 20 November — attribution-first source ledger and odd-prime family replay

Standing PR #1444 attribution policy: preserve original authors, exact primary
source, earlier DASHI producer and revision; distinguish quotation, theorem
intake, conceptual analogy, independent rediscovery, implementation, extension,
execution, formalization, kernel acceptance and external validation. Cite
external researchers, do not imply collaboration or co-authorship unless
actually evidenced. Missing metadata is an explicit residual. Reuse before
construct. No provenance inferred from a similar formula.

Primary bibliographic records checked 20 November 2026:
- Andrew V. Sutherland, On the evaluation of modular polynomials (2013),
  DOI 10.2140/obs.2013.1.531, arXiv:1202.3985. Direct specialization,
  CRT evaluation; established prior art, not implemented here.
- Maria Corte-Real Santos, Jonathan Komada Eriksen, Antonin Leroux,
  Michael Meyer, Lorenz Panny, Evaluation of Modular Polynomials from
  Supersingular Elliptic Curves, arXiv:2506.15429 (2025), proceedings
  DOI 10.1090/conm/840/16823 (2026). Supersingular evaluation and memory
  complexity under their stated model; no comparative run yet.
- Ralf Hemmecke, Peter Paule, Cristian-Silviu Radu, Computer-assisted
  construction of Ramanujan–Sato series for 1/pi, Ramanujan Journal 69,
  article 73 (2026), DOI 10.1007/s11139-026-01352-2. MultiSamba and
  ModFormDE, with lineage to Radu (2015), Hemmecke (2018), Paule and
  Radu (2021); author supplement
  https://www3.risc.jku.at/people/hemmecke/papers/oneoverpi/.
  No FriCAS execution or reuse of their code claimed.
- Reinier Bröker, Andrew V. Sutherland, An explicit height bound for
  the classical modular polynomial (2010), DOI 10.1007/s11139-010-9231-8,
  arXiv:0909.3442. Prior explicit height bounds; compare our slice bound
  with specialization of their bound before claiming improved theory.
- Reinier Bröker, Kristin Lauter, Andrew V. Sutherland, Modular polynomials
  via isogeny volcanoes (2012), DOI 10.1090/S0025-5718-2011-02508-1,
  arXiv:1001.0402. CRT isogeny-graph construction, established prior art.
- David Masser, Elliptic Functions and Transcendence (1975), original
  CM derivative observation; exact original lemma inspection pending
  (identified through cited Bruinier/Ono/Sutherland paper, not independently
  read from Masser's book). Jan Hendrik Bruinier, Ken Ono, Andrew V.
  Sutherland, Class polynomials for nonholomorphic modular functions,
  arXiv:1301.5672, CRT algorithm building on Masser's observation.
  Our chain-rule derivation is an independently constructed route,
  not discovery of the modular derivative/CM relation. Compare both
  normalization conventions and derivative orders explicitly.
- FLINT: David Harvey, William Hart (founders), Sebastian Pancratz,
  Fredrik Johansson and all relevant contributors; official
  https://flintlib.org/authors.html and https://flintlib.org/citation.html.
  External baseline, not executed or linked in current code.
- Classical Machin, Euler pentagonal theorem, Eisenstein, Dedekind eta,
  Klein j, Ramanujan, Serre derivative, Chudnovsky brothers, Newton
  inversion, Kronecker substitution, CRT and Bishop completion retain
  their historical attribution. Exact original edition/page ledger
  remains pending where not verified. Lorenz Milla arXiv:1809.00533
  remains related derivation lead. Do not claim classical results new.

Evidence boundary: bibliographic records and abstracts inspected; detailed
theorem-by-theorem comparison and benchmark replication still OPEN.
No claim that cited authors collaborated, no co-authorship trailers for
citation alone. Existing Aristotle/Harmonic attribution retained on actual
donor artifacts. Original DASHI codec, SWAR and Karp owners preserved.
Our candidate contribution is the specific two-slice cubic-jet execution,
cyclic-norm reconstruction and explicit slice certificate integration,
subject to prior-art review. SOTA remains OPEN.

New source scripts/check_cm_prime_family.py commit
ef295d0d7390475f1c4cd417be28866b04f5ff0b. Executed locally with SymPy
and original scalar/GMP constructors; classical K supplied, not derived.
For odd prime p, tau=(-1+i sqrt(4p-1))/2, h=-p/(tau+1),
alpha satisfies p alpha^2+(2p-1) alpha+p=0. Same cubic formula
and s2 normalization as CM163. Exact P/S parity at p=3,5,11,17,
double-point conditions, quadratic tangent and invertible denominator,
rational kappa verified. Results (one local run, seconds include both
backends):
D=-11 p=3 K=-32768 s2=32/77 0.030947798;
D=-19 p=5 K=-884736 s2=32/57 0.010402145;
D=-43 p=11 K=-884736000 s2=640/903 0.084691348;
D=-67 p=17 K=-147197952000 s2=33440/43617 0.521738573.
No independent analytic CM value or root isolation for these four cases
yet. p=2 (D=-7) excluded by odd-prime sign convention. P9.M13 partial PASS.
Local gp/sage absent, ldconfig no libpari/libflint, FriCAS absent;
no external runtime benchmark. Next generalize CRT radius for small
p and root enclosure, compare Masser formula and run pinned external
baseline in user environment. No Agda/CI execution.


## 20 November — Masser normalization and rational-only cubic jet

Primary text inspected: Bruinier, Ono, Sutherland, Class polynomials for
nonholomorphic modular functions, arXiv:1301.5672v3 (28 Jan 2015),
pp.2,9–10, eqs. (1.2), (2.6)–(2.9), Lemma 2.3. The authors credit
David Masser, Elliptic Functions and Transcendence, LNM 437 (1975),
p.118 and Lemma A2. Masser's original book not directly inspected.
Their gamma = s2/(6K) -(7K-6912)/(6K(K-1728)) equals -kappa by
our earlier normalization. Prior art owns this invariant, not DASHI.

Their formula at level |D| is gamma=(2 beta02-beta11)/beta01,
with beta01!=0 under their hypotheses D<-4, D != -3d^2.
For translated diagonal P and fixed slice S, symmetry gives beta02=S2,
beta11=P2-2S2, beta01=S1, hence gamma=(4S2-P2)/S1.
This two-slice rewriting is an elementary consequence of their formula,
not an independent discovery of Masser's theorem.

At lower prime level p=(1-D)/4, for the nodal cubic jet set
a=S2, b=S3, c=P2-2a, d=P3/2-b. The nonzero tangent alpha
obeys a(1+alpha^2)+c alpha=0. Assume a!=0, simple nonreal tangent
(alpha!= +/-1), and the established chain-rule relation
kappa=2beta/(alpha^2-alpha).
The cubic equation gives
kappa=-2[b(1+alpha^3)+d(alpha+alpha^2)]/
((c+2a alpha)alpha(alpha-1)).
Using c=-a(alpha+alpha^-1), denominator becomes
a(alpha+1)(alpha-1)^2; numerator is
-2(alpha+1)[b(alpha^2-alpha+1)+d alpha].
Since (alpha-1)^2=-(c/a+2)alpha and alpha^2-alpha+1=-(c/a+1)alpha,
cancel to get kappa=2[d-b(c/a+1)]/(c+2a)
=P3/P2-2S3/S2. Thus gamma=2S3/S2-P3/P2.
All divisions licensed by the stated hypotheses. This rational-only
consumer eliminates quadratic field inversion, not the need to establish
the analytic branch/tangent hypotheses. It is a specific alternative
lower-level computational route; novelty relative to other CM derivative
methods remains open. For D=-163 levels 41 vs 163, degrees in each
variable 42 vs 164; no implied measured speedup.

New executable scripts/check_cm_masser_weld.py at 152d7148f72d7f480ac928326bff402479729922,
locally executed exact Git blob e79b21cbe0e485b2b40502d53359afb8fa852d6b.
Run from repository:
python scripts/check_cm163_residue_swar.py --fast-j --bits 384 --output coeffs.json
python scripts/check_cm_masser_weld.py --coeffs coeffs.json
Local replay used existing cm_fast_j_coeffs.json; no fresh CM163
construction in this packet. Independent lower/higher polynomial
construction using original GMP backend:
D=-11 levels 3/11 gamma=289/8830976, 0.043565546 s;
D=-19 levels 5/19 gamma=275/226934784, 0.377458157 s.
Both exact parity PASS. Stored CM163 slice gamma=
77859659565707/19943834790540897829879824384000 and s2
77265280/90856689 PASS. Single execution observations, not comparative
benchmarks. Classical K supplied for smaller cases. No higher-level
163 reconstruction, original Masser book inspection, external benchmark,
or Agda/CI acceptance. Keep original quadratic field consumer as oracle.
Next: cross-level 43/67 and bounded CRT for 163, compare direct jet
competitors rather than only full polynomial reconstruction, integrate
rational consumer after parity on all supported CM cases.


## 20 November — direct consumer-selected translated jets (P9.M14)

Refactor scripts/check_cm163_residue_swar.py at bc4a24b9513ac57479f4b16d2295b247c9bd1197
(blob 16675c15d6617454e9cb3e5f15bb2a2807f4c70a) exposes raw_inputs and
normalized_product; original full-slice constructor remains an oracle.
New scripts/check_cm_direct_jet.py at 5aa4f5310f1db891ae8b4227e7181c61ce7fc606
(blob 6e1b83d5ff38d1cc42095b31f8a24b3ff17cbf62). Local Git hashes match.
Reuse existing cyclic norm, modular inverse and fast J producers; no
new classical modularity assumption. Preserve Masser attribution through
Bruinier–Ono–Sutherland arXiv:1301.5672 Lemma 2.3; classical formal residue
change of variable is not novel. Candidate contribution is the specific
consumer-selected implementation, its bounds and lower-level jet weld.
No actual co-authorship inferred from citations.

Let F be either polynomial slice of degree n, Q=q^n F(j(q)), V=J-Kq,
w=q/V. Formal residue of w^(m-1) F(K+1/w) dw after substitution is
[q^(n-m)] Q V^-m (1-qV'/V). This gives translated coefficient m
directly over residue rings, without reconstructing any full polynomial
or subsequent translation. V has constant coefficient 1. Substitution
identity holds over integers and hence descends to all residue rings.
Compute Z=Q(1-qV'/V), then multiply successively by V^-1 at decreasing
truncations n-m; select one coefficient at each order. Fixed-slice
V inverse is a prefix of the already computed H inverse, reused after
exact input equality check. Diagonal uses a small unit inverse recurrence.
This is conditional on existing integral slice and normalized product
identity and analytic branch hypotheses; not a fresh modularity proof.

Height proof: choose least integer B>=2 satisfying exact absolute sums
|V-1|<=1/4, |qV'|<=1/4 on |q|=B^-p; monotone exponential search/bisection.
On |t|=B^-1 bound H by 2^h using finite absolute coefficient sum,
bound g on q circle by 2^a. Norm invariant under t->zeta*t gives
|Q|<=2^(ph+a); |V^-m|<=2^m and |1-qV'/V|<=2.
Cauchy implies |translated c_m|<=2^E_m, E_m=ph+a+1+m+
ceil(log2(B^(p(n-m)))). All ceilings via integer arithmetic. Finite
truncation suffices because only coefficients through n enter.
CRT product >2^(max E_m+1) certifies unique signed reconstruction.
For CM163 B=3 for both slices, E arrays [5372,5308,5244,5180] and
[5069,5005,4941,4877], 14 rings, product 5413 bits.
Reconstruct eight integers (four zero witnesses, four nonzero
consumer coefficients); no full-polynomial recovery on normal path.
Optional --ring-oracle invokes full slice reconstruction per ring and
checks translated residue equality; --reference checks existing
signed-hex full coefficient file after reconstruction only.
CRT maintains O(1) reconstructed integer slots at fixed jet order,
not an O(1) total working-memory theorem. Series M=O(p^2) unchanged.
Old full power table O(p^2) residue slots replaced by constant number
of length O(p) arrays in extraction. Norm/series dominate overall memory.

Local final source Python 3.13.5/SymPy 1.14.0, serial subprocess runs
including construction, exact verification, final rational normalization:
- full slices (refactored original --fast-j --bits 384 --reference):
  3.697450925 s; RSS 138272 KiB; 2526 packed calls; 3721676 max operand bits.
- direct (--bits 384 --reference --output):
  3.352723950 s; RSS 138416 KiB; 958 packed calls; same max operand bits.
- direct with --ring-oracle: 6.346344054 s; RSS 138680 KiB;
  3450 packed calls; all 14 rings x 8 translated coefficients PASS.
Earlier prototype 3.123610317 s, RSS 138156 KiB, not used for matched comparison.
Both final normal paths exact s2=77265280/90856689,
gamma=77859659565707/19943834790540897829879824384000.
All eight direct coefficients match stored full slice translation.
Full payload 241632 bits, 61113 JSON bytes vs direct 18425 bits,
4664 JSON bytes (different JSON whitespace conventions, payload counts
independent). Direct nonzero bit lengths [4631,4580,4629,4577].
15.75x fewer reconstructed slots, 62.1% fewer packed calls, 9.3%
less elapsed time in one sequential pair, no observed RSS reduction.
No statistical benchmark or external SOTA claim.

Final --family replay: independently construct low cubic and high
Masser quadratic jets, low ring oracle enabled, different moduli target
widths 128 and 384, so times NOT a matched level speed benchmark.
| D | low/high levels | gamma | low/high seconds |
| --- | --- | --- | --- |
| -11 | 3/11 | 289/8830976 | .003908/.042307 |
| -19 | 5/19 | 275/226934784 | .011166/.228938 |
| -43 | 11/43 | 268427/226492858368000 | .088244/3.211053 |
| -67 | 17/67 | 44248307/6269455245182976000 | .357782/16.550388 |
All PASS same rational gamma and known s2; lower ring comparisons
1+2+6+11 rings. Classical K supplied. Higher cases use direct jets,
not full independently reconstructed polynomials. Both levels share
arithmetic backend, so not independent software implementations.
Level 163 Masser comparison still OPEN; optional --compare-masser
command exists but level 163 has not been run. Independent root
enclosures, external PARI/FLINT/FriCAS comparison, native SWAR full
backend, and proof/kernel acceptance remain OPEN.
Reproduce from repository:
python scripts/check_cm163_residue_swar.py --fast-j --bits 384 --output full.json
python scripts/check_cm_direct_jet.py --bits 384 --reference full.json --output jets.json
python scripts/check_cm_direct_jet.py --bits 384 --reference full.json --ring-oracle
python scripts/check_cm_direct_jet.py --family
Next: exploit sublinear-in-full-output norm consumer / tighter height
bounds, compare equal residue widths at different levels, run level 163
where resources permit. No CI or Agda run in this packet.


## 20 November — P9.M15 quotient norm reference and ring-solver boundary

Reference: scripts/check_cm_quotient_norm.py, implementation commits
561b7bcb406650efec54764ef80fb45b568deef9 and
00c29732aba34287fb3b4836baa20340ed2dd8b5.
Classical norm/resultant identity, not a novelty claim.
For R_n=R[q]/(q^(n+1)), A=R_n[t]/(t^p-q), split H into
H_r(q)=sum_k h_(pk+r) q^k. The multiplication matrix in the ordered
basis 1,t,...,t^(p-1) has entries H_(i-j) if i>=j and q H_(p+i-j)
otherwise (row i, column j). Its determinant is Res_t(t^p-q,H).
Terms beyond t^(pn) cannot contribute to the norm through q^n.
Normalized H(0)=1 implies norm(0)=1. Logarithmic route uses
L=t H' H^{-1}, not t H' H. The new reference uses exact ZZ[q]
determinant before coefficient reduction, so no division in the
possibly non-field residue ring is required. It is NOT a bounded-memory
production algorithm. Reduce H modulo the monic t^p-q before calling
SymPy resultant: a direct high-degree call exhibited a global sign
discrepancy at p=3, degree 9; preserve determinant orientation and
constant coefficient control. Local independently transcribed test:
48 determinant/reduced-resultant comparisons PASS (p=2,3,5,7;
n=1,2,3; moduli 4,9,25,121). Initial expanded Berkowitz test timed out;
exact polynomial DomainMatrix determinant used instead. Committed script
also includes scalar logarithmic recurrence where k is invertible;
exact committed script replay not yet performed, no PASS claimed for it.

Ring-solver reuse candidates: BalabanCanonicalRealPolynomialSolver,
BalabanRealPolynomialRing, NSTriadKNExactRingSolverBridge and
scripts/audit_agda_solver_fibre_boundaries.sh. Prior donor recovery
reported in preceding discussion; no new kernel receipt. Use abstract
commutative-ring scalar normalization, quotient interpretation and
determinant multiplicativity before instantiated coefficient transport.
P9.M14 unchanged PASS (previous receipt).
P9.M15a donor identification recorded; same-ring adapter OPEN.
P9.M15b quotient formulation derived.
P9.M15c small reference source implemented; production structured norm OPEN.
P9.M15d small independently transcribed parity PASS; original normalized
product and all eight translated jets parity OPEN.
P9.M15e runtime/RSS production comparison OPEN.
P9.M15f Agda quotient and determinant/logder same-object weld OPEN.
P9.M16 full level-163 Masser comparison OPEN.
Next: replay committed reference; compare original small-prime inputs,
then implement truncation-aware structured elimination or norm descent,
preserve existing packed backend as oracle. Do not claim a speedup from
residue decomposition alone. No CI or Agda execution.


## 20 November — P9.M15g split-prime cyclic orbit doubling

Candidate source scripts/check_cm_cyclic_orbit_norm.py, commit
a14e3d6c35d3eb57ed1b704cc867c35c87253f3a. Classical cyclic norm and
binary powering/orbit composition, no novelty claim. Choose prime
ell=1 mod p, ell>n, r=ell^e, prime p. Euler exponent projects onto
order p; require z^p=1 and gcd(z^k-1,r)=1 for 1<=k<p. These unit
conditions imply that the orbit product has zero coefficients outside
multiples of p, even over non-field Z/r. CRT still requires pairwise
coprime moduli and the original deterministic height bound; new split
modulus family has not been integrated into CRT yet. F_a(t)F_b(z^a t)
=F_(a+b)(t); all products truncate at pn. For p=41 five doublings and
two composition products suffice. No long inverse or logder needed;
short inverse retained for existing direct-jet contract. Current code
stores logarithmically many full blocks, so no memory improvement claim.
Independent local scalar transcription checked 30 randomized cases:
p=3,5,11,17,41; prime and cube modulus; n=1,2,3; complete projected
norm equality to scalar logder and all off-residue coefficients zero.
Not exact committed source replay, not original modular input parity.
New script runs original diagonal/fixed inputs and existing packed
oracle at identical split moduli, reporting per-slice times.
P9.M15g candidate source implemented, synthetic parity PASS;
original modular input replay, eight-jet/CRT transport, matched
performance and Agda kernel weld OPEN. Run:
python scripts/check_cm_cyclic_orbit_norm.py --bits 384
Next compare memory streaming via recursive binary prefix (double
accumulator then append H for a set bit), eliminating stored blocks;
consider diagonal H=J(q)-t^(p-1)J(t) valuation filtration and
truncated binomial/log expansion separately. No CI/Agda execution.


## 20 November — P9.M15h streaming orbit and diagonal valuation, CRT transport

Source commits 4d2b733befc3eea2d1cbe887635486638aae28df (streaming
binary prefix), de55af0622bd0ce450c20baf08fea59b1148e068 (opt-in direct
jet split CRT), 47b932e6c5bb3561f25fae5522099b2c1622464d (diagonal
valuation candidate). All source-written, no fresh execution receipt.
Prefix update F_(2m+b)=F_m(t)F_m(z^m t)H(z^(2m)t)^b, b in {0,1}.
Constant number of full series arrays, not constant total memory.
Original logder remains default and unchanged. --orbit selects split
moduli with pairwise coprime prime bases, retains original height
certificate, short H inverse and original jet consumer; --ring-oracle
compares every selected coefficient at the same modulus to old full slice.
For diagonal H=A(q)-t^(p-1)B(t), recover B from actual H and A=J(q).
log(N(H)/A^p)=-p sum_{k=1}^{floor(pn/(p-1))}
Pi_p(t^(k(p-1))B^k)/(k A^k). Truncate B^k at pn-k(p-1),
and A^-k at n-ceil(k(p-1)/p). Restore via short formal exp and A^p.
At p=41,n=82, top=84. Need units through max(n,top), not merely
through n: split prime 83 is a negative admission control at p=41.
Harness skips valuation candidate when this condition fails; orbit
itself has no such log denominator requirement. Valuation candidate
not default or wired into CRT. Classical formal log/exp and norm
identities, no novelty claim. M15h streaming source implemented;
M15i valuation source implemented; M15j orbit CRT transport source
implemented; all exact-head runtime, production parity, timing/RSS and
Agda kernel gates OPEN. M16 full level 163 remains OPEN.
Reproduce:
python scripts/check_cm_cyclic_orbit_norm.py --bits 384
python scripts/check_cm_direct_jet.py --orbit --bits 384 --ring-oracle
python scripts/check_cm_direct_jet.py --orbit --bits 384 --compare-masser
Last command potentially expensive; not executed here. No CI initiated.


## 20 November — exact-source SymPy acceptance (M15h/i)

GitHub connector retrieved norm source from 119acf4065691c2ce718811ec30c8a633aea5566.
Local git hash-object confirmed blob 14c80df19871435e2ac7d088e871cad3f7dc06fe.
Executed with SymPy 1.14.0 and independent scalar modular convolution:
36/36 streaming orbit versus scalar logder, 18/18 exact ZZ[q]
determinant/resultant versus orbit, 36/36 diagonal valuation versus orbit,
and explicit nonunit rejection at p=41,n=82,r=83^2 PASS.
Levels 3,5,7,11,17,41; orders 1,2,3; first two admitted split prime
powers of at least 12 bits; seeded synthetic coefficients. Determinant
comparison restricted to levels 3,5,7. Local harness preserved in
scripts/check_cm_norm_sympy_acceptance.py at 7e9cc1f1d438daf7fdac3f13b8278e94ddf05c02
(import narrowed to four functions; same test body). No fresh execution
of that exact harness blob after commit. M15h/i synthetic runtime PASS,
original modular input, packed backend, direct jets/CRT, full level-163
comparison and performance still OPEN. SymPy used instead of Agda for
computational acceptance by user direction; not a kernel theorem receipt.
No CI initiated.


## 20 November — original-input residue acceptance and comparative negative result

Local execution at f5e6dd37492a0808503ec9be5d8bdcd223085be9:
norm module exact Git blob 14c80df19871435e2ac7d088e871cad3f7dc06fe.
Independent nonnegative GMP Kronecker convolution, original raw input
formulas transcribed, J generated modulo r from the original Euler
pentagonal/E4^3/eta^24 identities, Newton inverse and delta*J=E4^3
checked. Independent logder recurrence with H*L=tH' check.
SymPy 1.14.0 Poly.shift(K) over ZZ on full residue polynomial
representatives compared modulo r with direct translated jet formula.
Levels 3,5,11,17,41; two split prime powers per level, >=384 bits.
Prime bases respectively (7,13),(11,31),(23,67),(103,137),(83,739).
20/20 orbit/logder norm cases, 6/6 admitted valuation cases, 80/80
translated coefficients PASS. Four diagonal valuation cases excluded
by nonunit denominator condition, not failures. Peak combined process
RSS 136460 KiB, not a backend-specific memory comparison.
Level 41 observed norm-only seconds (orbit, logder):
83 diagonal (.122159,.084985), fixed (.056417,.041607);
739 diagonal (.121342,.089824), fixed (.061263,.042790).
739 diagonal valuation .608603 s. Shared modular J setup .180391
and .163600 s for the two rings respectively. Single observations,
not statistical timings. Same independent multiplication backend,
not exact production GMP implementation comparison. No SOTA claim:
logder wins these level-41 observations. Keep default unchanged.
M15d.2 original mathematical input parity PASS on this residue sample;
M15d.3 modular jet parity PASS, full integer CRT still OPEN.
Production source-byte replay, repeated matched timings/RSS, level
163, external competitors, Agda kernel acceptance remain OPEN.
Next prioritize projected logder arithmetic and tighter height bounds,
compare modular J generation against shared integer J including all
CRT rings, and benchmark best internal route against direct specialized
external methods. Do not equate outperforming a full modular polynomial
construction with SOTA for CM derivative evaluation.


## 20 November — P9.M15k complementary cyclic receiver and selected packing

Source scripts/check_cm_projected_product.py commit
7127ee4eac9af4014ee7774b73f132603b1ab797. For D=tH', G=H^-1,
write D=sum t^i D_i(q), G=sum t^i G_i(q), q=t^p.
Pi_p(DG)=D_0G_0+q sum_(i=1)^(p-1) D_i G_(p-i).
This is the exact complementary-residue contraction, not a claim that
projection is a ring homomorphism. The q carry is essential.
Nonnegative Kronecker packing canonicalizes residues modulo r and
chooses byte width w with 256^w > min(len(a),len(b))*max(a)*max(b).
No interlane carry; decode only indices 0,p,...,pn. Reference uses
Python integer multiplication, NOT the native GMP production backend.
It still computes the full packed integer product and materializes its
bytes; only coefficient decoding and reduction are reduced.
Local SymPy 1.14.0 execution of independently written source and
scalar convolution: 72/72 three-way exact selected-packed vs
complementary-fibre vs ZZ polynomial multiplication comparisons.
Levels 3,5,7,11,17,41; n=1,2,3; moduli 83,83^2,739^3,2^384;
seed 9, signed inputs. Committed harness is equivalent but not yet
byte-identical replayed. No timing or memory improvement claimed.
M15k reference and synthetic parity PASS; native GMP selective
unpack, original modular input/jet integration and matched benchmark OPEN.
Retain full inverse verification: projected H*G=1 alone is not
sufficient to certify G. Do not weaken original full H*G check.
Next compare selective native export/unpack against original packed
convolution and p short complementary products, with shared inverse.
For height geometry, optimize rational circle radius per slice/order,
rather than least admissible integer B alone, and stop each slice at
its own deterministic CRT threshold; preserve centered uniqueness.
Full CRT, level 163 and external SOTA comparison remain OPEN.


## 20 November — cross-PR quadratic norm and complementary parity (CMP102)

Paper 3 / PR #1444 commit 1cf86519fd571b091301c864297a160de1a6d3eb transfers the original BishopFiniteEvenOddSeriesReindexExact from this branch unchanged, with identical exponent-owner blob on both branches. The signed degree-2n row has 2n+1 entries; retain the final even endpoint. The Yang–Mills specialization uses the already-local real factorial binomial producer rather than requiring the complex capstone.

A shared mathematical observation, not a new CM theorem or performance claim: for the rank-two algebra R[t]/(t^2-z), conjugation sends t to -t, and the multiplication matrix of a+bt is [[a,zb],[b,a]]. Its determinant is a^2-zb^2. For the factorial series C(z)=sum z^n/(2n)! and S(z)=sum z^n/(2n+1)!, exp(T_z)=C I+S T_z with T_z=[[0,z],[1,0]], giving determinant C^2-zS^2=1 by complementary signed binomial coefficients. At z=0, T_z is nilpotent. The Monster cyclotomic norm a^2-ab+b^2 is a related rank-two determinant, with different defining polynomial. This illustrates the multiplication-operator norm and complementary fibre viewpoint without identifying the quadratic algebra with Paper 9's general cyclic quotient, or transferring analytic convergence to a modular residue ring.

For CMP102, shift the vanishing positive-degree coefficients before limit evaluation to avoid division by z; actual Bishop convergence, native unit quaternion and physical attachment remain OPEN. No new Paper 9 analytic, CRT, performance or kernel gate is promoted. Keep existing projected-product/inverse verification and M15k obligations unchanged.


## 20 November — retained-strand carry, joint-observer separation and aggregate norm

Reconciled c6cee9cd47978acc18d788a8846efbd0738c71a6: intervening
CMP102 commit changes only Paper 9 and roadmap, preserved.
SweetgrassCarrierSpine, JPlusOne369FibreCarryHyperformalismExact
(lowerResiduePersistsAcrossCarry, carryRequiresJAndJPlusOneReading)
and KimmererNarrativeMetaphorCalibrationExact are methodological
donors, not mathematical proof owners. Robin Wall Kimmerer (2013)
retains cultural attribution; no cultural-to-mathematical authority promotion.
For residues r,s,u in [0,p), carry omega(r,s)=floor((r+s)/p)
satisfies cocycle identity by associativity of integer addition.
Joint observer separation: on R[t]/(t^(pn+1)), Pi_p(t^j H) for
0<=j<p jointly distinguish H; for coefficient i choose j=(-i) mod p,
then i+j<=pn and the selected coefficient is H_i. Thus universal
future complementary observers do not admit a nontrivial quotient
identifying distinct polynomial states. Restricted actual consumers
may permit further compression; representation compression is distinct.
Aggregate A_k=[X^k] truncated at M=pn for H=1-X, X(0)=0.
Projected q-logder coefficient L_i=-sum_k p*i*A_k[pi]/k.
Exact rational recurrence N_i=sum_(j=1)^i L_j N_(i-j)/i.
This is ordinary word aggregation, not primitive-necklace extraction,
and not a complexity improvement over production Newton logder.
Local SymPy 1.14.0 execution of scripts/check_cm_winding_geometry.py:
PASS carry, reachability, trace, aggregate norm: [75668, 537, 54, 54].
Carry ranks 2,3,5,7,11,17,41; reachability orders 1,2,3.
Trace and determinant ranks 2,3,4,5,6,7; trace powers 1..2p;
three signed/sparse X fixtures and orders 1,2,3. Exact ZZ[q]
DomainMatrix determinant oracle. Local git hash-object and connector
readback agree at blob 7ec8e7e0efdedf90f38ebdb947cf9b33841a45ab,
implementation commit 58019ca7622906de429ee386b8a2935bf57dd5e3.
M15l weighted wheel/trace finite PASS; M15n aggregate norm finite
PASS; carry cocycle and joint observer theorem algebraically derived
with finite controls. M15m block-factorization runtime, M15o efficient
primitive repetition aggregation, original modular production parity,
GMP selection, contour, CRT, level 163, external SOTA OPEN.
No new CI or Agda execution. Default algorithm unchanged.


## 20 November — scope clarification and valuation-filtered binary repetition

User objective clarified: SOTA specifically means fast certified pi. CM/modular-j
and cyclic norm arithmetic remain active complementary research, not a required
world-record claim. For pi prioritize matched end-to-end comparisons (including
constant generation, precision certificate, and output) against established
fast pi implementations; no new pi benchmark in this packet.

For original diagonal H=A(q)-t^(p-1)J(t), A=J(q), set U=t^(p-1)J(t)/A.
Then val U=p-1 and (1-U)^(-1)=prod_(k>=0)(1+U^(2^k)), truncated when
2^k(p-1)>pn. The projected derivative is p*q*A'/A-Pi_p(tU'/(1-U)).
Compute successive powers with shifted leading support, retain full inverse
verification, and reconstruct norm by the original q-logder recurrence.
Requires units only through n for norm reconstruction, not through
floor(pn/(p-1)) as the earlier valuation-log route did.
Independent local Python/GMP harness /tmp/p9/filtered.py using previously
transcribed original raw-input formulas and modular J generator:
10/10 exact diagonal norm comparisons with Newton logder, 10/10 full
(1-U)*G=1 verification; p=3,5,11,17,41, two split prime-power rings
per p, >=384 bits. Includes previously inadmissible valuation-log p=41
prime base 83. Level 41 single norm-only timing pairs (Newton, filtered):
83 (.08962,.19454) s; 739 (.08852,.19045) s. Shared J setup excluded.
Both routes use same independent nonnegative GMP convolution; no production
byte replay, statistical speedup, external benchmark, or Agda receipt.
Filtered repetition is slower; keep default Newton unchanged. Source
harness not yet persisted to repo in this packet. Sweetgrass retained-strand
motif remains attributed to Robin Wall Kimmerer, not mathematical authority.
Native selected extraction, contour optimization, full CRT and level 163 OPEN.


## 20 November — COMP1/2: projective binary splitting and shared compression programme

Fast certified pi remains the SOTA benchmark target; compression remains a
first-class cross-programme research objective, including CM, Monster/VOA,
FRACTRAN/FRACDASH and TOE. Do not demote wheel/holonomy, connectedness,
primitive repetition or retained-strand consumer sufficiency to discarded
ideas merely because a prototype is slower.

Reuse scripts/check_chudnovsky_exact.py (blob
eb58d9dd1d0a2e0d62e9ef16a0ad1ee9703e0e6b) and the existing
HypergeometricBSplitIntegerMergeExact owner. For Chudnovsky only the generic
extra denominator is 1. Triple (P,Q,T) represents [[P,T],[0,Q]].
Merge (pP,qQ,tQ+pT) is associative. Common nonzero scaling is
compatible with both left and right composition, preserving P/Q,T/Q
over Q with Q nonzero. Canonical primitive integer triple with Q>0
is sufficient for these rational observations, not for absolute
integer scale or arbitrary unrelated consumers. Do not transfer
this quotient into a residue ring where canceled factors are nonunits.
Tail enclosure retains original alternating bound and integer-isqrt
sqrt(10005) bracket, conditional on classical Chudnovsky identity.

Implementation scripts/check_pi_projective.py, commit
1055652c4a91a70aef8a607f3060a69fbfed9846; local git hash-object and
connector readback match blob 19c01fff2ff1326b47119a44c930ce7ed1fa1df2.
Actual local Python/SymPy 1.14.0: symbolic scalar-matrix compatibility,
400/400 interval split comparisons (a=0..19,b=a..a+19), 14/14 independent
factorial prefix sums. All three tested rational pi intervals identical
between modes and width <=10^(-digits). No new Agda proof.
Three-run sequential median interval computation, same specialized
triple constructor, CPython integer/Fraction arithmetic, normalization
at every leaf/internal node versus none:

| digits | terms | plain ms | normalized ms | plain final bits | normalized final bits |
|---:|---:|---:|---:|---:|---:|
| 1000 | 73 | 0.550 | 0.575 | 12222 | 9017 |
| 10000 | 716 | 28.915 | 26.835 | 142231 | 90212 |
| 50000 | 3573 | 616.538 | 539.675 | 784923 | 451516 |

At 50000 digits ~42.5% final carrier size and ~12.5% elapsed reduction.
Final summed bit lengths are NOT peak RSS. Width bound is NOT a proof
that decimal endpoint rounding agrees; add identical floor(10^d*L)
and floor(10^d*U) with adaptive refinement and actual output timing.
No external SOTA comparison; normalization may be costly at other scales.
Classical prior art includes Chudnovsky binary splitting and rational
common-factor removal; no novelty claim before review.

COMP1 algebraic projective composition derived and finite PASS.
COMP2 exact normalized split prototype PASS, production/native GMP OPEN.
COMP3 predictive prime valuation cancellation: seek gcd(P_left,Q_right)
which divides both numerator addends AND both products; cancel before
large products, compare residual post-merge gcd; prime-factor sieve
and factorial valuations as alternative. COMP4 operand-balanced tree
and empirical thresholds OPEN. COMP5 native GMP/MPFR/FLINT and
established fast pi external benchmark, certified output and peak RSS OPEN.
COMP6 Monster/VOA orbit/stabilizer, multiplicity and action compression:
reuse #1250, #1179, #1472 and actual Monster369ZetaSameObjectWeldExact,
JInvariant369Zeta6561MonsterCrosswalkExact, JInvariantLambdaOrbitBase369BridgeExact,
JInvariant369ConsolidatedNextStageExact. Graded trace/character parity
does not certify literal vertex operators, intertwiners or full action.
COMP7 FRACTRAN/FRACDASH shared program and exact reconstruction OPEN.
COMP8 general contextual consumer-preserving quotient/factorization
reuse canonical TOE owner, retain negative controls for projected
carrier non-descent. Sweetgrass/Robin Wall Kimmerer (2013) remains
cultural/methodological attribution, not mathematical proof authority.
All earlier CM gates, including projected GMP, contour, primitive
necklaces and level-163 Masser, remain active and unchanged. No CI initiated.


## 20 November — COMP3a: complementary pre-multiplication cancellation

For triples (p,q,t),(P,Q,T), g=gcd(p,Q)>0, write p=g*p0,Q=g*Q0.
The merge equals g*(p0*P,q*Q0,t*Q0+p0*T). Cancel before materializing
all three outputs. Works over integers with nonzero Q, including signed p.
This is classical rational cross cancellation, not novelty claimed.
Cross-only mode need not return a primitive triple; sufficient rational
consumer is preserved despite residual common scale.

Exact local run of scripts/check_pi_cross_cancel.py, commit
6e3a7236c5b521b53612ff0206e1f493dfb3886f; local git hash-object and
connector readback identical blob 3ccd75ca55528965d4f69ec207305d8ac33b5b8c.
SymPy symbolic matrix identity PASS; 1200/1200 subinterval comparisons
(400 intervals, three modes against plain), including canonical gcd
checks for modes 1/2. Four modes: 0 plain, 1 post-gcd, 2 cross+post-gcd,
3 cross only. Exact common decimal floor of rational endpoints certified
for each mode, all modes match at each precision, conditional on classical
Chudnovsky identity and alternating tail. No refinement needed.
Three-run sequential medians include interval computation, scaled endpoint
floors and decimal string conversion, exclude hash and separate carrier
measurement. CPython standard integers; SymPy only symbolic oracle.

| decimal places | terms | bits | plain ms | post gcd ms | cross+gcd ms | cross only ms |
|---:|---:|---:|---:|---:|---:|---:|
| 1000 | 73 | 4032 | .622 | .708 | .663 | .586 |
| 10000 | 716 | 40032 | 34.370 | 29.647 | 30.068 | 28.475 |
| 50000 | 3573 | 200032 | 675.993 | 590.620 | 602.470 | 553.565 |

Final triple summed bit lengths by mode:
1000 [12222,9017,9017,9030]; 10000 [142231,90212,90212,90233];
50000 [784923,451516,451516,451549]. Not peak RSS.
SHA256 of decimal integer string floor(10^d*pi), no dot:
1000 8a84d58d47f78c42a200ebfbbe7346426d4cdf4f2803d45c3590162865fcc0d2
10000 ab03bf7037718e1525340a0c43f0049ddbe99c6067ad3e08a4de5c591fedc524
50000 c330a1682b2ecb5907a1e4819b49b9a920223b3318c4dab73243d0afe2cc2ac1
Cross-only ~18.1% faster than plain at 50000 places, ~42.5% final
carrier reduction, only 33 bits more than fully primitive. Choose as
candidate, not production default or external SOTA. COMP3a PASS reference;
COMP3b factor-sieve predictive cancellation, COMP4 balanced tree and
thresholds, COMP5 native library/external matched benchmark all OPEN.
Preserve COMP6-8 and CM gates: minimal canonical form can be more costly
than sufficient noncanonical carrier; test this separately for Monster/VOA
orbit/action and FRACDASH reconstruction, do not infer equivalences.
No CI initiated or Agda kernel receipt.


## 21 November — P1 369 projective λ sign / punctured-27 holonomy maximum cut (LATEST)

**This week's constructive π work is mathematically more relevant to RH/369 than a speed-only π-digit benchmark.** Reopened original `JInvariantLambdaCyclotomicParityExact.agda` and `JInvariantLambdaOrbitIntegerKernelExact.agda`:
- On source `C3CyclotomicAmplitudeAlgebraExact.Cyclotomic3`, order-three `rotate` and order-two `reflect` satisfy `rotateCubed`, `reflectSquared`, `dihedralRelation`; Eisenstein norm `Q=a²-ab+b²` is invariant.
- **Retained oriented quantity** `V=ab(b-a)` obeys `V(rotate x)=V(x)`, `V(reflect x)=-V(x)`. The scalar Legendre numerator (256Q³) and denominator (V²) forget that sign. All six raw vs normalized λ-orbit representatives are certified equal after their explicit `signedRaw` correction. These are exact rational/polynomial original-source proofs, not yet full analytic `λ(τ)` or classical modular j.
- `scripts/check_369_j_analytic_weld.py` is already an original π PR reference that checks shell convergence and Lambert/divisor coefficients; its original source notes the Bishop same-object finite-to-lattice transport remains open.
- `JInvariantEllipticFixedPointCompilerExact` and `JInvariantEllipticStandardJValuesCompilerExact` already compile conditional (E_6(i)=0,E_4(ω)=0,j(i)=1728,j(ω)=0) from native modular S/ST and nonzero Delta. CM -163 has exact 128-bit half-integer endpoint **integer** check `JInvariantCM163DyadicHalfIntegerExact`, with analytic q/π/CM-integrality link OPEN. Hypergeometric P/Q/B/T binary splitting is an acceleration for the same π/complex analytic branch, **not** an independent analytic proof.
- This avoids falsely solving the analytic (j) problem from the first E8 root coefficient. E8→E4 root coefficient 240 remains a true first-shell equality; higher-shell `theta_E8=E4` and selected lattice analytic same-object remain open.

**New source module in this PR:** `DASHI/Moonshine/JInvariantLambdaPunctured27SignMaxCutExact.agda` imports and reuses the actual existing rational cyclic λ and punctured-27 sources. It restates exact original `rotateEven`, `reflectOdd`, `reflectNorm` on the original cyclotomic carrier; on the independent native punctured cube it reuses `decodeEncode` and the **actual native four-cycle** `noEdgeCompatibleOrientation`. This is **two source-typed sign obstructions**, NOT an invented same-object map between λ and 13-axis geometry. Agda compiler pending; no CI.

**Independent local check:** exact SymPy `Q(Rx)=Q(Sx)=Q(x)`, `V(Rx)=V(x)`, `V(Sx)=-V(x)` PASS. On original ternary point-set analogue, exact local Python shows 26 nonzero / 13 projective axes, all 16 four-cycle bit assignments impossible; 3^5 separate index tuples give 3888 sign-obstruction regressions. These are arithmetic experiments, NOT new Agda kernel checks.

**Cross-PR integration:** RH #1533 now owns `RHGRHIndexedPunctured27HolonomyExact.agda`, which attaches the original same five-coordinate (h,t,k,j,v) to the native 13-axis orientation/sign/residual, with the original no-global-edge-section obstruction. TOE #1291 keeps ownership of the governed six-face indexed residual cube; no source theorem implies arbitrary six-face commutation by changing the index. Link the five-axis **same-object** λ phase/CM operator only if one can construct original selected operator/observer and prove commuting edge correction. An *invariant scalar j* cannot restore the forgotten (V) sign or cure spatial holonomy without new information.

**Next priorities:** (1) original Bishop (λ(τ)) / weight-4/6 Eisenstein-to-standard-j normalized analytic SAME carrier and selected nonzero Delta; (2) source-typed sign/residual correction on the original #1291 cube, not forced equality across nontrivial holonomy; (3) selected j=0/CM cubic Jacobi and global Hecke original character if constructible; (4) P0 original RH/GRH imports remain separate. No new Monster representation, Hecke theta or RH claim.


## 23 Nov — explicit j=1728 signed-V collision and pointed nine / YM H05 non-descent

The existing master JInvariantAnalyticJCoarseFineObserverExact, JInvariantRiemannObserverResidualSufficiencyBidiExact, JInvariantSheafHyperformAdmissibleDescentExact and JInvariantJCoarseFineElevenTritChartShiftExact ALREADY own this observer/Fricke/relative-fibre story. Source-owner [YM #1536 four-mark/H05/j9 audit](https://github.com/chboishabba/dashi_agda/blob/agent/ym-p0-cmp119-r445-master-weld-20261121/Docs/physics/YMClayP0FourMarkKTimeJ9SufficientConsumerCommutingSquare20261123.md) adds a **local exact SymPy collision receipt**, not new analytic-j theorem: for rational modular-j algebraic chart Q(a,b)=a²-ab+b²,V(a,b)=ab(b-a),j=256Q³/V², source pairs (1,2),(2,1) have identical j=1728 but opposite signed V=±2; at V=0 rational j is undefined/pole. Thus coarse j cannot FactorsThrough orientation-sign consumer, matching THIS roadmap's existing forgotten-V warning. It does not identify original elliptic/analytic τ states without source uniformization.

Punctured nine T² has 8 nonzero + one fixed central zero; five antipodal inversion orbits × two sign orientations =10 labelled slots, two over zero. The *chosen* 9+1 pointed coding retains the extra zero-branch residual; it is NOT the already-proved **eleven-trit** 1+10 ↔2+9 source shift or J+1 marked Monster unit and must not silently become a physical YM gauge zero/ζ zero. H05 #1291 owns six-face indexed source; RH #1533 owns C26/time-k and signed actual-zero obstructions; YM #1536 owns four ORIGINAL marked F19 coefficients and the nonzero covariant mixed-log determinant. Cross-domain analogy only; original analytic-j Bishop λ(τ)/Eisenstein, source Fricke and sign/cusp domain still require separate proofs. No Agda/Lean/CI or claims of RH, Moonshine or Clay physics closure.


## 23 November 2026 — COMP3b exact prime-valuation carrier; performance negative control

Continuation of COMP1/COMP2/COMP3a from scripts/check_pi_cross_cancel.py,
with the same original Chudnovsky P_k=-24(2k-1)(6k-5)(6k-1),
Q_k=640320^3 k^3 and the *same* rational interval and decimal-floor
consumer. New scripts/check_pi_prime_valuation.py on this PR,
commit e45255afd9065ad23b3d4fbef28eca2478a164ce;
the locally executed script and connector readback have the identical
Git blob 8ae26be179e4664eb373ec8628136c66b96a250a.

At each leaf build exact prime-exponent Counter maps for |P| and Q.
Represent 640320^3 through triple the exponents of 640320; multiply
leaf factors 24,(2k-1),(6k-5),(6k-1) and k^3. At each internal merge
compute the intersection e_l=min(v_l(P_left),v_l(Q_right)), reconstruct
g=prod_l l^e_l and divide P_left,Q_right *before* constructing
P_left*P_right,Q_left*Q_right,T_left*Q_right+P_left*T_right.
Update the maps by the exact cross cancellation, then sum remaining
P and Q exponents. This is an exact factorization invariant of the
cross-only triple, not of T. No factorization of an arbitrary large
post-merge integer is attempted.

Local CPython execution: 64/64 prefixes (n=1..64) match cross-GCD
**identical P,Q,T integers** and reconstruct |P|,Q exactly from
the tracked prime maps. Three-run sequential medians for certified
decimal floors, with shared integer-isqrt and Fraction output:
| digits | n | cross-GCD ms | valuation-map ms | final sum of P/Q/T bits |
|---:|---:|---:|---:|---:|
| 1000 | 73 | 0.595 | 1.932 | 9030 |
| 10000 | 716 | 26.930 | 41.999 | 90233 |
| 50000 | 3573 | 534.913 | 612.077 | 451549 |

Exactly the same certified decimal strings at all three precisions,
including prior SHA256 for 50000:
c330a1682b2ecb5907a1e4819b49b9a920223b3318c4dab73243d0afe2cc2ac1.
The SPF sieve construction is outside both timed modes (and adds extra
overhead to the valuation approach in end-to-end use); separate map
reconstruction assertions are also outside the timed inner loop.
Full-map bookkeeping is 14.4% *slower* than cross-GCD at 50000 digits
and produces NO smaller integer carrier. This is a matched local
negative result, not a native GMP/FLINT/MPFR or external SOTA benchmark.
The cross-GCD route remains the fastest of these two modes at 50000.

COMP3b exact predictive factoring PASS finite reference; COMP3b
*performance improvement FAILED at these scales*. Narrow next cut:
selective valuations for known small/smooth primes; compute the
residual cross-GCD or a certified residual-coprimality check to preserve
exactness, and measure the factor-map setup cost. COMP4 tree-shape and
COMP5 native/externally certified pi remain OPEN. Preserve CM M15k-p
wheel/primitive repetition, GMP selective coefficients, contour and
full 163 Masser, and COMP6 Monster/VOA full-operator versus trace
non-descent, COMP7 FRACDASH reconstruction, COMP8 consumer quotients.
No cultural-metaphor-to-mathematical-authority promotion:
Robin Wall Kimmerer / Braiding Sweetgrass is methodological attribution.
No Agda/Lean compiler or CI run; classical Chudnovsky identity is
external and Bishop same-real transport remains OPEN.


## 23 November — COMP3b selective valuations with residual GCD (local negative result)

Starting live #1529 head 8c6dd40630689b0b12f08f9a2d21f6333b89b81c.
Committed scripts/check_pi_selective_valuation.py at
5c718494b8c1e67d4523b753393607d9e519d58e.
Candidate carries exact selected-prime exponents of the Chudnovsky
P,Q leaves for all primes <=B, B in {7,31,127}. At each interior
merge, remove the intersection of P_left and Q_right selected
valuations before materializing products, and then apply residual
gcd(P_left,Q_right) to preserve FULL projective exactness.
For primes outside B, no support is discarded. Exponents of P,Q
are updated through multiplication and tracked cancellation.
This is not a claim that the output triple is more compressed than
the original cross-GCD-only representation.

Local CPython fixture (from the same algorithm source, not a
byte-identical replay of GitHub script): 448/448 exact subinterval
triples and selected-valuation invariants PASS for four prime bounds
2/7/31/127, 16 starting indices, lengths {0,1,2,3,4,8,16}.
All 12 certified decimal outputs for modes {cross-GCD, select <=7,
<=31, <=127} at digits {1000,10000,50000} agree exactly and
retain prior 50000-digit SHA256:
c330a1682b2ecb5907a1e4819b49b9a920223b3318c4dab73243d0afe2cc2ac1.
Exact triple summed bit lengths remain 9030/90233/451549 at
1000/10000/50000 digits. Three sequential medians (milliseconds,
enclosure, floor certificate, string conversion; prime list
construction excluded but small):

| digits | GCD | selected <=7 | <=31 | <=127 |
|---:|---:|---:|---:|---:|
| 1000 | 0.663 | 1.109 | 1.290 | 1.501 |
| 10000 | 27.055 | 30.984 | 33.650 | 37.833 |
| 50000 | 554.043 | 574.189 | 607.291 | 620.726 |

Selective <=7 is ~3.6% slower than existing cross-GCD at 50000;
higher selected-prime bounds become slower. Approximately half the
selected <=7 merge calls still need a nontrivial residual GCD at
50000 (5325 of 10716 calls across three runs, 49.69%). 127 reduces
residual-nontrivial cases to 450/10716, but adds greater overhead.
No native GMP, memory/RSS, randomized order, external SOTA or Agda
acceptance in this packet. COMP3b exact constructive route retains
PASS, matched runtime improvement FAILED at tested scales.

Research next: quantify per-prime cancellation benefit vs bookkeeping
and fuse leaf/merge valuation operations in native code only if it can
beat GMP gcd; prioritize COMP4 trees and COMP5 production pi output
and independent established comparator. Do NOT close the CM wheel
winding/primitive necklace, projected GMP, contour or level-163 Masser,
or COMP6 Monster/VOA operator-level, COMP7 FRACDASH reconstruction,
COMP8 all-future-consumer non-descent. Robin Wall Kimmerer / Braiding
Sweetgrass is methodological attribution, not a theorem source.


## 23 November — COMP4 ordered multiplication-tree geometry

Implemented scripts/check_pi_tree_geometry.py on #1529 commit
b7f023a8a6e68b996736f123eced00d047660225,
connector readback blob 22ae2bfdf14df1ce226cca3d8c11ebfefb48a2aa.
Reuse original Chudnovsky integer P,Q,T split and exact COMP3a
pre-multiplication cross GCD: (p,q,t)*(P,Q,T) with g=gcd(p,Q)
computed as (p/g*P,q*(Q/g),t*(Q/g)+(p/g)*T).
Compare ordered (noncommutative upper triangular transport) contiguous
interval trees using midpoint, predicted q-bit-weight midpoint,
quarter and three-quarter split. Preserve ORIGINAL series order;
never permute leaves by valuation, since arbitrary reordering changes
the noncommutative split and may change term semantics.
Weight predictor cumulative sum log2(640320^3)+3log2(max(k,1)).
This is heuristic, not rigorous bit-cost optimization.

Independent local CPython harness /mnt/data/check_pi_tree_geometry.py
with same algorithms: 612/612 exact subinterval P/Q and T/Q parity;
12/12 identical certified decimal-floor strings at 1000,10000,50000
digits, same 50000 SHA256
c330a1682b2ecb5907a1e4819b49b9a920223b3318c4dab73243d0afe2cc2ac1.
Three-run sequential medians (milliseconds; includes interval,
scaled exact floor and decimal string; excludes statistics collection):
| digits | midpoint | weighted | quarter | three-quarter |
|---:|---:|---:|---:|---:|
| 1000 | .634 | .647 | .673 | .615 |
| 10000 | 27.024 | 27.657 | 28.315 | 30.370 |
| 50000 | 541.004 | 564.890 | 553.486 | 537.535 |

All 50000-digit final sum of P/Q/T bit lengths = 451549 (same exact
cross-cancel output at full interval), not peak process RSS.
The initial three-quarter marginal lead is not robust:
subsequent 7-run pseudorandomized interleaved order control at
50000 digits (same exact consumer and source algorithm) medians:
midpoint 544.361 ms, weighted 545.867 ms, quarter 564.761 ms,
three-quarter 548.431 ms. Order control samples included all
floor and string work. Baseline midpoint leads by only 1.506 ms
over weighted and 4.070 ms over three-quarter; no statistically
established speedup or production promotion.
Tree max intermediate operand bits at 50000:
midpoint 112172, weighted 108684, quarter 162012,
three-quarter 154925; tree max depths 11,13,27,24 respectively.
Proxy bit-products are only illustrative, not actual GMP mul cost
or work bounds. Distinct product tree shapes cannot be treated as
independent Monster/VOA/CM equivalence proofs; same rational
consumer does not reconstruct original operator histories.
COMP4 finite arithmetic parity PASS, measured improvement OPEN/negative.
Keep midpoint COMP3a as baseline. Next test thresholded hybrid trees
only with repeated order-controlled medians, native GMP memory/RSS,
and genuine external pi software at matched certified output.
COMP5 fast pi SOTA, CM winding / necklaces / 163 Masser and COMP6-8
Monster-VOA / FRACDASH / observer-fibre remain OPEN.
No Agda or CI. Kimmerer Sweetgrass relation is cultural/methodological
attribution, not theorem authority.


## 23 November — COMP5 native GNU GMP baseline, byte-identical source acceptance

Native source committed as scripts/check_pi_native_gmp.cpp at
2df45bf7be24dda3e9fdf7ae7f8cdd4028af2d45, Git blob
b5d1d9b7555f559aa4a99225dc98c9ee96a7a9ff.
The local compiled C++ source has exactly that git hash-object, and
GitHub connector readback matches byte for byte. Compile locally:
g++ -O3 -std=c++17 scripts/check_pi_native_gmp.cpp -lgmpxx -lgmp -o /tmp/check_pi_native_gmp
Run /tmp/check_pi_native_gmp 50000 plain 5 and
/tmp/check_pi_native_gmp 50000 cross 5.
Compiler GNU g++ 14.2.0, GMP C++/libgmp.so.10 on Linux x86-64.
No GitHub CI used; no Agda proof promoted.

Uses original Chudnovsky P/Q/T midpoint tree with optional pre-product
gcd(P_left,Q_right) and GMP mpz_class/mpq_class, exact integer sqrt of
10005*2^(2*bits), alternating-tail rational endpoints and integer
floor(10^d*L)==floor(10^d*U) before decimal emission. Includes binary
splitting, interval computation, square root, rational floors and
decimal string conversion INSIDE each timed run; excludes compilation,
process startup and hashes. Source retains classical Chudnovsky
pi identity as EXTERNAL premise and original Bishop same-real
transport OPEN. Distinguish certified precision conditional on the
identity from a new standalone analytic derivation.

Exact output parity for d=1000,10000,50000:
hashes respectively
8a84d58d47f78c42a200ebfbbe7346426d4cdf4f2803d45c3590162865fcc0d2,
ab03bf7037718e1525340a0c43f0049ddbe99c6067ad3e08a4de5c591fedc524,
c330a1682b2ecb5907a1e4819b49b9a920223b3318c4dab73243d0afe2cc2ac1.
Matches prior exact CPython reference and matches native
plain/cross outputs. Native final P/Q/T summed bit sizes at
d=50000 plain 784923 versus cross 451549.

Five-run within-process native medians, milliseconds:
| digits | plain GMP | cross GMP | relative cross improvement |
|---:|---:|---:|---:|
| 1000 | .168645 | .179010 | negative |
| 10000 | 4.869130 | 4.517620 | 7.2% |
| 50000 | 49.345400 | 44.222700 | 10.4% |

Second independent invocation using identical source/toolchain
again matches ALL exact hashes; five-run medians at d=50000:
plain 51.5054 ms, cross 45.8929 ms (10.9% faster).
Single subprocess /usr/bin/time -v for cross d=50000 reported
peak RSS 3076 KiB, NOT matched plain-v-cross peak RSS and NOT
a reliable isolated algorithmic memory comparison.
Relative timings are confined to this specific environment;
do not extrapolate to native GPU or world-record scale.

No installed y-cruncher, PARI/GP or FLINT development headers were
found locally. External SOTA remains OPEN. Public source comparators:
FLINT documentation on fast constants and binary splitting
https://flintlib.org/doc/algorithms/integers/binary-splitting.html ;
FLINT arb_const_pi https://flintlib.org/doc/constants.html ;
y-cruncher official https://www.numberworld.org/y-cruncher/ .
Their published results do NOT constitute matched hardware/precision/
certification benchmarking. Next COMP5: same-environment
FLINT arb_const_pi with explicit uncached work, MPFR/AGM and y-cruncher
if available, verify identical decimal floor plus independently
documented rounding guarantees; compare threads, cold/warm cache,
peak RSS, and complete end-to-end output costs. Consider GMP low-level
mpn in-place multiplication, reduced rational construction overhead,
and streaming output for 100k-1M digits.

COMP3a cross cancellation remains valid and beneficial natively
at d=10000,50000; COMP3b selected-valuation and COMP4 alternative trees
stay negative controls. Preserve the unified COMP6 Monster/VOA
full-action non-descent, COMP7 FRACDASH reconstruction, COMP8
future-consumer sufficiency, CM winding/primitive necklaces and
level-163 Masser. Sweetgrass cultural/methodological attribution
belongs to Robin Wall Kimmerer, not mathematical theorem authority.
