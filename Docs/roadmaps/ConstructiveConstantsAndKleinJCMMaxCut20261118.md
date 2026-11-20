# Constructive constants and actual Klein-j max-cut — 18 November 2026

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
