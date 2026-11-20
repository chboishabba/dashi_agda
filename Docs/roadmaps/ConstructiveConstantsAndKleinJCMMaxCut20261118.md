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
