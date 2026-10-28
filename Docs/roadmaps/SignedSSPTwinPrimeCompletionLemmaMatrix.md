# Complete proposed lemma matrix: 3×3×3 → signed SSP/FRACTRAN → twin primes

**DASHI PR:** https://github.com/chboishabba/dashi_agda/pull/1408
**Cross-PR donor:** https://github.com/chboishabba/dashi_agda/pull/1407

**Scope:** 75 named proof obligations in this *current proposed architecture*:
8 T (coordinate/consumer bridge) + the 67 existing A–G tasks.
This cannot promise an exhaustive enumeration of unknown future analytic lemmas
needed to settle the open twin-prime conjecture. It is exhaustive for the
dependency architecture we are actually pursuing as of 2026-10-28.

## Essential correction: geometry, not a bag of labels

`27` is the **capacity**, not the definition. The actual existing
`DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact`
owner defines:

```agda
record Ternary27Point : Set where
  constructor ternary27Point
  field
    x : SSP.SSPTrit
    y : SSP.SSPTrit
    z : SSP.SSPTrit

hypervoxelStateCount = 3 * 3 * 3
hypervoxelStateCountIs27 : hypervoxelStateCount ≡ 27
```

Thus the full carrier is `T³ = {-1,0,+1} × {-1,0,+1} × {-1,0,+1}`.
Its ordered input-pair carrier is `T³ × T³ ≅ T⁶`: **six typed
coordinates**, `(3×3×3)×(3×3×3)=27×27=729` ordered pairs.

PR #1407 explicitly encodes this in
`R2P227729FourierObserverIncidenceExact.ModeCube27`,
`R2P227729PairSixTritFibreBidiExact.SixTritIndex` and
`R2P2ThreeModeBinaryTernaryNSAliasingCutExact.threeAxisSignedModeCount`.
The #1408 `TwinPrimeConsumerParetoObserverExact` adapter now imports
the *existing master* geometry, exhibits exact x/y/z coordinate roundtrips
and exposes axis/product cardinalities through all three TOE roots.

Crucial distinction: T³ is a finite geometric *observer address*. Its
three factors are ternary coordinates, **not** three certified distinct
CRT primes, not a 27-element set of arbitrary prime labels, and not a
Monster 3B/4B representation theorem. Pair incidence 729 alone is not
twin-prime distribution.

## Evidence/status legend

- `O`: older named theorem owner found; preserve upstream attribution.
- `S`: source-written Agda in #1408; **kernel check not observed**.
- `C`: conditional theorem/interface that requires a concrete instance.
- `P`: partially covered by named sources; more proofs required.
- `N`: new unimplemented Agda obligation.
- `R`: genuinely open research-grade mathematics, not an implementation bug.

`O` does not imply a successful exact-head kernel check for the *whole*
current PR. `S` must never be shown as a kernel-certified theorem. No CI
is required by the current user request; an actual local kernel receipt
would nevertheless be necessary before promoting a theorem as verified.

## T. Three independent ternary coordinates; eight explicit obligations

| ID | Lemma / acceptance statement | Status / owner |
|---|---|---|
| T01 | `threeAxisTritCarrier`: the address is `SSPTrit × SSPTrit × SSPTrit`, with named x/y/z axes, not an anonymous `Fin 27`. | O: `Base369Ternary27HypervoxelFabricGeometryExact.Ternary27Point` |
| T02 | `threeCoordinateDecodeEncode`: reconstruct a point from its ordered x/y/z coordinates. | S: `TwinPrimeConsumerParetoObserverExact` |
| T03 | `threeCoordinateEncodeDecode`: project the reconstructed point back to x/y/z. | S: same |
| T04 | `threeAxisCountIsThree`: exactly three coordinate axes. | S: same, reuses geometry |
| T05 | `threeAxisCapacityIsThreeTimesThreeTimesThree`: retain the **factorisation** as 3×3×3. | S: same |
| T06 | Preserve `3³=27=1+13×2`, the GLOBAL 14-class antipode, and the distinct inner-phase `3×5=15` quotient | O/S: original geometry, antipodal and Ibrahim owners; explicit 5-vs-20 arithmetic collision in `TwinPrime369IbrahimQuotientBoundaryExact`, kernel pending |
| T07 | `orderedPairAxisCountIsSix`: two ordered 3-coordinate points have six coordinates. | S; #1407 also has an exact `TritCube 6` BIDI owner, separate branch |
| T08 | `orderedPairCapacityIsSevenHundredTwentyNine`: 27×27 = 729 is a cardinality of typed ordered pairs. | S; #1407's independent 343/386 incidence result stays source-owned |

### Existing signed geometry refinement: 1 + 13×2 = 27

The **already-on-master** `DASHI.Foundations.BalancedTernaryAntipodalOrbitExact`
owns `ternaryCubeCountDecomposesAsCentrePlusThirteenPairs` and
`antipodalClass27CountIsFourteen`: the genuine three-axis cube
`{-1,0,+1}³` has a unique all-zero fixed centre, thirteen nonzero
strict-sign antipodal pairs, and fourteen C₂ orbit classes. The
`TwinPrimeConsumerParetoObserverExact` module now **reuses** both
owner theorems with its existing x/y/z cardinality declaration.
Its arithmetic theorem is merely that this structured observer is
a quotient and must retain additional data for twin-primality queries.

PR #1407 has since added the separately owned
`R2P227729AntipodalThirteenFiveOrbitFourierCutExact`,
`R2P227729HermitianThirteenPairFourierCodecExact` and
`R2P227729HermitianConvolutionTransportExact` source-written modules.
For Hermitian `f(-k)=conj(f(k))`, the centre-plus-13-pair data can
retain a restricted Fourier field, and a decoded convolution can retain
the required finite outputs. This relies on the **Hermitian constraint**.
There is no reason to impose that constraint on an arbitrary Nat prime
emitter or identify Fourier Hermitian symmetry with prime correlations.
No direct branch-only import was made and attribution remains with
the established antipodal owner and the #1407 proof author.

These two reused named results refine T06's geometry evidence rather
than introducing new uncounted dependencies on the arithmetic
twin-prime proof. The 75-ID architecture tally is unchanged.

## A. Signed SSP / FRACTRAN source machine (10 obligations)

| ID | Lemma | Status / exact outstanding cut |
|---|---|---|
| A01 | SSP lane identity, including carrier 2 | O: `SignedSSPFRACTRANWeaveExact`; audit on current branch |
| A02 | Signed magnitude interpretation in arithmetic | P: signed constructors exist; prove full compiler decoder |
| A03 | Canonical signed normal form | N: normalisation theorem for actual signed register states |
| A04 | Exactly one active sign-state carrier per register | O/P: FRACDASH paired-register implementation; link exact target |
| A05 | Enabled fraction iff all denominator valuation guards hold | O/P: numeric first-applicable and generic vector interfaces |
| A06 | First-applicable scan determinism | O: `FRACDASHNumericInterpreterTargetExact`, `FractranCOL` |
| A07 | Each signed IR step simulates a numeric FRACTRAN macro | P/C: bridge interfaces; concrete general instance needed |
| A08 | Arbitrary finite signed trace simulation | S/C: `SignedSSPPrimeEmitterTraceTransportExact.traceSimulation` requires exact step-alignment |
| A09 | Halting / emitted readout integrity | P: precise terminal power-of-two marker plus decoder/acceptance proof |
| A10 | Register-prime renaming invariance | N: permutation of carriers preserving fractions, guards and readout |

## B. Source/target arithmetic interpretation (8 obligations)

| ID | Lemma | Status / exact outstanding cut |
|---|---|---|
| B01 | Carrier prime labels distinct from arithmetic generated primes | S: explicit firewall in `SignedSSPPrimeOutputBoundaryExact` |
| B02 | Accepted output has a unique decoded natural exponent | S/P: concrete proof-carrying exponent residual; **raw VM decoder still missing** |
| B03 | Real compiled execution and arithmetic decoder commute | P: ±2 code-level square written; concrete whole-program compiler missing |
| B04 | Source arithmetic +1/+2 compilation | S/P: +2 fraction macro; arbitrary +1 and actual dispatcher not yet proved |
| B05 | Source arithmetic −2 compilation | S: guarded two-step `[1/6]`; actual dispatcher outstanding |
| B06 | No signed/Nat wraparound or subtraction underflow | S/P: p=2+k guarded; arbitrary machine safety outstanding |
| B07 | Correct arithmetic macros compose for arbitrary admitted programs | N: selected instruction/compiler composition and no spillover |
| B08 | Arithmetic output completeness over every requested Nat | C: codec representability; executed prime emission still missing |

## C. All-prime generation and signed compiler (9 obligations)

| ID | Lemma | Status / exact outstanding cut |
|---|---|---|
| C01 | Historian-correct Conway/Guy ordered fraction program | O: Conway 1987, Guy 1983; finite Python replay not a kernel theorem |
| C02 | Numeric FRACTRAN step iff prime valuation-vector update | N: one-step equivalence for complete program |
| C03 | Prime output marker iff exact decoded exponent | N: sound output-marker/readout theorem |
| C04 | Every emitted exponent is arithmetically prime | N/O: historical theorem must be imported/proved against concrete code |
| C05 | Every arithmetic prime p eventually occurs | N/O: formalise historical completeness for the selected ordered program |
| C06 | Emission order and unique prime-output indices | N: distinguish output repetitions from distinct exponents |
| C07 | Arbitrarily large source prime outputs are reachable | N/O: derived only after a proper C05 theorem + prime infinitude |
| C08 | Signed SSP compiler matches historical reference outputs | C: `transportReferencePrimeEmitter` *provided the actual compiler/readout instance* |
| C09 | A nontrivial signed-specific invariant affecting arithmetic primes | R: no new distribution theorem observed; not implied by encoding |

## D. Exact ±2 on generated prime outputs (8 obligations)

| ID | Lemma | Status / exact outstanding cut |
|---|---|---|
| D01 | +2 two-step fraction macro | S: `SignedSSPPrimeOffsetMacroExact.plusTwoFractionMacro` |
| D02 | −2 two-step fraction macro, p≥2 | S: `minusTwoFractionMacro` |
| D03 | Correct macro guards, actual first rule, final output and halting | S/P: two certified fraction steps; full interpreter composition outstanding |
| D04 | Preserve the original Prime p certificate and provenance | S/P: conditional encoded endpoint certificate transport |
| D05 | Neighbour +2/−2 BIDI inverse on decoded Nat | S: `SignedSSPBidirectionalNeighbourExact` |
| D06 | Pair of independent prime certificates implies true `TwinPrimeAt` | S: `TwinPrimeCertifiedEnumeratorExact` and BIDI transport |
| D07 | Every true twin pair is representable in coded finite enumeration | S: `SignedSSPTwinFiniteCoverageExact`; source runtime reachability still C08 |
| D08 | Canonicalise double-counting of (p,p+2) via upper/lower readout | N: proof of unique canonical lower endpoint / list normal form |

## E. Actual arithmetic CRT / sieve (15 obligations)

| ID | Lemma | Status / exact outstanding cut |
|---|---|---|
| E01 | `CertifiedPrimeAxis` carries real `Prime modulus` witness | S: `CertifiedPrimePairModulusExact` |
| E02 | Modulus 2 is retained and has exactly one pair-survivor residue | P: six-wheel owner and finite probe; general Nat theorem still required |
| E03 | For odd prime p the two excluded classes differ | N: arithmetic proof p>2 |
| E04 | Exactly p−2 locally surviving residues for each odd p | N: Fin/cardinality proof; cannot assume it from a Python count |
| E05 | Arithmetic CRT reconstruction from general pairwise-coprime certified prime moduli | P: explicit FINITE modulus-270 affine CRT injection and 27-case lookup in `TwinPrimeTernary270AffineCRTCodecExact`; general inverse and 270-survivor Agda coverage theorem still N |
| E06 | Forward/reconstruction inverse laws for arbitrary coprime CRT | P: 27-element cube/270-wheel decode-after-encode proof is source-written; arbitrary-axis true CRT BIDI and exhaustive 270-coverage in Agda remain N |
| E07 | General finite pairwise-coprime prime product CRT | N: inductive step with a coprime-product proof |
| E08 | Exact total survivor count `∏(p−ν_p)` modulo product | N: leverage E02–E07 and `FinitePrimeProductSieveExact` |
| E09 | Product of any finite prime moduli is a sieve period | S: `CertifiedPrimePairPeriodExact` (even with repeated axes) |
| E10 | Filter order invariance | S: same owner; reordering conjunction |
| E11 | Duplicate prime filter idempotence | S: same owner |
| E12 | Fresh filters only remove candidates | P: monotonicity theorem / explicit refinement import |
| E13 | Genuine twin p,p+2 passes each proper finite small-modulus filter | N: handle modulus equal to endpoint and range assumptions correctly |
| E14 | ∀ finite certified-prime axis lists and N, construct n≥N with both endpoints Composite, and all local pair filters passed | S (kernel pending): `everyFinitePrimeSieveHasLargeDoubleCompositeSurvivor` covers empty and nonempty lists; no CRT inverse, coprimality or fixed SSP15 limit |
| E15 | FRACTRAN decoded-exponent / CRT commuting square | S/P: signed ±2 decoded square; additionally explicit cube/270 finite C2 affine endpoint-swap and certified p2/p3/p5 local sieve; full signed VM interface outstanding |

## E14 max-cut: factorable double-composite family, no CRT inverse

For any finite certified axis list, let `P=modulusProduct axes`.
For any given surviving `r≥2` and `t≥1`, set

```
L = r * (1 + P*(r+2)*t)
U = (r+2) * (1 + P*r*t)
k = r * (r+2) * t
```

**Exact identities:** `L+2=U`, `L=r+kP`. Therefore
`AllPairSurvive axes r ⇔ AllPairSurvive axes L` by the already
source-owned `allPairProductPeriodicMultiple` and its inverse.
The four multiplicative factors are all strictly greater than 1.

New `DASHI.Arithmetic.FiniteTwinSieveFactorableLiftExact` contains
source-written semiring equalities, both sieve transports, strict
`TwoNontrivialFactors` witnesses for L and U, the `suc`-indexed
proof that every product of certified moduli is positive, and
`factorableSurvivorWithBothStrictFactors` for any given surviving
`r=suc(suc a)`. Distinctness and coprimality are **not needed**.

The universal baseline **has now been written as Agda source**, not
merely numerical intuition. In
`FiniteTwinSieveUniversalCompositeBaselineExact`:

- `baselineMinusOne b = 2(suc b)−1` uses natural arithmetic without
  truncated subtraction;
- `baselineLocalPairSurvives` proves that for any certified axis p|P,
  both `2P−1` and `2P+1` have nonzero residue modulo p. It reuses
  `m%n≡0⇒n∣m`, `∣m+n∣m⇒∣n` and the actual `Prime p` witness.
  An assumed zero remainder would force p|1, contradicting p≥2;
- `baselineAllPairSurvivesAtCommonPeriod` structurally reuses the
  original `CommonPeriod` certificate for each axis;
- `anyFinitePrimeSieveHasBaseline` applies the product-period owner;
- `axisHasAtLeastTwo` and
  `nonemptyModulusProductHasAtLeastTwo` show every nonempty
  certified prime-axis product is ≥2;
- `everyNonemptyFinitePrimeSieveHasDoubleCompositeSurvivor`
  applies the factored lift to that baseline;
- `factorableLeftLinearInParameter`,
  `factorableLeftDominatesParameter`, and
  `factorableSurvivorExactOutputIsComposite` keep the exact
  growing output and show it exceeds an arbitrary threshold;
- `everyNonemptyFinitePrimeSieveHasLargeDoubleCompositeSurvivor`
  packages **∀N, ∃n≥N** satisfying all finite sieve predicates
  while carrying `Composite n × Composite(n+2)`.

The exported wrapper `everyFinitePrimeSieveHasLargeDoubleCompositeSurvivor`
now completes the **empty-list** branch explicitly with baseline
`r=2`, `P=1`, `t=N+1`. Its nonempty branch consumes the
previous nonempty theorem, so the type quantifies over **all**
finite certified-prime axis lists with no nonemptiness condition.
The additional lemma has no new mathematical assumptions or
postulates. All claims remain Agda **source-written only**.

These are constructive finite-sieve obstruction theorems at the
**source-written** level. They do not require a CRT inverse and do
not prove the broader Selberg parity theorem or anything about
infinitely many *prime* pairs. Since Agda has not been typechecked,
the final universal theorem remains **kernel pending**.

The independent Python witness checks exercised the previous 504
factorable survivors plus **54 extra unbounded-threshold cases**
across six finite prime lists (including duplicates and modulus 2).
All integer identities, thresholds and strict factors passed.

DHJ Polymath/ Selberg sieve parity historical authority remains
source-owned. The construction shows why no *fixed* finite local
test is a proof of genuine twin-primality once a survivor exists;
it is not itself the full analytic parity theorem. Do not use
3×3×3 Fourier/Monster labels or Ibrahim 3B analogy as a proxy
for any arithmetic prime-pair correlation.

**Next max-cut:** unconditional baseline and monotonicity lemmas,
then source-to-target FRACTRAN compiler reachability and a genuine
analytic correlation result.

### E14 promotion to genuine arithmetic non-primality

Further cross-check of the pinned Agda standard library found the
**existing true predicate** `Data.Nat.Primality.Composite`, smart
constructor `composite-≢`, and `composite⇒¬prime`.
`FiniteTwinSieveFactorableLiftExact` now upgrades its explicit
`suc(suc a) * suc(suc b)` factor certificates via
`twoNontrivialFactorsAreComposite` and
`twoNontrivialFactorsRefutePrime`; it exposes
`factorableSurvivorWithBothCompositeCertificates` and
`factorableSurvivorCannotBeGenuineTwin`.

These results no longer merely describe **integer factors**: the
source-written types demand actual stdlib `Composite n`,
`Composite(n+2)`, `¬Prime n` and `¬Prime(n+2)` proofs. The original
Nat primality kernel owner is reused; no alternative primality or
analytical oracle is introduced. Exact-head Agda typechecking remains
pending, so source-written proof terms must NOT be called
kernel-verified.

**Not yet discharged:** for any given arbitrary certified axis list,
the `r=suc(suc a)` sieve survivor is an input premise. Proving its
universal construction from `2P−1` with base `P=∏p` and deriving a
formal unbounded/injective family remains the E14 kernel-level gap.
The independent finite Python tests exercised those baselines without
proving the universal Agda statement.

## F. Arithmetic-analytic leap (9 obligations)

| ID | Lemma | Status / exact outstanding cut |
|---|---|---|
| F01 | Uniform distribution of emitted genuine primes across arithmetic progressions | R: prove an exact quantified distribution theorem |
| F02 | Joint primality correlation for n and n+2 | R: **central unresolved mathematical gate** |
| F03 | Signed/SSP weighted sieve corresponds to actual arithmetic sums | N/R: semantics for weights and proofs of positivity/equality |
| F04 | Uniform distribution/remainder estimate strong enough for pair lower bound | R: needs a legitimate analytic estimate, not fitted finite results |
| F05 | Signed-specific quantitative gain survives complete arithmetic decoding | R: information not present in ordinary arithmetic must be shown and sourced |
| F06 | Explicitly overcome or bypass the *pure sieve* parity obstruction | R: prove genuine method-specific new information; generic reformulation insufficient |
| F07 | Positive unbounded pair-counting criterion for gap exactly two | R: target `∀N∃p≥N,Prime p × Prime(p+2)` |
| F08 | Correctly transport GPY/Maynard/Polymath bounded-gap theorems | C: preserve all stated analytic assumptions and gap parameters |
| F09 | Discharge any imported external assumptions needed for an unconditional proof | R: conditional works remain conditional |

## G. Conclusion, integration, promotion (8 obligations)

| ID | Lemma | Status / exact outstanding cut |
|---|---|---|
| G01 | Infinitely many actual certified twin-prime pairs | R: **not proved** |
| G02 | Constructive `∀N∃p≥N` equivalent to infinitely many distinct pairs | N: formal set/list infinitude equivalence |
| G03 | Distance-two prime pair is consecutive among primes | N: no integer strictly between odd endpoints can be prime; handle (3,5) |
| G04 | Canonical TOE export through all three intended roots | S: current source imports present |
| G05 | Zero forbidden escapes/no fabricated theorem authority | P: static hole/escape scan; code audit still needed |
| G06 | Exact-head Agda kernel type-check of complete import closure | N: **no successful kernel receipt**; CI not requested |
| G07 | Independent review of analytic proof, if any, and its input hypotheses | N/R: no analytic proof exists to review yet |
| G08 | All original authors / dated primary sources / PR proof ownership preserved | P: source genealogy and ownership documented; keep review active |

## 2026-10-28 local Python max-cut: 14 rules / 10 factors / 15 SSP carriers

This continuation corrected an earlier **factual attribution/count error**.
The 15/14,15/2 variant recorded by Richard K. Guy (1983) contains
**14 ordered fractions**. The alternate 15/2,1/7 Conway (1987)
presentation ALSO contains **14 ordered fractions**. See original
Conway FRACTRAN paper and OEIS A202138, A007546 and A203907.
The typed `SignedSSPFRACTRANWeaveExact` atlas independently contains
**15 carrier primes**, not 14 rules. Of those 15 prime constructors,
the Guy programme requires **exactly ten distinct factors**:
2,3,5,7,11,13,17,19,23,29.

`DASHI.Arithmetic.PrimegameSSP15CarrierFactorisationExact` source-writes
each Guy fraction as a product of actual existing SSPPrime constructors
for numerator and denominator. The theorem
`typedFractionsAreExactGuyFourteen` asks Agda to prove the resulting
ordered list definitionally equals all 14 historical numeric fractions.
`guyProgrammeRuleCountIsFourteen`,
`primegameUsesTenTypedCarriers` and
`originalSSPAtlasHasFifteenTypedCarriers` keep all three counts
explicit without creating new register primes or new "proven" output
prime theorems. The module is wired into all three TOE facades and
is **Agda source-written, kernel pending**.

`scripts/check_primegame_ssp15_valuation_bisimulation_local.py`
reuses the existing 14-rule Python fixture and compares integer
FRACTRAN to a ten-prime valuation vector. The independently executed
local Python equivalent (20,000 steps; all 14 rules observed) verified
priority guard equivalence, exact successor exponent updates, 20,001
integer reconstructions, and nine prime-exponent marker events at
published steps 19,69,280,707,2363,3876,8068,11319,19201.
This is finite evidence only, **not** C02's universal Agda lemma,
and not C04/C05 machine-completeness or the actual signed runtime.

`DASHI.Arithmetic.FiniteTwinSieveNoPromotionExact` additionally
derives, for every finite certified prime-axis list and every lower
bound N, an actual `n≥N` surviving all pair filters with separate
`¬Prime(n)` and `¬Prime(n+2)` certificates. This refutes a claimed
general implication `AllPairSurvive → TwinPrimeAt` even eventually.
The proof reuses the already-written universal double-Composite
constructor rather than restating primality or making a new sieve.
Exact-head Agda typechecking remains unperformed.

Local symbolic Python/SymPy expansion proved the factor identities,
and seeded integer testing verified **2,703 cases across 159 finite
prime-modulus lists**, including repeated moduli, p=2 and empty lists.
All local checks are independent computational evidence, not kernel
receipts or arithmetic distribution theorems. The x/y/z geometry
remains `3×3×3=27`; 13 antipodal pairs + centre retain prior owners;
Monster 3B/4B and Ibrahim prior attribution remain unchanged.

**Remaining frontier:** fully general source-Agda integer↔valuation
one-step equivalence, exact first-applicable signed-SSP compiler and
reachable outputs, arithmetic CRT inverse, and a genuine joint
prime-pair distribution estimate. Neither a 14-rule enumeration
nor an SSP15 codec establishes infinitely many twin primes.

## 2026-10-28 numerology max-cut: exact finite 3³, 9→5, 3×5=15, and CRT-270

The complete source-owner / scope / verification ledger is
[SignedSSPPrimeNumerologyCrossPollinationLedger.md](SignedSSPPrimeNumerologyCrossPollinationLedger.md).

**New source-written owners:**
- `TwinPrimeThreeAxisLocalThreeOrbitExact`: the x=−1 slice of
  `Ternary27Point` has nine balanced y/z residues
  `n=−1+3y+9z(mod27)`, all with `n≡2(mod3)` and
  `n+2≡1(mod3)`. Affine prime-endpoint reversal
  `n↦−n−2(mod27)` equals inner strict antipode. Therefore the
  exact nine-coordinate *local* orbit quotient has one fixed centre
  plus four pairs = five classes. The real
  `LocalPairSurvives` predicate is transported conditional on an
  actual certified prime-3 axis.
- `TwinPrime369IbrahimQuotientBoundaryExact`: imports the
  **existing source-owned** Ibrahim 27→3×5=15 phase reduction and
  separate global 27→14 antipodal residual codec. It proves the
  3×5 phase quotient COLLIDES actual centered residues 5 (genuine
  5,7 twin pair) and 20 (not twin). It therefore cannot answer even
  that restricted actual arithmetic query without its missing inner
  orientation. A different inherited code preserving the dependent
  residual reconstructs all three axes. The existing nine-axis
  `3+3+3` Pareto chart gives `3⁹=19683`. The Agda guard
  `3⁵=243 ≠ 5³=125` rejects numerical conflation with the
  exceptional E6 source-owned PR #1389.
- `TwinPrimeTernary270AffineCRTCodecExact`: explicitly maps the
  typed ternary cube into 27 genuine 2/3/5 finite local sieve
  survivors modulo `270=27×2×5`, using the affine expression
  `(41+108d(x)+30d(y)+90d(z)) mod270`. The 27-case
  partial inverse proves injectivity on cube points and the
  `n↦−n−2` sign-involution equation. It source-writes all six
  local remainder/nonzero checks and transports them to the
  **actual certified** `AllPairSurvive` for supplied p=2,3,5
  axes. Independent exhaustive Python additionally checks that
  the image covers all 27 arithmetic survivors among 0..269,
  but THIS COVERAGE IS **NOT** an Agda theorem yet.

**Independent local Python:** nine prime-3 survivors, five
inner C2 orbits, 14 global 3³ C2 orbits, 15 phase-preserved
inner-orbit labels, 27 pair-sieve survivors modulo270, exact
270-element exhaustiveness and 27 affine reversal identities
all passed. Separate finite FRACTRAN and factorable-sieve checks
were rerun. Original Ibrahim Monster, Conway/Guy, PR #1407
and Polymath8b attribution is unchanged. No ESD or CI changes.

**Next proof:** E05/E06 finite 270 *coverage* in Agda using
the existing `Fin`/residue-owner operators; C02/A07/C08
the concrete faithful all-step signed FRACTRAN compiler;
F02/F04/F07 the genuinely open analytic joint-primality
frontier. All new sources remain **Agda-kernel pending**.

## Critical dependency DAG

```text
T01–T08   exact 3×3×3 x/y/z observer, product-pair coordinate meaning
   ├─> consumer query adequacy / collision (already source-written on #1408)
   └─> no arithmetic prime inference from 27 or 729

A01–A10 ──> B02,B03,B07 ──> C02,C03,C08 ──> C04–C07
                    │                            │
                    └─> D01–D08 (signed ±2) <────┘
                              │
                              v
E01–E04 ──> E05–E08 ──> E13–E15 (CRT/decoder/finite pair evidence)
                              │
                              v
F01–F06 (new signed-invariant + analytic correlation; NOT derivable
         from any finite CRT or bijective encoding alone)
                              │
                              v
                  F07 -> G01 -> G02,G03 -> G04–G08
```

**Max-cut / Pareto:** first reuse `Ternary27Point` and exact generic
consumer sufficiency. Next prove the specific *concrete* signed
FRACTRAN interpreter/compiler/readout instance (A05/A07/A08/B03/C08)
against the canonical reachability owner. Then true arithmetic CRT
inverse and p−2 local counts (E02–E08). Lastly a new quantitative
joint-primality theorem (F02/F04/F07), with independent scrutiny of
sieve parity. Snowball only from proof-bearing inputs and date/source
roots. IBM/Monster or Ibrahim 3B/4B fingerprints cannot promote
a same-object representation or gap-two theorem.

**Mathematics source:** DHJ Polymath, *Variants of the Selberg sieve,
and bounded intervals containing many primes*, Research in the
Mathematical Sciences 1 (2014), article 12, DOI:
https://doi.org/10.1186/s40687-014-0012-7.
It proves H1≤246 unconditionally and H1≤6 under generalized
Elliott–Halberstam; the parity argument concerns purely sieve methods.

**Acceptance boundary:** a file with an Agda proof term is source
written, not kernel verified until an exact-head type-check exists.
The actual all-prime reachability theorem is not supplied by a finite
SSP15 label set, numerical tests or by the presence of a field in
an uninstantiated record.
