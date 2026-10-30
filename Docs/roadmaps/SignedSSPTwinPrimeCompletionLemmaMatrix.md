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
| E05 | Arithmetic CRT reconstruction from general pairwise-coprime certified prime moduli | P: explicit FINITE modulus-270 affine CRT injection and 27-case lookup in `TwinPrimeTernary270AffineCRTCodecExact`; general inverse remains N; finite 270-survivor coverage source-written in TwinPrimeTernary270SurvivorCoverageExact (kernel pending) |
| E06 | Forward/reconstruction inverse laws for arbitrary coprime CRT | P: 27-element cube/270-wheel decode-after-encode proof is source-written; arbitrary-axis true CRT BIDI remains N; finite 270-coverage source-written, kernel pending |
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

## 2026-10-28 extension: actual finite CRT-wheel reverse coverage (new owner)

The source-written `TwinPrimeTernary270SurvivorCoverageExact` now adds the
missing reverse direction **at the finite 270-element residue level**.
It reuses the already typed `Ternary27Point(x,y,z)`, the source-owned
injective affine encoder, and the certified prime-axis predicates.

- `wheel270CompleteFin`: every one of the 270 representatives
  passing the actual 2/3/5 pair guards admits a typed cube preimage.
- `certifiedWheel270ToGuards` and `wheel270CompleteCertified`:
  transport from real `CertifiedPrimeAxis` evidence, not a new oracle.
- `wheel270SurvivorDecodes`: a local sieve survivor has a successful
  `wheel270ToCube` readout (no unexplained `nothing`).
- `wheel270ProjectionMod27`, `wheel270ProjectionMod5` and
  `wheel270ProjectionMod2`: the precise arithmetic decomposition
  `1 × 9 × 3 = 27`. The x trit selects an allowed mod-5 class,
  y/z encode the 9 allowed mod-27 classes, and parity is fixed.

The proof table has **270 computed cases: 27 inverse witnesses and 243
rejections** by an explicit modulus/equality contradiction.
Independent exact Python arithmetic checked all 270 instances. The
Agda compiler is unavailable here. These declarations are **source
written, KERNEL PENDING**, not G06-discharge.

Status refinement: E05/E06 advance for this special 2/3/5 wheel
only. E05–E08 for general pairwise-coprime moduli remain open, as do
A07/A08/B03/C08 for the full signed PRIMEGAME execution compiler,
F02/F04/F06/F07 and G01 for gap-two analytic infinitude.
The codec is a bijection of finite *candidate residues*, not of
actual twin primes. Finite surving composites remain source-owned
counterexamples. Original Ibrahim Monster 3B ownership and other
mathematical roots are unaffected; no protected ESD files changed.

### Exact typed-cube composite counterexample

Inside this very 27-state image, the point
`ternary27Point sspZero sspPosOne sspPosOne` encodes residue
`119`. The actual finite filters pass, yet
`119 = 7·17` and `121 = 11·11`.
`wheel270119IsComposite` and `wheel270121IsComposite` consume
the earlier `FiniteTwinSieveFactorableLiftExact` constructor for
real stdlib `Composite` evidence; `wheel270119SurvivalCannotProveTwin`
rejects a genuine `TwinPrimeAt 119` proof. This is a concrete
no-promotion example **within the same inverse-coded cube**, not
merely a composite outside its chosen representation.

The committed existing finite regression
`scripts/check_twin_prime_369_affine_270_crt.py` now checks the
243 rejects, three projections and 119/121 factorizations.
Its equivalent exact-integer tests were run locally; CI and Agda
kernel were not run.

**Exceptional small-prime boundary:** the local mod-2/3/5 wheel
excludes n=3 and n=5 because an endpoint equals a sieving prime.
These are genuine familiar twin-prime starts (3,5) and (5,7),
so the mod-270 theorem must be described as *exactly covering the
wheel's local surviving residues*, never as classifying every
genuine pair. The new source-written
`wheel270RejectsExceptionalStartThree` and
`wheel270RejectsExceptionalStartFive` assert the arithmetic
filter exclusions explicitly, and are re-exported through all
three TOE roots. Agda kernel pending.

## 2026-10-28 continuation: Guy priority BIDI plus in-wheel Ibrahim counterexample

### Concrete new proof owners (kernel pending)

`PrimegameTypedNumericFirstApplicableBidiExact.agda` reuses
`PrimegameSSP15CarrierFactorisationExact`'s exact ordered equality of
the 14 typed Guy fractions and the historical 14 numeric fractions,
and `FRACDASHNumericInterpreterTargetExact.FirstApplicableStep`'s
original inductive first-applicable policy.

The source-written lemmas `typedStepToNumeric` and
`numericStepToTyped` preserve and reflect the chosen rule AND every
failed higher-priority guard. `guyTypedToNumeric`,
`guyNumericToTyped`, `guyTypedHaltToNumeric`, and
`guyNumericHaltToTyped` specialise to the **actual 14-rule Guy
programme**. `ExactFractionApplies` uses an integer successor
witness `m*d=n*a` with nonzero denominator. The new `concreteExactFractionEvaluator` now supplies an actual **Nat quotient** evaluator for this arithmetic guard. It uses `Data.Nat.DivMod.m≡m%n+[m/n]*n` and `m*n%n≡0` to prove `next*d=n*a`. A concrete **signed FRACDASH state/action compiler** is still absent.

This advances A05/A06 and the typed-factor part of C02/C03 from a
bare 14-rule list to **first-applicable BIDI source terms**. A07/A08,
B03 and C08 still need an actual signed state/action compiler and
readout commuting proof. No purported historical PRIMEGAME
completeness proof was conjured.

`TwinPrimeTernary270IbrahimSurvivorCollisionExact.agda` strengthens
the earlier arithmetic 5-versus-20 proof by using an **in-sieve**
pair of 3x3x3 states, both passing the finite 2/3/5 filters:

- `(x,y,z)=(0,-1,+1)` encodes 59, a genuine twin start (59,61).
- `(0,+1,-1)` encodes 209=11×19, not a twin start.

The *original Ibrahim* quotient `27→3×5=15` identifies both states
because the x coordinate agrees and y/z are simultaneous antipodes.
`ibrahimFifteenFailsActualTwinConsumerWithinWheel` reuses the
existing `ConsumerCollision`/`nonFactorabilityWitness` theorem
owners and `SignedSSPOrientationTwinClassifierNoGoExact.twinStartBool`
(actual Nat proof-bearing primality decider). Thus this exact
quotient is not even sufficient **after local 2/3/5 sieving**.
The full 3x3x3 state plus an adequate residual remains necessary
for lossless prime-start observation. This does not establish any
Monster 3B same-object equivalence or an analytic prime result.

### Executed finite evidence and next max-cut

Local exact Python executed the 270 residue cases, actual 59/209
in-sieve collision, all 14 Guy factorisations and 20,000 selected
first-applicable integer steps. The new committed regression script
`scripts/check_primegame_typed_numeric_priority_bidi.py` makes the
latter repeatable in-repo; `check_twin_prime_369_affine_270_crt.py`
now includes the 59/209 collision. **No Agda kernel or CI run**.

Remaining direct implementation cut: provide a *concrete*
`ExactFractionEvaluator` for Nat arithmetic, prove its chosen
successor matches the original FRACDASH runtime, preserve 14-rule
priority under signed compilation, and instantiate existing
`ReferenceToSignedPrimeEmitter` only if its independent source
reachability/completeness premises can actually be proved.

Independent subsequent cut: E03–E08 general coprime prime-product
CRT, p-2 local counts and analytic gates F02/F04/F06/F07 and G01.
Existing finite encodings and Monster fingerprints cannot
discharge these analytic estimates.

### 2026-10-28 numeric evaluator is now *source-instantiated*

`PrimegameTypedNumericFirstApplicableBidiExact` now defines
`exactNumericNext`, `exactNumericNextIsCorrect`, and an inhabited
`concreteExactFractionEvaluator` record. The zero denominator is
rejected by `ExactFractionApplies`; for positive denominators,
Agda's stdlib quotient/remainder equations derive exact output
`next*d=n*a` from the arithmetic integrality witness. This is
not an uninterpreted evaluator axiom. The three canonical TOE roots
export `guyConcreteExactPriorityForward` and
`guyConcreteExactPriorityBackward`.

**Scope/evidence:** source-written Agda with explicit stdlib names,
not typechecked in this runtime. Local exact Python tested the
14 original Guy fractions and 20,000 integer steps; it is not the
Agda kernel. The missing A07/A08/B03/C08 frontier is now the
actual signed SSP/FRACDASH action-state simulation plus readout,
not a missing integer-division specification. No branch-only
#1414 polynomial/quintic/monodromy module was imported: #1414
correctly distinguishes its own 27-label endomorphism/S3 meanings
from cube-coordinate semantics, and no mathematical map into the
actual twin-prime correlation was established. Preserve its own
PR ownership and Ibrahim 3B boundary.

## 2026-10-28 executable Guy PRIMEGAME scanner and non-halting cut

`PrimegameTypedNumericFirstApplicableBidiExact` now has a
**source-written executable `firstApplicableNumeric`** and an
`exactFractionApplies?` decision procedure. For positive
denominator d it reuses standard-library quotient/modulus identities
to show that the integrality guard admits exactly the returned Nat
successor `(n*a)/d`; d=0 is explicitly rejected.
`firstApplicableNumericSound` connects a `just after`
computation to the *existing* FRACDASH
`FirstApplicableStep` relation. `firstApplicableNumericHalt`
connects `nothing` to the original conjunction of blocked rules.
`guyTypedExecutableStepSound` and `guyTypedExecutableHalt`
transport those receipts back to the original ten-factor SSP
representation of all 14 Guy fractions.

**Critical semantic correction:** Guy PRIMEGAME does not halt.
Its last instruction is **55/1**, applicable for every Nat n.
`guyLastRuleAlwaysApplies`,
`guyNumericScannerNeverHalts`,
`guyNumericAlwaysSteps`, and
`guyTypedAlwaysSteps` source-write this fact and an actual
selected transition for **every** natural-number state. The
obligation A09 must therefore treat emitted powers-of-two as
readout events on an ongoing trace, not termination output.

Independent locally executed Python checks:
- 270 arithmetic wheel representatives and the 59/209
  inner-antipodal consumer collision.
- 20,000 Guy states from initial 2 with all 14 instructions
  exercised, matching typed/numeric priorities and arithmetic.
- 21,000 individual numeric fraction guards, 3,048 admitted.
- 20,000 separate Nat inputs with a defined first-applicable step.

This improves A05, A06, C02's representation direction, and the
numeric portion of A09. It **does not** prove A07/A08/B03/C08 for
the signed FRACDASH machine, historical prime-enumeration
completeness, an arithmetic CRT inverse, or gap-two infinitude.
No kernel receipt, CI pass, or full signed executor proof is
reported. All new Agda terms are source-written and need an
actual pinned Agda typecheck before being promoted.

Web historical corroboration: Richard K. Guy's 1983 14-rule
version uses 15/14 plus 15/2 and 55/1. Conway's variant differs
(1/7 replaces 15/14), and must stay separate.
OEIS A267572: https://oeis.org/A267572.
No protected ESD surfaces changed. PR #1414 monodromy
objects are branch-only and independent; no same-object
Monster 3B or quintic prime-distribution claim is made.

## 2026-10-28 source-owned S3/C3/Stirling/sign-orbit connection — Q cut

The mathematical identity and its exact **source ownership** are now explicit.

Let T=Z/3Z. Every value permutation in S3 is one of the
six affine maps t -> a*t+b with a=±1 and b∈T; C3 is the
translation subgroup. For an anchored word
w=(w0,w1,...,wn), define

`normalise(w)=(w1-w0,...,wn-w0)`.

Then:
* `normalise(w+b)=normalise(w)`;
* `normalise(-w+b)=-normalise(w)`;
* the section `d↦(0,d1,...,dn)` reconstructs every difference
  vector exactly;
* every anchored word translates to its normalised section.

Therefore there is a canonical (once the first position is chosen)
orbit-set correspondence
`T^(n+1)/S3 ≅ T^n/C2`, with the RHS under simultaneous sign
inversion. This is NOT an equivariant identification of the raw
actions nor a claim that label permutations equal position swaps.

**Original repository owner found:** PR #1244,
`DASHI.Mathematics.Topology.AlexanderHornedS3WordSignOrbitTransportExact`
already source-writes `relativeTranslate`,
`normaliseTranslate`, `relativeReflection`,
`normaliseReflection`, `signedRelativeSection`, and
`normaliseViaTranslation` for **arbitrary n**. The #1244 code says
the quotient equivalence follows from its interface; no explicit
univalent/set quotient implementation, all-n Burnside/Stirling
cardinality theorem, or successful Agda kernel receipt was observed.
Do NOT duplicate this owner or import its unmerged branch as if
it were part of the current master/#1408 import closure.

**Original statistical owner found:** PR #1275,
`ZipfThreeDrawEqualityPatternFactorExact` owns five genuine
three-letter value-S3 equality patterns; its companion
`ZipfTernary27ActionHeapsExact` separates value relabeling,
position permutations, and endomorphism conjugacy. These are
different quotients. The RGS/Stirling interpretation at arbitrary
n is mathematics of set partitions with at most three blocks, not
a Zipf law or a particular corpus law.

**Original invariant field owner found:** PR #1244's
`AlexanderHornedDepthTwoFiveOrbitFibreExact` proves source-written
pointwise inflate/deflate for depth-two native H-invariant fields.
The native end-field rank r_n is described as (3^n+1)/2 in
`Docs/topology/AlexanderHornedInvariantCylinderDirectLimitMaxCut20261028.md`;
that roadmap explicitly says the all-depth count has no kernel
receipt. Count the *orbits* first; the corresponding C3-valued
invariant field cardinality is `3^(r_n)`, not r_n.

For n≥0:
`r_n=(3^n+1)/2=sum_{k=1}^3 S(n+1,k)`.
The single all-zero sign word is fixed, and the other
`3^n-1` sign words form disjoint pairs. Independently,
global S3 value relabelings classify words by equality partitions
of n+1 positions into at most three blocks. Finite exact integer
checks exhaustively confirmed the orbit bijection for n=0,...,6.

| n | length n+1 | Stirling terms S(n+1,1/2/3) | orbit rank r_n |
|---:|---:|---|---:|
| 0 | 1 | 1,0,0 | 1 |
| 1 | 2 | 1,1,0 | 2 |
| 2 | 3 | 1,3,1 | 5 |
| 3 | 4 | 1,7,6 | 14 |
| 4 | 5 | 1,15,25 | 41 |
| 5 | 6 | 1,31,90 | 122 |
| 6 | 7 | 1,63,301 | 365 |

### New Q-series — every remaining orbit/consumer lemma

Statuses: O=pre-existing owner, S=source-written kernel-pending,
P=partially realised, N=not yet source-written, C=requires a
concrete cross-domain same-object/intertwining witness.

| ID | Required exact lemma or proof obligation | Status and current owner |
|---|---|---|
| Q01 | `threeLabelsAsC3`: identify the existing finite ternary label carrier with C3 | O/P: #1244 phase/trit bridge |
| Q02 | `allS3Affine`: all six global value-label permutations are exactly t↦±t+b | P: #1244 translates/reflects; formal S3 action equivalence requires its laws |
| Q03 | `normaliseTranslate`: first-label differences ignore C3 shift | S: #1244 existing source |
| Q04 | `normaliseReflection`: global reflection becomes coordinatewise negation | S: #1244 existing source |
| Q05 | `signedRelativeTranslationInvariant`: signs preserve translation cancellation | S: #1244 existing source |
| Q06 | `signedRelativeReflection`: signed normalization is C2 equivariant | S: #1244 existing source |
| Q07 | `signedRelativeSection`: exact inverse on zero-anchored difference vectors | S: #1244 existing source |
| Q08 | `normaliseViaTranslation`: each anchored word is a translated normal form | S: #1244 existing source |
| Q09 | `orbitMapWellDefined`: normalization descends from full value-S3 to sign-C2 quotients | S: #1244 `s3ToC2`, `c2ToS3`, and `actualWordDifferenceOrbitBidi` now instantiate the arbitrary-depth setoid quotient relations; kernel pending |
| Q10 | `orbitMapSurjective`: section hits every sign orbit | S: #1244 `normalisationSurjective`, `canonicalWordSection` and `wordForCanonicalClass`; kernel pending |
| Q11 | `orbitMapInjective`: same signed orbit implies an original global S3 permutation | S: #1244 `canonicalEqualityGivesWordOrbit`, `canonicaliseComplete`; kernel pending |
| Q12 | `anchoredOrbitBijection`: assemble the exact set quotient equivalence | S: #1244 `CanonicalRelative n`, `wordOrbitGivesCanonicalEquality` and converse provide a constructive full normal form of S3 word orbits; kernel pending |
| Q13 | `S3WordOrbitsAreEqualityPatterns`: same orbit iff same labelled-position equality partition | P: #1275 three-letter instance, all-length theorem missing |
| Q14 | `restrictedGrowthCanonical`: bijection to RGS using ≤3 blocks | P/N: #1275 finite case, arbitrary-length canonicalisation missing |
| Q15 | `restrictedStirlingCount`: #RGS(n+1,≤3)=sum S(n+1,k) | N: classical Stirling theorem; no all-n Agda proof observed |
| Q16 | `uniqueFixedSignWord`: only all-zero vector fixed under simultaneous sign flip | S: #1244 canonical first-nonzero-positive normal form isolates the all-zero class; kernel pending |
| Q17 | `pairPartition`: all non-fixed sign words have 2-element C2 orbits | S: #1244 `canonicalCover` plus `canonicaliseNegationInvariant` and normal-form completeness; kernel pending |
| Q18 | `signOrbitCount`: #T^n/C2=(3^n+1)/2 for all n | S: #1244 `canonicalStepToSum`, `sumCanonicalRoundTrip`, `doubleCanonicalRank` prove all-depth 2r_n=3^n+1; kernel pending |
| Q19 | `stirlingSignCount`: identity both by orbit bijection and by counting | N/P: mathematically established, formal composition missing |
| Q20 | `phaseFieldInflateDeflate`: invariant fields correspond pointwise to functions on sign orbits | S: #1244 n=2 owner; all-n construction still a separate obligation |
| Q21 | `global14WheelNoGo`: two surviving cube points have equal global sign class but different genuine TwinPrimeAt | S: **new #1408** `globalFourteenOrbitLosesTwinConsumer` at 59/209 |
| Q22 | `endpointFlipCommutes`: 270 affine endpoint reversal agrees with strict global C2 | S: #1408 affine codec; full cube correspondence source-written |
| Q23 | `nativeSectorVsValueWordBridge`: intertwine native H-sector action and S3 value-word action on a specified SAME object | C: raw native actions remain different; no imported same-object theorem |
| Q24 | `consumerFactorCriterion`: only C2-invariant observables factor through the 14 orbit classes; twin primality fails | O/S: source-owned ConsumerCollision plus new #1408 global no-go |

The original 75 items T01–G08 remain unchanged in scope; Q01–Q24
are **additional cross-domain proof obligations**, not a hidden
replacement or a proof of joint prime correlations. Arithmetic
applications must keep the extra orientation/residual for
lossless reconstruction and cannot make any true twin-prime
predicate periodic modulo a fixed finite wheel.

**Highest Pareto cut:** Q09–Q12 and Q15–Q19 close the remaining
general quotient/counting *formalisation* using #1244 and #1275
source owners without importing unmerged branches. In parallel,
A07/A08/B03/C08 require a real signed-state compiler, and
E03–E08 require genuine all-prime coprime CRT. F02/F04/F06/F07
remain OPEN MATHEMATICS about gap-two simultaneous primality.
This #1408 addition owns only consumer non-factorability; Ibrahim
Monster 3B, original sector topology, statistical Zipf/Heaps and
2026 polynomial PR owners remain separately credited.

### Q25–Q26: full-cube period-information wall

| ID | Required exact lemma or proof obligation | Status and current owner |
|---|---|---|
| Q25 | `fullCubePeriodNoGo`: full 27-state wheel code at 59 and 329 collides while true twin starts differ | S: new #1408 `wholeCubeResidueLosesTwinConsumer`, `noUniversalTwinClassifierFromFiniteWholeCube`; 329=7×47, 59/61 prime |
| Q26 | `NatWheelResiduePeriodBidi`: preserve the unrestricted quotient k along with r=n mod270, prove n=270*k+r and roundtrip, and show genuine twin observer acts on the **reconstructed Nat**, not residue alone | S: new #1408 `NatPeriod270`, `decodeEncodeNatPeriod270`, `encodeDecodeNatPeriod270`, finite cube-period survivor lift; kernel pending |

**Important information hierarchy:** `S3 equality pattern` /
`C2 sign orbit` (14 classes) is coarser than the full
`Ternary27Point` (27 states). The full cube is a typed
and invertible description of an **admissible residue modulo 270**
but is still a quotient of unbounded integers. Neither 14 nor 27
states suffices to determine genuine `TwinPrimeAt n` for all n.
Even `Nat ≅ (residue, unbounded period index)` is a *lossless input
representation*, not a proof of joint prime correlation.

## 29 October 2026 actual source completion: S3/C2 normal form and Nat period BIDI

**Checked against CURRENT active PR heads before writing.** #1244 already
had explicit forward and converse affine-S3/relative-sign relation
witnesses; the new, original-owner module
`AlexanderHornedS3SignQuotientSetoidBidiExact` adds an
equivalence relation for C2 differences and for S3 words,
a constructive `CanonicalRelative n` normal form, orbit-class
soundness/completeness in both directions, a section to anchored
words, and an exact `CanonicalRelative(suc n) ↔
CanonicalRelative n ⊎ Vec C3 n` constructor BIDI.
Its `doubleCanonicalRank` proves `2r_n=3^n+1` for ALL n,
not just n≤7 numerical checks. This is a typed source
setoid/canonical quotient, **not** the already different native
wild-end/sector or Zipf probability object.

**The arithmetic Q26 owner is newly source-written on this PR:**
`TwinPrimeNat270PeriodResidualBidiExact`. Its full
`NatPeriod270` representation stores `periodIndex : Nat`
and `boundedResidue : Fin 270`. The source proves
`decodeEncodeNatPeriod270` using existing standard-library
Euclidean decomposition and `encodeDecodeNatPeriod270`
using exact positive-modulus quotient/remainder and Fin
injectivity, following the prior repository Gödel base-12
codec's divisor-quotient proof method.
`encodeCertifiedCubePeriod270` additionally reuses the
original *27-state survivor coverage* and returns a
`(period,cube)` with an **exact Nat reconstruction proof**.
`cubePeriodResidueRoundTrip` and
`cubePeriodDecodeToCube` give the reverse residue/cube
direction. Non-admissible residues remain in the full
Fin270 code, not falsely mapped into one of 27 states.
All three canonical #1408 TOE roots import/export these owners.

**Executed independent finite model:** enumerate every anchored
word and all six affine label relabelings for n=0..6,
matching full orbit classes, canonical normal form and
1,2,5,14,41,122,365. Exercise all 270 residues across
five period indices and arbitrary large Nat examples.
Both numerical fixtures passed. Source Agda kernel
typechecking has **not** run (no Agda binary available).

**Still open:**
Q15/Q19 explicitly identify the all-depth
Stirling/RGS **counting** proof with the separately owned
#1275 canonical datatype, rather than relying on numerical
correspondence; Q20 extends the native invariant-field
inflation beyond depth two; Q23 needs a same-object
wild-sector/value-label intertwiner and must remain
conditional. A07/A08/B03/C08 remain the actual signed
machine compiler, and E03–E08 the general certified-prime
CRT. F02/F04/F06/F07/G01 are unsolved analytic
twin-prime mathematics, as confirmed in current primary
bounded-gap and formalisation documentation.
No ESD surfaces, prior Ibrahim Monster 3B owners, or
independent Zipf/Heaps PR proof ownership were edited.

## 29 October 2026: live M-series residual/Mangoldt proof ledger

**Source owners imported, never duplicated:** `DASHI.Analysis.RiemannVonMangoldtSpecification` (original `VonMangoldtAt`/`VonMangoldtFunction`), `DASHI.Cognition.ResidualPhaseGeometry` (`Projection`/`Residual`), `DASHI.Core.ConsumerGuidedReopenableRefinementExact` (consumer-guided strict refinement), `DASHI.Core.NonginOnePointOneArmyRefinementExact` (frame-sensitive consumer), `DASHI.Core.ResidualNaturality` (category-level interface), `DASHI.Arithmetic.TwinPrimeNat270PeriodResidualBidiExact` (lossless full-Nat code). All these owners retain original attribution; Ibrahim Monster 3B and PR #1244/#1275 symmetry/counting proofs are independent.

| ID | Exact obligation | Status and source |
|---|---|---|
| M01 | Reuse native `Phase.Projection` | S: `TwinPrimeResidualMangoldtBidiExact.periodProjection` |
| M02 | Native residual fibre for period code | S: `exactPeriodResidual` |
| M03 | Nat gives a fibre witness | S: `natGivesPeriodResidual` |
| M04 | Any fibre witness uniquely determines original Nat | S: `periodResidualUniqueness` |
| M05 | Any Nat consumer lifts to full period code | S: `liftNatConsumer`/`liftConsumerSound` |
| M06 | Consumer transport preserves both directions | S: `liftConsumerComplete`/`periodConsumerBidi` |
| M07 | Actual von Mangoldt scalar forward | S: `mangoldtPeriodForward` |
| M08 | Actual von Mangoldt scalar backward | S: `mangoldtPeriodBackward` |
| M09 | Pair-weighted correlation forward | S: `pairCorrelationForward` |
| M10 | Pair-weighted correlation backward | S: `pairCorrelationBackward` |
| M11 | Construct and verify an actual `AllPrimeArithmetic` instance, prove its scalar laws | P/N: existing Riemann owner; no fresh analytic instance assumed |
| M12 | Finite intervals: Nat sum ↔ period-coded sum, for arbitrary additive carrier and paired Mangoldt | **NEW S**: `TwinPrimeResidualMangoldtFiniteSumBidiExact.finiteSumBidiForward`, `finiteSumBidiBackward`, `pairFiniteSumBidiForward`, `pairFiniteSumBidiBackward`, `mangoldtFiniteSumForward` |
| M13 | Decompose entire finite interval exactly by 270 residue classes and variable period bounds | N: M12 does not yet prove the nested 270 Fubini/reindex theorem |
| M14 | Separate genuine prime pairs from contributions with at least one proper prime power | N/R: requires a sound prime-power decomposition |
| M15 | Uniform explicit upper bound on prime-power-only correction | N/R: prove, do not infer from tests |
| M16 | Analytic positive-correlation estimate + M14/M15 ⇒ arbitrarily large certified twin primes | N/R: conditional implication missing; premise is **open mathematical conjecture-scale** |

**New source:** `DASHI/Arithmetic/TwinPrimeResidualMangoldtFiniteSumBidiExact.agda`, 29 October 2026, imports the original correlated Mangoldt consumer and existing period-residual BIDI. The theorem is induction on finite interval length, using `cong₂` for additive sum transport; it does not import an assumed analytic estimate. The generic additive carrier requires no unproved positivity/commutativity for this pointwise transport.

**Executed local Python:** 396 exact finite-sum equalities over 33 start indices and six interval lengths, on the actual mathematical von Mangoldt values and paired `Lambda(n)Lambda(n+2)`; 20,000 Nat and 21,600 period-code bidirectional round trips, PASS. These executed checks validate the finite arithmetic model, **not Agda kernel acceptance** or a large-X positive lower bound.

**Critical max-cut:** M13 exact residue partition; M14/M15 proper-power removal; M16 conditional conversion; F02/F04/F06 original analytic positivity/parity barrier; G06 kernel verification. No claim twin-prime infinitude solved. Recent conditional bounded-gap work and Fernando Portela's June 2026 Krafft/Turán preprint are comparative research context, not proof imports. The latter reduces its result to a finite-dimensional optimisation inequality and itself states that inequality is a prerequisite. Preserve original authors and dated roots.

**Integration:** All three TOE roots now import and selectively export the new M12 bridge. All status S markers mean source-written only and are NOT kernel verification receipts. Do not modify ESD surfaces.

### 29 October 2026 continuation: Q25/Q26 actually invoke original CEGAR refinement

NEW `DASHI/Arithmetic/TwinPrimeNat270ConsumerGuidedStrictRefinementExact.agda` does not redefine the original `StrictProjectionRefinement` or `ConsumerGuidedRefinement`. It instantiates those exact source-owned records at the consumer `SignedSSPOrientationTwinClassifierNoGoExact.twinStartBool`:

- `coarseResidue : Nat → Fin 270` versus `finePeriod : Nat → NatPeriod270`.
- `coarseFactorsThroughFine` explicitly forgets the period.
- `fiftyNineAnd329SameResidue` proves the old fibre equality by computation.
- `fiftyNineAnd329DifferentPeriod` proves the fine codes distinct.
- `twinConsumerSeparates` proves consumer outputs different (59/61 true twin; 329 composite).
- `strictConsumerGuidedPeriodRefinement` uses the original CEGAR refinement constructor; `noActualTwinConsumerFromBareFin270` invokes the original no-descent theorem.

This is **source-written only, kernel check pending**. It closes a concrete instance of the strict consumer-guided refinement boundary, not arbitrary all-nat CEGAR completeness. Imported through the three original TOE roots; no ESD modifications.

**Pareto/max-cut:** the immediate finite obligations are kernel validation and M13 full 270-way reindexing; the analytic bottleneck is still F02/F04/F06. Snowball results are only propagated when the typed consumer actually factors through the claimed projection; the original Ibrahim 3B group-action ownership remains separate and unmodified.

## 29 October 2026 — M13 row-wise exact finite partition, further max-cut

**Source-written owner:** `DASHI/Arithmetic/TwinPrimeResidualMangoldtPeriodRowsExact.agda`
on #1408, imported by all three TOE roots. It reuses the existing
`NatPeriod270` true arithmetic BIDI, `TwinPrimeResidualMangoldtBidiExact`
and `TwinPrimeResidualMangoldtFiniteSumBidiExact.AdditiveScalar`.
It neither redefines the Riemann/Mangoldt specification nor imports
unmerged #1244, #1275, or Ibrahim Monster group actions as though
they were the same object.

- `rowNat`, `rowEncodeDecode`: 270k+r with actual `Fin 270` coordinate and exact codec reconstruction.
- `rowConsumerForward`, `rowConsumerBackward`: original Nat consumer = lossless period-coded consumer, both directions.
- `sumFinFrom`, `sumFinCongruence`: finite bounded fold respecting pointwise equalities; **no unproved additive associativity** or permutation invariance.
- `periodRowSum`, `periodRowCodeSum`, `periodRowBidiForward`, `periodRowBidiBackward`: all 270 residues within one period.
- `periodPairCorrelationBidi`: pair Mangoldt-style weighted correlation sum carried exactly through the original Nat codec.

**Actual local Python executed:** 80 complete 270-residue rows,
84 arbitrary partial/period-crossing intervals, 21,600 Nat/period
inverse checks, and finite von-Mangoldt pair correlation equality:
PASS. This is an independent arithmetic model, not an Agda kernel receipt.

**Remain OPEN:** the general arbitrary-interval `M13-interval`
partition theorem that reorders a contiguous finite sum into
potentially partial period rows, with an explicit additive
associativity/commutativity or order-preserving interval reindexing
justification. The 27-survivor extraction requires handling
small-prime exceptional cases, not equating all 270 rows with the
27 admissible points. M14/M15 require actual proper prime-power
classification and a certified asymptotic upper bound. M16/F02/F04/F06
remain the nontrivial positivity/parity-barrier mathematics.
Kernel verification for ALL newly written Agda sources remains open.
The 2026 unrefereed H1<=186 bounded-gap result does not imply gap 2.
No ESD changes; original Conway/Guy, Brun/Selberg/Polymath,
#1244 native C3, #1275 RGS and Ibrahim Monster 3B ownership retained.

## 29 October 2026 — M13 complete-period contiguous BIDI

**New source:** `DASHI/Arithmetic/TwinPrimeMangoldtFinIntervalReindexExact.agda`.
Owner: #1408. It imports the ORIGINAL finite-sum, exact Nat
period BIDI, and `Fin270` row owners, without recreating
their carriers. The source supplies:
`intervalFinSum`, `intervalFinSumExact`
(any start/count and any additive scalar, using indexwise
congruence, **no scalar commutativity axiom**),
`periodRowIsContiguousInterval`, and
`periodCorrelationToContiguous` /
`contiguousToPeriodCorrelation` for every period.
Therefore the ordered sum over 270 finite residual codes is
the identical ordered arithmetic correlation sum over
[270k,270k+270), not a numeric-rank analogy.

**Actually executed local Python:** 55 complete period rows,
80 arbitrary boundary-spanning interval partitions, 14,850
pairwise Nat <-> period/residue witness pairs: PASS.
These tests do not certify Agda typing or an analytic lower bound.

**Next concrete M13 cuts:** prove a general prefix/suffix partial
period row is an ordered interval with exact bounds, then
prove concatenation of rows via explicit additive associativity
(or construct a common index fold with matching evaluation order)
and arbitrary interval partition across period boundaries.
Once M13 is fully complete, M14 proper-prime-power accounting,
M15 finite upper bound and M16 conditional positive-correlation
implication remain. F02/F04/F06 still need genuinely new
unconditional number theory; neither finite CRT nor S3/C2
orbit equivalence supplies it. Avoid Monster same-object
promotion and keep prior Ibrahim 3B ownership.
**Source-written, kernel pending. No CI or ESD edits.**

## 29 October 2026 — multi-period finite-sum max-cut (M13)

**New source owner:** `DASHI/Arithmetic/TwinPrimeMangoldtMultiPeriodConcatExact.agda`.
Reuses the pre-existing scalar fold, pointwise Mangoldt residual BIDI and
Fin270 period-row owners. The explicitly supplied `MonoidSum` requires
only left identity and associativity of addition; it assumes neither
scalar commutativity nor analytic positivity. `sumIntervalSplit`
proves concatenation of any two ordered finite intervals; 
`blockRowsCorrect` inducts over any number of complete 270-element
blocks, beginning at any Nat start index. `codeBlockRows` defines
the coded multi-period correlation sum. Its BIDI correctness is
**not yet proved**, nor is arbitrary partial-row partition.

**Executed independent local Python:** 42 comparisons over 0..5 complete
blocks and 7 starting offsets; all full ordered sequences matched.
This is computational testing only; Agda kernel and CI not run.
All 3 TOE roots import the module. No ESD files touched.

**Next highest-value proof cuts:** establish `codeBlockRows` to
`blockRows` via the true `periodIndex` step arithmetic;
prove prefix/suffix partial-row assembly and arbitrary interval
partition (M13); then prime-power exceptional terms and bounds
(M14/M15), followed by conditional inference M16. Open research
F02/F04/F06 remains **unconditional gap-two correlation**, which
cannot be supplied by any quotient, finite-sieve count, or matching
Ibrahim/Monster fingerprint. Attribution: original residual and
Conway/Guy source owners retained; bounded-gap input credits
Zhang/Maynard/Polymath, and any unrefereed 2026 bounds retain
their conditional/unverified scope.

## 30 October 2026 — highest-alpha max-cut: actual Mangoldt + entire coded block + partial interval BIDI

**Repository-first audit performed (NOT only PR names):**

- Agda on `master`: opened `DASHI/Analysis/WeilTestSpace.agda`, `RiemannVonMangoldtSpecification.agda`, `RiemannPrimePowerCounting.agda`, `RiemannPrimePowerMangoldtIdentity.agda`, `RiemannPrimeExhaustion.agda`, `WeightedValuationVonMangoldtBoundary.agda`, `DASHI/Core/ParetoSymmetryQuotientAdmissionExact.agda`, `DASHI/Core/SnowballAttributionProvenanceInvariantExact.agda`, `DASHI/Wikimedia/IbrahimSnowballParetoFrontierExact.agda` and `IbrahimEnglishHighFlowQidBindingsExact.agda`.
- Agda on #1408: opened actual current `TwinPrimeNat270PeriodResidualBidiExact.agda`, `TwinPrimeResidualMangoldtFiniteSumBidiExact.agda`, and `TwinPrimeMangoldtMultiPeriodConcatExact.agda`. Checked #1244/#1275/#1414 recent heads for separate source ownership; did not pretend those other branches had been merged.
- Lean on `chboishabba/dashi_lean4` `main`: opened `README.md`, `docs/DECLARATION_LANDSCAPE.md`, `Main.lean`, `DashiPerf.lean`. It records a narrow current checked-in Lean declaration map, and much larger candidate *bundles that have not been materialized*; there is no checked-in Lean proof of the required gap-two estimate in this inventory.
- `chboishabba/agda2lean` `main`: opened `README.md` and `lean-toolchain` (Lean 4.28), verified that elaboration snapshot / strict IR / Lean reconstruction is a translation pipeline, **not** independent proof of an unresolved source claim.
- Checked recent commit search in all three repositories. `QID` bindings are external identity metadata, **not** mathematical proof authority. Pareto geometric symmetry is *not* admitted without semantic consumer preservation; Snowball retention does *not* prove arithmetic positivity. Original Ibrahim 3B ownership remains separate.

**This turn's actual new / extended source-written Agda:**

1. `TwinPrimeMangoldtMultiPeriodConcatExact.agda` now additionally proves `codeBlockRowsCorrect`, `codeBlockRowsToInterval`, `intervalToCodeBlockRows`: ANY period index and ANY number of full 270-block rows; original finite-fold owner; additive associativity required only for contiguous regrouping; no scalar commutativity.
2. `TwinPrimeMangoldtPartialPeriodPartitionExact.agda`: `partialPeriodPartition` and reverse `partialPeriodPartitionBidi`. For **any** start / prefix / period / number of full rows / suffix with witnessed `start + prefix = 270*period`, the exact contiguous correlation sum agrees with the prefix + coded full blocks + suffix; original ordering unchanged. No claim that witness is automatically constructed for every start yet.
3. `TwinPrimeMangoldtActualPrimePowerResidualExact.agda`: `actualMangoldtPair` uses ORIGINAL `VonMangoldtFunction.lambda` and `AllPrimeArithmetic._*S_`, `actualPairPeriodBidi` and reverse; `mangoldtPrimePowerPeriod` uses ORIGINAL `lambdaAtPrimePower`; `occurrenceMangoldtPeriod` uses ORIGINAL `PrimePowerOccurrence`; `actualPairAtPrimePower` transports precisely `Lambda(p^(k+1))=log p`, NOT k*log p. This is the exact M14 prime-power **weight** prerequisite; not the proper-prime-power counting/bounding theorem.
4. `TwinPrimeWeilActualCorrelationPartitionExact.agda`: reuses ORIGINAL `WeilTestSpace` scalar, constructs `weilAdditive`, requires `WeilAdditiveLaws` (`leftZero` and `addAssociative`) **because those laws are absent from the original WeilTestSpace record**, and assembles `realMangoldtPartialPeriodBidi`. The supplied analytic model and laws are still explicit parameters, not generated automatically by an alias.

All four modules are imported in `EverythingTOESymmetryResolved369`, `Unifier`, `Unified/Everything`; no ESD changes.

**Actually executed local Python, not Agda:** 1,280 aligned partial/full-period interval identities; 183 exact **symbolic** `log(p)log(q)` monomial-Counter correlation equalities; 20,250 `Nat ↔ (period,residue)` checks; 59/209 and 59/329 no-go; plus 66 `Lambda(p^k)=log p` prime-power instances. **PASS**. The committed regression harness is `scripts/check_twin_prime_mangoldt_partial_period_exact.py`. Local `agda`, `lean`, `lake` executables unavailable; NO kernel receipt and no CI claim.

**Remaining truthful proof cut (do not mark solved):**

- M13-all: construct the alignment witness algorithm for *every* `start, count`, prove the residual prefix/suffix bounds, and connect it with the source-written partial-period theorem. Source-written sum identities still require Agda kernel check.
- M11: supply a genuinely instantiated `AllPrimeArithmetic`/`VonMangoldtFunction` from the existing proof-bearing Nat prime calculus and a concrete Weil scalar with proved `WeilAdditiveLaws`, rather than a hypothetical parameter.
- M14/M15: actual classifier/count of **proper prime powers** (k>=2) and certified uniform upper bound on their total pair-correlation contribution; the existing Riemann counting/finite enumeration owner is prior art and source of types. Do not confuse the weighted-valuation energy `p*v_p(n)` with classical von Mangoldt.
- M16: prove the *conditional* lemma turning an independent genuine `sum Lambda(n)Lambda(n+2) >= cX` estimate, after M14/M15 errors, into certified unbounded twin pairs.
- F02/F04/F06/G01: the **unconditional** analytic positive gap-two correlation remains an unsolved mathematical problem. Neither finite CRT, 3^5 vs 5^3, orbit matching, Monster fingerprint, nor a proof-carrying encoder discharges it.

**Relevant external prior-art verification, not a proof import:**
Stadlmann, *Bounded gaps between primes*, arXiv:2608.31126 (2026);
Song & Yue, *Bounded Gaps Between Primes: An Upper Bound of 236*, SSRN 7408198 (September 2026);
Teorth bounded-prime-gap record https://teorth.github.io/optimizationproblems/constants/88a.html (reported H1<=186, distinct from established/peer-reviewed);
Wang, *Why expansion methods for Chowla do not reach twin primes*, Zenodo 23694711, 27 Oct 2026 (method-limitation **report**, not a twin-prime result).
Preserve original Conway/Guy, Zhang/Maynard/Polymath, original Agda/Lean and Ibrahim proof/source ownership. QID = source identity only. No claim of kernel certification, independent analytic verification or a solution to twin primes.

## 30 October 2026 — highest-alpha follow-on: M14 support, M16 certified count and source-checked reuse

**Concrete repo inspection, not just PR titles.** GitHub source fetched from
`dashi_agda` (#1408 and `master`):
`TwinPrimeNat270PeriodResidualBidiExact.agda`,
`TwinPrimeMangoldtMultiPeriodConcatExact.agda`,
`TwinPrimeMangoldtActualPrimePowerResidualExact.agda`,
`TwinPrimeMangoldtFinIntervalReindexExact.agda`,
`TwinPrimeResidualMangoldtBidiExact.agda`,
`RiemannVonMangoldtSpecification.agda`,
`RiemannPrimePowerCounting.agda`,
`RiemannPrimePowerMangoldtIdentity.agda`,
`ChebyshevPrimeCounting.agda`,
`RiemannVonMangoldtPrimeSide.agda`,
`TwinPrimeCertifiedEnumeratorExact.agda`,
`PrimeCountingFunction.agda`, and `TwinPrimeSixWheelExact.agda`.
Inspected `dashi_lean4` actual `MoonshineFractran.lean`,
`Main.lean`, `DashiPerf.lean`,
`docs/DECLARATION_LANDSCAPE.md`; and `agda2lean` README and
`lean-toolchain`. The checked-in Lean FRACTRAN material covers
finite SSP counters/equalities, **not** a proved twin-prime gap-two estimate.
The translator is not a kernel proof by itself. Rechecked #1408, #1244,
#1275, #1414 heads; #1244/#1414 have newer independent heads and
must not be treated as merged owner branches.

**New or fixed code on #1408** (all source-written, kernel pending):

1. `TwinPrimeMangoldtMultiPeriodConcatExact.agda`: removed duplicate
   `Data.Nat.Properties` import detected in the actual branch source.
2. `TwinPrimeMangoldtPrimePowerPairBothSidesExact.agda`:
   `ProperPrimePowerOccurrence` distinguishes exponent >=2 from
   prime exponent 1; `properPowerMangoldtPeriod`,
   `rightPrimePowerWeight`, `bothPrimePowerWeights`,
   `bothPrimePowerPeriodBidi` reuse the original
   `lambdaAtPrimePower` and proof-bearing occurrence type.
   The identity is `Lambda(p^k)=log(p)`, NOT k log(p).
3. `TwinPrimeMangoldtOutsidePrimePowersZeroExact.agda`:
   `OutsideAllPrimePowers`, `mangoldtZeroOutside`
   use the original relational `outsidePrimePowers` and
   `specificationSingleValued`; `leftOutsidePairZero` and
   `rightOutsidePairZero` plus exact period transport require
   explicit `ProductZeroLaws`. These laws are **not** auto-entailed
   by an arbitrary Weil space or claimed as new analytic results.
4. `TwinPrimeMangoldtCertifiedIntervalScheduleExact.agda`:
   `CertifiedIntervalSchedule` requires exact first-boundary
   alignment and total-length equality.
   `scheduleCorrelationForward`/`Backward` compose existing
   ordered partial/full period proofs. `boundaryIntervalSchedule`
   and `wholeRowsSchedule` are actual constructed instances.
   The arbitrary nonaligned `start,count` schedule constructor
   remains an OPEN obligation, distinct from this conditional BIDI.
5. `TwinPrimeCertifiedCountJumpBidiExact.agda`: genuinely reuses
   `TwinPrimeCertifiedEnumeratorExact` and original proof-bearing
   `PrimeCountingFunction.primeCountAtPrime` /
   `primeCountAtNonprime`. Proves
   `TwinPrimeAt (k+2) ↔ count(k+2) ≢ count(k+1)`
   as a structured two-sided criterion over all k >=0.
   It is NOT the wheel-survivor count.
6. `TwinPrimeConditionalUnboundedFromCountJumpsExact.agda`:
   final `∀N ∃p≥N, TwinPrimeAt p` follows by an exact constructive
   map **only after** supplying an explicit
   `UnboundedCertifiedCountJumps.laterJump` assumption.
   This assumption is mathematically equivalent in strength to the
   remaining infinitude gate and is NOT discharged here.
7. `TwinPrimeCertifiedNatPeriodWitnessBidiExact.agda`:
   original `TwinPrimeAt` certificates move between
   `Σ Nat TwinPrimeAt` and
   `Σ NatPeriod270 (TwinPrimeAt ∘ decode)`.
   Both underlying Nat/period-code round trips are proved via
   existing codec inverse lemmas; no proof-irrelevance or promotion
   of Ibrahim/sign-orbit class to a primality oracle.

All six new modules are imported through
`EverythingTOESymmetryResolved369`, `Unifier` and
`Unified/Everything`, without ESD edits.

**Independent local Python actually executed:**
- 1,260 prefix + 0..4 whole rows + suffix interval index checks;
  252 exact symbolic `log(p)log(q)` paired-weight sum comparisons;
  30,000 Nat/period inverse checks; 66 powers `p^k` checks: PASS.
- 25,000 independent pair-support comparisons using two different
  prime-power algorithms; 66 proper-power checks; 59/209 and
  59/329 distinction: PASS. `scripts/check_twin_prime_mangoldt_support_bidi.py`.
- 70,001 original certified twin-count step comparisons (sieve
  vs independent trial division): PASS, with 905 finite jump indices.
  `scripts/check_twin_prime_count_jump_bidi.py`.
These finite tests are not proof-assistant checks and do not imply
infinitude. An executable local `agda` or `lean` is unavailable;
CI was not run by request. Static new-module scan found no
`postulate` declarations or `?` holes; this is not a kernel receipt.

**Updated outstanding max-cut ledger:**

- **M11 (partial):** concretely instantiate original all-prime
  `VonMangoldtFunction`, proof-bearing Nat prime arithmetic
  and `WeilAdditiveLaws`; scalar laws are explicit dependencies.
- **M13 (partial):** for arbitrary unaligned `start,count`,
  construct `CertifiedIntervalSchedule` with first-boundary
  distance, all whole rows, suffix and two arithmetic equalities.
  Existing guarded BIDI must then be kernel-checked.
- **M14 (partial):** exact left/right prime-power and outside-support
  term identities are written. Missing global proper-prime-power
  occurrence classification, multiplicity handling, prime-only
  extraction and full finite-sum accounting.
- **M15 (open):** prove a uniform proper-power *weighted pair*
  bound; note the standard O(sqrt X log^2 X) scale needs a
  genuinely specified analytic scalar and a proof, not Python.
- **M16 (partial):** certified count-jump BIDI and explicit
  conditional unbounded implication written; an analytic
  correlation-to-count-growth theorem requires M14/M15.
- **F02/F04/F06/G01 (OPEN):** unconditional gap-two prime-pair
  correlation and parity barrier. As of 30 October 2026 current
  reported H1 bounds are still greater than 2; these reports do
  not constitute a twin-prime proof.
- **G06 (OPEN):** complete exact-head Agda kernel check; no CI
  substitute claimed.

**Provenance and semantic boundary:** Classical von Mangoldt,
Riemann, Brun, Hardy–Littlewood, Zhang, Maynard/Tao, Polymath and
the original Agda/Lean source owners retain their dated contributions.
`ParetoSymmetryQuotientAdmissionExact` requires eligibility/objective
preservation before quotienting; `SnowballAttributionProvenanceInvariantExact`
preserves source role; Ibrahim `IbrahimSnowballParetoFrontierExact`
is a separate historically attributed dataset-genealogy programme;
QIDs identify entities but do not confer kernel proof. No new
Monster 3B same-object representation is asserted. No ESD edits.

## 30 October 2026 — M13 semantic correction: short intervals versus boundary-crossing intervals

A **mathematical flaw in the previous proposed cut** was identified:
`CertifiedIntervalSchedule start count` requires
`start + prefixLength = firstWholePeriod*270` together with
`count = prefixLength + blocks*270 + suffixLength`.
For a short non-boundary interval, e.g. `start=59, count=1`,
this schedule cannot exist. No amount of Agda proof search could
construct it for all `start,count`. The correct arbitrary interval
split has **two constructors**:

1. **within one 270-period**:
   `start%270 + count ≤ 270`, use the already existing
   `pairFiniteSumBidiBackward` for the exact lossless
   Nat→period-code finite fold;
2. **crosses a period boundary**: pass the already defined,
   proof-bearing `CertifiedIntervalSchedule` to
   `scheduleCorrelationForward`/`Backward` and retain the
   exact prefix + whole 270-blocks + suffix semantics.

**Implemented** the repaired typed interface, forward/backward
transport as
`DASHI/Arithmetic/TwinPrimeMangoldtTwoCaseIntervalPlanExact.agda`.
Updated the original `TwinPrimeMangoldtCertifiedIntervalScheduleExact`
header to reject the impossible universal aligned-only claim.
This uses the original `NatPeriod270` code; 270 residue positions
are **not** misidentified with the 27 sieve survivors or with
Ibrahim 15/global antipodal 14 quotient classes.

**Actually executed local Python**: 3,010 interval plans,
335 within-period and 2,675 crossing-boundary; 274 exact
symbolic `log(p)log(q)` correlation comparisons, all PASS.
Explicit edge cases include [59,60), [269,270),
[269,271), [270,270), [270,541), and [329,330).
Checker committed at
`scripts/check_twin_prime_m13_two_case_plan.py`.

**NEXT M13 theorem:** constructive
`completePlan : (start count : Nat) →
 CompleteIntervalPlan start count` using division/remainder,
a decidable within-period inequality, and in the crossing
branch the correctly bounded prefix, period count and suffix
with *both* equality witnesses. This is now a logically valid
total-constructor target; still source-open, not kernel-checked.
No unproved positivity imported.

**Actual independent-PR source inspections, not just heads:**
- #1244 `AlexanderHornedS3SignQuotientSetoidBidiExact.agda`
  proves a distinct C3/S3 word-action setoid quotient. It cannot
  replace the lossless Nat/Fin270 period residual required by
  primality.
- #1275 `ZipfThreeDrawEqualityPatternFactorExact.agda`
  has a source-written 27-code → 5 equality-pattern map for
  observation/Heaps histories, not a prime-pair classifier.
- #1414 `PolynomialC3S3TwentySevenOrbitRefinementExact.agda`
  states a 27-endomorphism conjugation (7 S3 orbits);
  `PolynomialIbrahimParetoSnowballMaxCutExact.agda` explicitly
  blocks numerical analogy from creating same-object/Monster
  proof authority. This is valuable *admission logic*, not a
  substitute for analytic gap-two correlation.
- Prior source `DASHI/Core/ParetoSymmetryQuotientAdmissionExact`
  requires declared semantic objective and eligibility
  preservation before quotienting. Original Ibrahim QID bindings
  retain entity identity only, not theorem or kernel authority.

All M13 additions are imported through the three target TOE roots.
No protected ESD files changed. No Agda kernel or CI receipt.
External sources still distinguish Polymath/Maynard bounded
gaps from the open H1=2 twin-prime conjecture.

## 30 October 2026 — M13 TOTAL construction source-written, kernel pending

**Implemented the next previously open mathematical source cut**
`DASHI/Arithmetic/TwinPrimeMangoldtTotalIntervalPlanExact.agda`.

- `distanceToBoundary`: `270 ∸ (start %270)`;
  at exact boundaries this is 270, consistent with the
  within-period branch of the corrected two-case plan.
- `residueIsAtMost270`, `residueCompletes270`:
  reuses `m%n<n`, `n≤1+n`, `m∸n+n≡m`.
- `firstBoundaryExactForAnyStart`:
  reuses `m≡m%n+[m/n]*n` and elementary Nat
  associativity/commutativity to prove
  `start + distanceToBoundary start
      = (suc (start/270))*270`.
- `plusLeftMonotone` and `shortWhenWithinDistance`:
  translate the count bound into the exact
  `start%270+count ≤270` within-period witness.
- `mustCrossBoundary`: reuses the existing
  `NP.≤-total` and a contradiction with the failed
  `_≤?_` test, proving the prefix fits inside the count.
- `splitCountAtBoundary`: decomposes the remaining
  count with the original Euclidean identity, obtaining
  `count=prefix+blocks*270+suffix`.
- `completeIntervalPlan`: **total** source-written
  construction of `CompleteIntervalPlan start count`,
  using `NP._≤?_` and actual certified equality
  witnesses in the crossing branch.
- `totalIntervalCorrelationForward` and
  `totalIntervalCorrelationBackward`: for ALL Nat
  start/count, exact original correlation fold ↔
  automatically constructed lossless plan, with no
  additive commutativity assumption or prime heuristic.

This **supersedes the earlier claim** that a single aligned
schedule could be constructed for every interval: that type
was impossible for short nonboundary intervals. The new
two-case plan + total constructor fixes the problem at
the interface level. The earlier conditional aligned schedule
remains useful internally.

**Numerical sanity evidence actually executed:**
3,010 total plans, 335 within and 2,675 crossing,
274 exact symbolic Mangoldt-pair comparisons,
including [59,60), [269,270) and boundary-spanning
intervals. Separately, 70,001 exact certified count-jump
checks and 25,000 paired Mangoldt support checks passed.
Scripts are committed in the PR.

**Scope:** M13 is now **source-written for arbitrary finite
intervals, still Agda-kernel-pending**. All three canonical
TOE roots import the total module. Agda compiler/CI was
not run. Strictly no ESD edits, postulate-based
positivity or Monster/3B numerical identification.

**Remaining highest-alpha proof cuts:** exact Agda typecheck
of M13 (including stdlib normalization of Fin270/
division lemmas), concrete Weil/AllPrimeArithmetic model,
M14 proof-bearing prime-power count and extraction,
M15 uniform proper-power weighted error bound,
M16 **correlation-to-real certified count jumps**,
F02/F04/F06 unconditional analytic gap-two estimate,
G06 full safe kernel proof. Do not mark twin infinitude
unconditional from the conditional count-jump field.

## 30 October 2026 — M14 exhaustive actual Mangoldt support + proper-power gap-two no-go

**Source-written, kernel-pending:** 
`DASHI/Arithmetic/TwinPrimeMangoldtExhaustiveSupportCaseExact.agda`.

- Import and case-split `RiemannVonMangoldtSpecification.VonMangoldtAt`
  through `VonMangoldtFunction.lambdaSpecified` directly.
- `MangoldtSupportCase` has three **exhaustive** alternatives:
  `exponentOne` with original n=p^1 witness,
  `exponentAtLeastTwo` with original n=p^(k+2) witness,
  `noPrimePower` with original excluded-all-prime-powers witness.
- `mangoldtValueAtExponentOne`,
  `mangoldtValueAtProperPower`,
  `mangoldtValueOutside` reuse the ORIGINAL
  `specificationSingleValued` and constructors to preserve
  exact Weil scalar weights `log p, log p, 0`.
- `BothEndpointsClassified` and `allPairSupportCases`
  provide every logical 3×3 pair-support case for
  (n,n+2). This is a classification of **support**,
  not an identification with the 3×3×3 SSP geometry.

**Explicit soundness counterexample:**
`DASHI/Arithmetic/TwinPrimeMangoldtProperPower25_27NoGoExact.agda`
reuses `RiemannPrimePowerArithmetic.natPow`,
`FiniteTwinSieveFactorableLiftExact.TwoNontrivialFactors`,
`Data.Nat.Primality.Composite` and the genuine
`TwinPrimeSixWheelExact.TwinPrimeAt`.
It records `25=5²`, `27=3³`,
`25+2=27`, proves actual 25/27 composite
certificates and refutes `TwinPrimeAt 25`.
Hence even **both** endpoints being proper prime powers
at gap two cannot establish genuine twin primality.
A separate analytic scalar with positive log weights
would be needed to formally state nonzero Mangoldt
product; this module does not invent it.

**Actually executed local Python:** 100,000 consecutive
paired-support classifications, all 9 combinations
observed including `(proper,proper)`, PASS.
Committed `scripts/check_twin_prime_mangoldt_support_nine_cases.py`.
Prior 3,010 total two-case M13 interval checks and
70,001 true certified count-jump checks also PASS.
All are finite model evidence, NOT Agda kernel receipts.

**Status adjustment:** M14 exhaustive support classification and
term-weight identities are now source-written. **OPEN**
is finite-count multiplicity, extraction of only true prime/prime
contributions, and the uniform proper-power weighted
pair-error estimate M15. M16 remains conditional on a
genuinely new positive correlation-to-count-jump theorem.
F02/F04/F06/G01 remain mathematically OPEN;
do NOT label this a proof of twin-prime infinitude.
All new modules are imported into all three TOE roots.

**Highest-alpha finite next cut:** kernel-check the complete
M13 source chain, then prove the finite weighted pair
decomposition by the 3×3 cases, with explicit zero-product
and addition laws; prove elementary proper-power counting
and logarithmic error bounds. **Research next cut:**
an unconditional gap-two correlation estimate overcoming
the sieve parity barrier. QIDs remain identification metadata,
Ibrahim Monster 3B ownership unchanged, original Pareto
semantic-admission and Snowball provenance controls preserved.
No protected ESD edits and no CI claimed.

## 30 October 2026 — source-audited M13 × M14 max-cut: exact classified finite sums, true prime-one BIDI, retained error

### Repository and external state checked in THIS continuation

Actual Agda source read on #1408 (not only PR titles):
`TwinPrimeMangoldtMultiPeriodConcatExact.agda`,
`TwinPrimeMangoldtCertifiedIntervalScheduleExact.agda`,
`TwinPrimeMangoldtTotalIntervalPlanExact.agda`,
`TwinPrimeMangoldtExhaustiveSupportCaseExact.agda`,
`TwinPrimeMangoldtProperPower25_27NoGoExact.agda`,
`FiniteTwinSieveFactorableLiftExact.agda`,
`TwinPrimeCertifiedEnumeratorExact.agda`.
Existing original owners on `master` read:
`RiemannVonMangoldtSpecification.agda`,
`ChebyshevPrimeCounting.agda`,
`NatPrimeCountingInstance.agda`,
`PrimeCountingFunction.agda`,
`RiemannPrimePowerCounting.agda`,
`ParetoSymmetryQuotientAdmissionExact.agda`,
`SnowballAttributionProvenanceInvariantExact.agda`,
`IbrahimEnglishHighFlowQidBindingsExact.agda`.
Distinct PR-source material read:
#1244 `AlexanderHornedS3SignQuotientSetoidBidiExact.agda`,
#1275 `ZipfThreeDrawEqualityPatternFactorExact.agda`,
#1414 `PolynomialIbrahimParetoSnowballMaxCutExact.agda`.
Latest heads observed: #1408 `4b36f817...` at session start;
#1244 `4b9ef09e...`, #1275 `bca5fb61...`,
#1414 `51860893...`. These independent PRs were NOT merged.
Lean actual source read:
`dashi_lean4/MoonshineFractran.lean` (finite SSP state and arithmetic
equalities), `dashi_lean4/docs/DECLARATION_LANDSCAPE.md` (actual
checked-in declarations distinct from candidate bundles);
`agda2lean/README.md` (typed Core IR/CBOR/Lean reconstruction).
No Lean proof of unconditional gap-two correlation was found in
these checked surfaces.

Current external primary references:
Julia Stadlmann (arXiv:2608.31126, 2026) H1<=240;
Song & Yue (SSRN 7408198, 2026) claim H1<=236;
OpenAI (2026) reports H1<=186 but its Lean receipt explicitly has
unpaid analytic/numeric assumptions. They are *bounded gaps*, NOT gap 2.
A 2026-10-27 Laporta upload titled a claim of the full conjecture
(arXiv 2006.04547) is an **unverified research claim**, not usable
as a proved lemma merely because an abstract says "true".
No source claim is promoted to kernel authority or identified
as a same-object Monster/Ibrahim theorem.

### Concrete code and paydown (all SOURCE-WRITTEN / kernel PENDING)

1. Repaired `TwinPrimeMangoldtMultiPeriodConcatExact.sumIntervalSplit`
   zero-length base case with `Data.Nat.Properties.+-identityʳ`.
   The previous base case failed to explicitly transport the
   variable-index `start+0` to `start` under the finite fold.
2. `TwinPrimeMangoldtClassifiedFiniteSumExact.agda`:
   `supportWeight`, `supportWeightCorrect`,
   `pairSupportWeight`, `classifiedPairWeightExact`,
   `classifiedPairPeriodExact`,
   `finiteCorrelationClassifiedExact`.
   These reuse the ORIGINAL `VonMangoldtAt` cases and
   exact `specificationSingleValued`; EVERY finite
   actual lambda-pair sum is equal to its classified sum
   with zero additive commutativity assumptions.
3. `TwinPrimeMangoldtPrimeOneCertifiedBidiExact.agda`:
   imports the ORIGINAL `ChebyshevPrimeOwnership`
   and `NatPrimeCountingInstance.natPrimePredicate`.
   `primeOnePairToTwin` and `twinToPrimeOnePair`
   transport actual `NatPrimality.Prime n` certificates
   both directions using `p^1=p` and the owned
   `primeToCarrier` / `carrierIsPrime` maps.
   `PrimeOneTwinBidi` is a logical BIDI, NOT
   equality of dependent proof objects.
4. `TwinPrimeMangoldtPrimeErrorFiniteSplitExact.agda`:
   nine explicit case proofs `pairCaseSplit`;
   `classifiedPointwiseSplit`; all-length ordered
   `finiteSumPointwiseSplit`; `finiteMangoldtPrimeErrorSplit`.
   Original lambda-pair sum is EXACTLY the sum over
   exponent-one/exponent-one terms PLUS all remaining terms.
   `AdditiveInterchangeLaws` supplies unit and
   commutative regrouping as **EXPLICIT additional scalar
   assumptions**. No fake monoid/Weil laws.
   **Semantic correction:** `AllPrimeArithmetic.Prime`
   is an arbitrary carrier unless the ORIGINAL
   `ChebyshevPrimeOwnership` bridge is supplied.
   The unguarded `primeOnlyAtNat` is therefore a
   carrier-exponent-one *candidate* sum, not automatically
   genuine `NatPrime` evidence.
5. `TwinPrimeMangoldtFiniteErrorPeriodBidiExact.agda`
   composes M13 total arbitrary interval code with M14
   finite prime/error split in BOTH directions:
   `finiteCodedPeriodToPrimeError`,
   `finitePrimeErrorToCodedPeriod`.
   The **admitted** `finiteCodedPeriodToCertifiedPrimeError`
   explicitly also requires `ChebyshevPrimeOwnership`,
   and `primeOneOwnerBidi` witnesses that owner.
   This is an exact finite certificate-preserving interface,
   NOT a twin-prime count growth theorem.
6. Each of the three canonical TOE roots now imports the
   four new modules once; pre-existing duplicated
   `TwinPrimeMangoldtActualPrimePowerResidualExact` imports
   were removed without editing ESD.
7. Independent Python regression oracle committed:
   `scripts/check_twin_prime_m14_prime_error_split.py`.
   The Python interpreter was ACTUALLY RUN locally:
   15,002 independent support classifications;
   606 exact symbolic M14 finite intervals;
   15,000 actual prime-one/twin case comparisons;
   30,000 pair classifications;
   706 exact symbolic whole=prime+error intervals;
   all PASS, including (25,27) as prime-power ERROR,
   (59,61) as a genuine twin pair, and all nine
   support category pairings. Symbolic monomials
   are formal `log(p)*log(q)` tokens and imply NO analytic estimates.
   Existing local 3,010 M13 interval tests,
   25,000 support tests, 70,001 count-jump checks,
   and 30,000 Nat-period checks also ran PASS.
8. Static checks / imports / absence of `postulate`
   do NOT establish successful Agda kernel elaboration.
   The local container has no executable `agda` or `lean`.
   No CI was run by explicit user instruction.

### Updated max-cut frontier (highest-alpha)

- **M13:** exact all-Nat interval reindexing and count decomposition
  source-written; actual Agda typecheck remains an unpaid gate.
- **M14:** full original 3×3 source-support algebra, classified
  finite correlation, exponent-one NatPrime certificate BIDI
  *under genuine ownership*, and explicit retained proper-power
  error source-written. Still need proof-bearing finite
  multiplicity/no-duplicate classification and concrete total
  instantiated `AllPrimeArithmetic`/Weil analytic scalar.
- **M15:** a UNIFORM positive/ordered scalar bound for
  `nonPrimeErrorAtNat` remains OPEN; an elementary bound
  on the count of proper powers must be paired with
  explicit growth bounds on logarithmic weights.
- **M16:** formal conditional implication from
  positive gap-two `sum Λ(n)Λ(n+2)` to genuine NatPrime
  pair count growth remains OPEN. Existing
  `UnboundedCertifiedCountJumps` is an ASSUMPTION,
  not proof of its own existence.
- **F02/F04/F06/G01:** unconditional positive prime-pair
  correlation and the parity obstruction are mathematically
  OPEN; QIDs, Pareto search rankings, C3/S3 matching
  orbit sizes, or historical Ibrahim/Monster fingerprints
  do NOT discharge them.
- **G06:** exact-head Agda kernel verification, with
  `--safe`, zero postulates/metas and no artificial
  termination escapes, remains OPEN.

Provenance: original von Mangoldt/Riemann, Brun (1919),
Hardy–Littlewood (1923), Zhang (2013/14),
Maynard/Tao/Polymath (2013–14); original DASHI
Agda/Lean proof owners; independently owned Ibrahim
3B and Snowball/QID references retained. The
finite classification identities are DASHI-specific
new source-written adapters, not falsely attributed
as the historical source authors' formalised proofs.

### 30 October 2026 — primary-source correction of a misleading purported solution

The preceding paragraph describing Laporta `arXiv:2006.04547`
as an "unverified research claim" is strictly strengthened by
the **current primary arXiv record**, checked on 30 October 2026:
https://arxiv.org/abs/2006.04547 records **withdrawn**
(last revised 27 October 2026), with the author's explicit
comment **"Lemma 2 is false"**. This is NOT a candidate analytic
ingredient, and neither the original title nor secondary arXiv
mirrors may override its current withdrawn status. No
F02/F04/F06/G01 promotion is justified.

## 30 October 2026 — further M16 constructive closure from nonzero prime-only finite sums

Source written (kernel pending):
`DASHI/Arithmetic/TwinPrimeMangoldtNonzeroPrimeSumWitnessExact.agda`.

This module REUSES `TwinPrimeCertifiedEnumeratorExact.twinPrimeAt?`,
`ChebyshevPrimeOwnership`, `NatPrimeCountingInstance`,
`TwinPrimeMangoldtPrimeOneCertifiedBidiExact`,
the prior `exponentOne` vs proper-power support split,
and the explicitly supplied `AdditiveInterchangeLaws.zeroLeft`.
It introduces the constructive indexed finite certificates
`TwinInInterval` and `NoTwinInInterval`, and proves:

- `finiteTwinSearch`: a complete finite decision BIDI
  returns a genuine Nat-primality twin witness or
  a proof that the entire bounded interval contains none.
- `primeOnlyWeightZeroIfNotTwin`: all 9 source support
  cases analysed; the exponent-one/exponent-one case is
  ruled out by the ORIGINAL `ChebyshevPrimeOwnership`
  and `primeOnePairToTwin` if no twin exists.
- `primeOnlySumZeroWithoutTwins`: finite sum
  is zero on a certificate-free interval, by recursion
  with the explicit additive left-zero law.
- `nonzeroPrimeOnlySumGivesTwin`: if an interval's
  actual **certified** prime-only sum is not equal to zero,
  return a genuine `TwinInInterval` witness.
- `twinInIntervalReadout`: extract its exact Nat magnitude,
  lower-bound index, and two standard NatPrime certificates.
- `twinUnboundedFromUnboundedNonzeroPrimeSums`:
  `∀N∃p≥N TwinPrimeAt p` is obtained **CONDITIONALLY**
  from a separately supplied window-length function and
  a proof that the certified prime-only sum never vanishes
  on each such future window. This premise is the unpaid
  **twin-prime-infinite arithmetic/analytic gate**. It is
  NOT proved by the finite-sum transport or the 27-wheel.

**Actually executed local Python:** the independently written
`check_m16_nonzero_prime_sum.py` checked 2,206 finite windows;
534 zero/non-witness cases and 1,672 nonzero/witness cases:
PASS. The committed corresponding regression is
`scripts/check_twin_prime_m16_nonzero_prime_sum.py`.
No claims of infinite nonzero windows, Agda kernel verification,
new positive correlation, or safe full-build closure.

**Full remaining analytic join:**
(1) certify the original Weil scalar as an ordered analytic ring
with additive and multiplicative positivity and the needed
positive log-prime weights;
(2) prove a uniform M15 upper bound on the retained proper-power
pair error (including multiplicity and window boundaries);
(3) prove a new lower bound on the ORIGINAL gap-two lambda correlation
strong enough to force prime-only sum nonzero beyond the error,
then use this M16 theorem. The missing (3) is not supplied by
currently known bounded-gap results, nor by any S3/C2/Ibrahim
quotient equivalence. Check all Agda with the golden safe kernel
before claiming a theorem. No ESD edits.

## 30 October 2026 — exact FINAL critical-path obligations (research OWNED by DASHI)

**Target:** the original `TwinPrimeSixWheelExact.TwinPrimesInfinitelyOften`,
constructively `∀ N → Σ Nat (λ p → N ≤ p × TwinPrimeAt p)`.
The status below is based on actually fetching the October 30 source
of M13, M14, M16 and the original Riemann/prime-counting interfaces.
Being source-written is **not** kernel verification. This document
lists **our own proof obligations** and must not defer the mathematical
discovery to unspecified third parties.

### A. Materialization and consistency obligations (independent of novel analytic breakthrough)

| ID | Exact lemma/result we must discharge | Existing donor / present state |
| --- | --- | --- |
| CT01 | `SafeAgdaClosure`: import-closed `{-# OPTIONS --safe #-}`, no postulates, holes or termination escapes; all newly added modules and TOE roots typecheck at pinned stdlib | Source-written, **not checked**; some new modules currently lack explicit `--safe` |
| CT02 | `NatPrimeCarrierConcrete`: actual `AllPrimeArithmetic.Prime` with certified `NatPrime.Prime`, injective `toNat` and `ChebyshevPrimeOwnership` fully inhabited, no proof-object identity shortcut | `NatPrimeCountingInstance`, `ChebyshevPrimeCounting`; partial interfaces |
| CT03 | `PrimePowerUniqueBase`: for primes p,q and positive i,j, `p^i=q^j ⇒ p=q`; including uniqueness of the Mangoldt scalar value | Original `RiemannPrimePowerCounting`; not yet actual unconditional proof |
| CT04 | `PrimePowerDecidableTotal`: every Nat either witnesses a certified positive prime power or formally excludes all such powers; cannot assert `lambdaSpecified` without constructing it | `RiemannVonMangoldtSpecification.VonMangoldtAt` relational; construction open |
| CT05 | `ConcreteVonMangoldtWeil`: `WeilTestSpace`, log-prime weights, genuine multiplication, ordered scalar/additive laws, zero-annihilation, `VonMangoldtFunction.lambdaSpecified` and `specificationSingleValued` inhabited without postulates | `RiemannTrackedToVonMangoldtBridge` tracks ONLY 15 primes; `RiemannPrimeExhaustion` is parametric; real-analysis donor `NSPeriodicCanonicalRealAuthorities` has **postulates**, therefore disallowed in Golden closure |
| CT06 | `Finite270TotalBidiKernel`: full `start,count` Nat interval ↔ two-case period-plan and reverse with all code/interval identities kernel-checked | `TwinPrimeMangoldtTotalIntervalPlanExact`; source-written |
| CT07 | `FinitePrimeErrorSplitKernel`: original `Λ(n)Λ(n+2)` finite sum = sum of exponent-one pairs + retained all-other support terms, with all 9 cases and correct algebra | `TwinPrimeMangoldtPrimeErrorFiniteSplitExact`; source-written |
| CT08 | `PrimeOneActualNatPrimeBidiKernel`: two first-exponent carrier certificates ↔ two actual NatPrimality.Prime proofs at gap two | `TwinPrimeMangoldtPrimeOneCertifiedBidiExact`; source-written conditional on CT02 |
| CT09 | `FiniteNonzeroExtractsTwinKernel`: nonzero *prime-only* finite sum → `Σ p, TwinPrimeAt p` in the source interval, no new axiom | `TwinPrimeMangoldtNonzeroPrimeSumWitnessExact`; source-written conditional on CT02/CT05 |
| CT09b | `TwinInIntervalUpperBound`: upgrade the current lower-only readout to `Σ p, (start ≤ p) × (p < start+count) × TwinPrimeAt p`; the existing `twinInIntervalReadout` does NOT return the upper bound | Missing explicit proof; elementary induction on `here` / `there` and Nat arithmetic |

### B. Classical elementary M15 lemmas WE CAN PROVE, not a research-paper dependency

Let `U=2X+2` for integer `X≥2`, and let E(X) be the
exact nonnegative weighted contribution of pairs with at least
one **proper** prime power (exponent ≥2). All estimates here
refer to a REAL, ORDERED, genuinely logarithmic scalar,
not an arbitrary `WeilTestSpace.Scalar`.

| ID | Exact theorem we must formalise | Mathematical proof idea |
| --- | --- | --- |
| CT10 | `PerfectPowerExponentBound`: if `p^k≤U` with `k≥2`, then `p≤⌊√U⌋` and `k≤⌊log₂ U⌋` | Integer monotonicity; all primes ≥2 |
| CT11 | `PerfectPowerFiniteCount`: # distinct integers `n≤U` with `n=p^k, k≥2` is ≤ `⌊√U⌋⌊log₂ U⌋`; counting repeated representations gives an upper bound | Map each (p,k) to an integer; bounded union; don't require uniqueness |
| CT12 | `LogWeightUpper`: `0≤Λ(n)≤log U` for `2≤n≤U`; hence `0≤Λ(n)Λ(n+2)≤(log U)^2` for arguments within U | Basic ordered-log laws and original prime-power definition |
| CT13 | `ProperPowerPairErrorBound`: `0≤E(X)≤2⌊√U⌋⌊log₂ U⌋(log U)^2` over `X≤n<2X` | At most two shifted proper-power sets; CT11–CT12; exact support partition |
| CT14 | `ProperPowerErrorSublinear`: for every `ε>0` eventually `E(X)≤ε X` | Explicit domination `√X log³ X = o(X)`, proved in the chosen ordered real model |

The CT13 bound is deliberately conservative but is enough for
infinitude. These are **proposed exact lemmas**, not currently
kernel-verified or claimed established on #1408.

### C. NEW theorem we ourselves must discover and PROVE (parity-sensitive gap-two)

Define the original, fully instantiated von Mangoldt correlation
`S(X)=Σ_{X≤n<2X} Λ(n) Λ(n+2)`.

| ID | Exact target | Status |
| --- | --- | --- |
| CT15 | **`GapTwoMangoldtDyadicPositive`**: `∃ c>0, X₀, ∀ X≥X₀, S(X)≥cX` (stronger than necessary; alternatively `∀N∃X≥N, S(X)>E(X)` is a minimal sufficiency target) | **UNPROVED NEW MATHEMATICS**; original Hardy–Littlewood conjectural main term `2 C₂ X` is NOT a donor theorem |
| CT15a (research decomposition) | Prove an exact parity-sensitive analytic expansion `S(X)=M(X)+R(X)`, with a **proved** `M(X)≥aX`, `a>0`, and a **proved** one-sided `R(X)>-aX/2` | Only a proposed attack, NOT an existing bound or imported theorem |
| CT15b (key scientific wall) | Establish the shifted double-primality correlation/cancellation estimate required for the `R(X)` bound; existing BV/Maynard/bounded-gap results do NOT give it | **UNPROVED**; explicitly test putative refinements against the parity obstruction, including the double-composite survivor construction in `FiniteTwinSieveFactorableLiftExact` |
| CT16 | `DyadicLowerBeatsProperPowerError`: CT14 + CT15 ⇒ `P(X)=S(X)-E(X)>0` for every sufficiently large dyadic window | Elementary ordered-real inequality; source open |
| CT17 | `DyadicPrimePairReadout`: CT16 + CT09 ⇒ `Σp, X≤p<2X × TwinPrimeAt p`; choose sufficiently large X≥N for each N | Conditional composition, source open |
| CT18 | `TwinPrimesInfinitelyOftenFinal`: export the UNCONDITIONAL, ZERO-POSTULATE theorem through the TOE roots, with all premises of CT15 *proved*, NOT record fields left uninhabited | Final goal, OPEN |

Important: CT15a/b are NOT an assertion that a standard sieve
already supplies the requisite estimate. They define an auditable
research decomposition. The novel proof must explicitly defeat
the residual parity-indistinguishability obstruction, not merely
rename it as `CorrelationLaw`, `UnboundedNonzero`, `Positivity`,
`Ibrahim`, `QID` or a supplier parameter.

### D. Distinguish the two goals

Proving the **number-theoretic** twin-prime theorem requires
CT01–CT18 (excluding any unused optional stronger estimates).
The more ambitious **signed SSP/FRACTRAN executable BIDI** additionally
requires A03/A07/A08/A09, B02–B07, C02–C08, D03–D08 and E15
from the original 101-lemma matrix: machine trace semantics,
faithful readout, true reachability and certificate transport.
Those DO NOT bypass CT15, and need not block working on CT15
in parallel.

**Proof order for highest-alpha work:** CT02/CT03/CT04/CT05
(concrete original semantic model), CT06–CT09 (kernel and
consumer proof), CT10–CT14 (elementary proper-power bound),
CT15a/b (new mathematics and independent adversarial
counterexample checks), CT16–CT18. No CI shortcut, no ESD edits;
the Golden Agda --safe kernel, rather than Python,
is final proof authority.

Primary source: Tao, `A general parity problem obstruction`
(2014); Hardy–Littlewood, `Partitio Numerorum III` (1923);
Brun (1919), Zhang (2013/14), Maynard/Tao and
Polymath8b (2013–2014). Original Riemann/Mangoldt,
DASHI module authors, and preexisting
Pareto/Snowball/Ibrahim/QID source ownership remain distinct.

## 30 October 2026 — new max-cut: constructive CT09b + CT10 using existing in-repo integer square root

**Source audit this turn (actual Agda, not just PR):**
Read the #1408 `TwinPrimeMangoldtNonzeroPrimeSumWitnessExact.agda`,
`TwinPrimeCertifiedEnumeratorExact.agda`,
`TwinPrimeSixWheelExact.agda`, the real
`RiemannPrimePowerCounting.agda` interfaces, and the original
`RiemannPrimePowerArithmetic.natPow`.
Located and READ `DASHI/Mathematics/NumberTheory/FiniteNatFloorSquareRootExact.agda`
on `master`. Its `floorSquareRootUpToMaximal` is the
exact existing donor for base-sqrt bounds; no extra sqrt algorithm
is necessary. Also inspected `FinitePositiveFactorPairExact`,
`BishopNatEmbeddingPowerValidation`, and
`PrimeCountingTransforms`: Riemann/Möbius bridge *records*
are not a concrete proof of the gap-two correlation.
Lean and PR #1244/#1275/#1414 owners remain distinct and
not automatically merged; their S3/RGS/Ibrahim/QID
equivalence does not satisfy NatPrime.

**Implemented source-written, Agda kernel PENDING:**

- CT09b in `TwinPrimeMangoldtNonzeroPrimeSumWitnessExact`:
  `twinInIntervalBoundedReadout` and
  `nonzeroPrimeOnlySumGivesBoundedTwin`. The witness now
  has BOTH `start ≤ p` and `suc p ≤ start+count`;
  original `twinInIntervalReadout` remains for existing callers.
- CT10a in `TwinPrimeProperPowerFloorRootBoundExact.agda`:
  `powTwoEqualsSquare`,
  `powNextAtLeastPrevious`,
  `squareBelowEveryProperPower`,
  `properPowerBaseLeFloorRoot`.
  Reuse the ORIGINAL proved-in-source Nat floor square root.
  For all **positive** bases b and exponents e≥2,
  `b^e≤U ⇒ b≤floorSquareRoot U`.
- CT10b in `TwinPrimeProperPowerBinaryExponentLowerExact.agda`:
  `binaryPowerBelowPositiveBasePower`,
  `properPowerBinaryCeiling`, using Nat multiplication
  monotonicity. For every base b≥2,
  `2^e≤b^e≤U` for exponent e≥2.
- CT10 conjunction in `TwinPrimeProperPowerRectangleBoundExact.agda`:
  `ProperPowerRectangle` and
  `properPowerInRectangle`. A proper prime-power index
  must lie in the actual finite coordinate rectangle
  `b≤floor sqrt U` and `2^e≤U`.
  This rectangle is NOT yet counted in Agda as a
  cardinality ≤floor sqrt U ×floor log₂ U.

**Actual local Python executed:** independently enumerated all
prime powers up to U=80002, and checked the CT10 bounds,
CT11 integer #proper ≤isqrt(U)×floorlog2(U),
and the corresponding **numerical** weighted CT13 envelope
over 247 dyadic windows (up to X=40000): PASS.
The oracle encountered 1,427 actual non-prime-pair
prime-power error terms and 56,996 total nonzero pair
terms across these windows. The independent regression was
committed as `scripts/check_twin_prime_m15_proper_power_envelope.py`.
This is finite oracle evidence only, not Agda kernel receipt
or a proof of the asymptotic weighted bound.

**Still UNPAID:** CT01 full safe Agda compilation,
CT11 genuine cardinality over a duplicate-safe
power/base/exponent finite enumeration (the rectangular
coordinates just proved), CT12 real log and product
upper bound, CT13 finite error bound, CT14
`o(X)` in certified ordered analysis, CT15 parity-sensitive
gap-two positive correlation, CT16–CT18 unconditional final closure.
Do NOT import `NSPeriodicCanonicalRealAuthorities`
as golden `--safe`: the file explicitly carries
postulates. No ESD edits, no CI, no spurious proven
Monster/symmetry/QID representations.

**Fresh primary research (Oct 2026):** Wang's version 0.8
`Why expansion methods for Chowla do not reach twin primes`
(Zenodo 23694711, 27 Oct 2026) proposes explicit
dilation/entropy parity limitations. It does NOT
rule out all future approaches, but is a worthwhile
adversarial test for any CT15 remainder claim.

## 30 October 2026 — CT15a signed Möbius-convolution exact finite probe

**Research objective:** Prove the new gap-two shifted Mangoldt
correlation estimate ourselves, not import or assume it. Explicitly
test the *signed residual* instead of quotienting it away.

Reused/checked the actual original
`DASHI/Analysis/RiemannPrimePowerCounting.agda`
`MobiusScalarKernel` (a parametric Riemann prime-count
inversion, NOT an already proved shifted-Lambda identity),
`PrimeCountingTransforms.agda`,
`RiemannVonMangoldtSpecification.agda`,
`FiniteNatFloorSquareRootExact.agda`; actual
`dashi_lean4/MoonshineFractran.lean`,
`dashi_lean4/docs/DECLARATION_LANDSCAPE.md`,
`agda2lean/README.md`. Refreshed heads #1244/#1275/
#1408/#1414: no foreign branch was silently merged.
Respected Pareto admissibility, Snowball provenance,
Ibrahim 3B owner and QID identity-not-proof roles.

**Committed exact symbolic local Python:**
`scripts/check_twin_prime_ct15_exact_mobius_parity_probe.py`.
It implements the CLASSICAL divisor identity, as a formal
vector of integer coefficients of `log(p)`:
`Lambda(n) = sum_{d|n} mu(d) log(n/d)`.
The shifted product expands to a signed double-divisor sum.
A surviving term has `d|n,e|n+2`, and therefore
`gcd(d,e)|2` (necessary CRT compatibility).
Independent direct prime-power classification matches
the signed expansion EXACTLY over all 8 dyadic windows
X=2,3,5,10,59,100,270,500. For X=500,
34,943 positive and 34,930 negative signed unit
coefficients cancel to just 13.
All tested symbolic coefficient identities and necessary
CRT conditions PASS.

**Status:** CT15a has a compelling **finite computational
identity**, but a corresponding unbounded Agda/analytic
divisor-convolution theorem is not yet proved;
CT15b/c remain OPEN. The cancellation magnitude shows
why positive coarse finite-sieve survivors or bounded-gap
estimates cannot be promoted to a uniform lower bound.
To reach CT15c, an independently proved *uniform* signed
bilinear remainder estimate is required. Neither the
finite receipts nor a new `RemainderEstimate` field
can discharge it. Treat the Wang 2026 parity-limitation
report as an adversarial method check, not an external
proof of impossibility or a resolution.

**Committed incremental proof paydown:**
CT09b now source-written with strict interval endpoint;
CT10a/b and their rectangular conjunction source-written.
CT11–CT14 remain complete-proof obligations; their
local Python checks are finite. No protected ESD edits,
no CI. Agda kernel proof still pending.

## 30 October 2026 — further CT13/M15 max-cut: nonzero retained error has proper-power witness

**Actual source-written Agda:** 
`DASHI/Arithmetic/TwinPrimeMangoldtErrorSupportProperExact.agda`,
imported once through `EverythingTOESymmetryResolved369`,
`Unifier` and `Unified/Everything`.

Reuses the original `RiemannVonMangoldtSpecification`,
the exhaustive `TwinPrimeMangoldtExhaustiveSupportCaseExact`
three-way cases, the original finite prime/error split,
and explicit `ProductZeroLaws` (NOT silently inferred).
Defines `ProperPowerAt`, `ProperPowerAtEitherEndpoint`,
and two nontrivial case theorems:

- `errorZeroIfNoProper`: if no left/right proper prime-power
  occurrence exists, the actual retained error scalar
  is exactly zero. Handles all nine support combinations.
  Outside-support contributions require the real zero
  multiplication laws; exponent-one/exponent-one has
  retained error zero by source definition.
- `errorNonzeroHasProperPower`: for any Nat `n`,
  a proof that the retained error weight is **not**
  equal to zero yields a real, ORIGINAL
  `AllPrimeArithmetic.Prime` and exponent ≥2
  for `n` or `n+2`. This is a constructive
  source-level inverse support witness, not a
  finite-sieve class or prime-density assumption.

**Actually executed local Python:** 150,000 candidates
with independent prime-power trial-factor classifier:
47 nonzero proper-power error pairs, 1,701 genuine
prime/prime pairs, 148,252 outside-support pairs.
For every 47 error pair, actual proper-power bases
satisfy the integer `isqrt(n+2)` limit and
`2^exponent≤n+2`. PASS. Committed runnable oracle
`scripts/check_twin_prime_m15_error_support_proper.py`.
Earlier executed 247-window numerical CT13 error tests
and 8-window CT15 signed-Möbius parity audit remain
recorded separately. No kernel receipt or analytic
unboundedness claim.

**Updated exact debt:**

1. CT10a/CT10b: base and binary-exponent rectangular
   envelopes SOURCE-WRITTEN, not kernel-checked.
2. M15-support: only nonzero errors occur at proper
   powers SOURCE-WRITTEN, not kernel-checked.
3. CT11: PROVE rectangle index enumeration/cardinality
   with duplicate-safe counting of prime-power
   **values**; a pair's error support counts at most
   twice the proper-value support, not arbitrary pairs.
4. CT12: REAL ordered logarithm positivity/growth,
   not a Nat-valued weight proxy.
5. CT13–CT14: assemble the uniform actual weighted
   residual bound and its sublinearity.
6. CT15: **still genuinely missing** uniform negative
   cancellation bound on the signed Möbius/divisor
   shifted prime-pair correlation. The exact finite
   parity probe detects enormous cancellation;
   it does not assert a positive asymptotic.
7. CT16–CT18: compose with genuine certified
   nonzero-prime-only-sum-to-witness theorem, close
   under Golden Agda --safe with no postulates.
No ESD files, no CI; provenance retained for
original mathematical authors, independent
DASHI/Lean authors, Pareto/Snowball/Ibrahim/QID.

## 30 October 2026 — CT11 exact candidate image max-cut, actual Agda/Lean/PR audit

**This turn's actual repository inspection:** #1408 current Agdas
`RiemannPrimePowerArithmetic.natPow`,
`TwinPrimeProperPowerFloorRootBoundExact`,
`TwinPrimeProperPowerBinaryExponentLowerExact`,
`TwinPrimeProperPowerRectangleBoundExact`,
`TwinPrimeMangoldtErrorSupportProperExact`,
`TwinPrimeMangoldtNonzeroPrimeSumWitnessExact`;
master `FiniteNatFloorSquareRootExact`,
`FiniteWeightedReindexExact.listLength`,
`ChebyshevPrimeCounting` and
`RiemannPrimePowerCounting`. Also fetched actual
`dashi_lean4/MoonshineFractran.lean`,
`docs/DECLARATION_LANDSCAPE.md`, `agda2lean/README.md`,
#1244 Horned-S3 quotient, #1275 Zipf pattern, #1414
Polynomial-Ibrahim/Pareto/Snowball, and the original Pareto
semantic-admission/QID identity boundary files. Refreshed all
four PR heads. Independent S3/RGS/Monster/orbit identities must
not be promoted into a Nat-prime correlation theorem.

**New source-written CT11 owner:**
`DASHI/Arithmetic/TwinPrimeProperPowerRectangleEnumerationExact.agda`.
Imports the EXISTING `FiniteWeightedReindexExact.listLength`,
the ORIGINAL `RiemannPrimePowerArithmetic.natPow`,
the ORIGINAL `FiniteNatFloorSquareRootExact`, and the
CT10 square-root lemma; no redundant finite-power ontology.

- `powerRow` / `powerRowLength`: exact E exponent-index
  candidates with `k=0..E-1`, corresponding to exponent `k+2`.
- `powerRectangle` / `powerRectangleLength`: all bases
  `1..B` paired with all E indices, **exactly B*E entries**.
- `powerValueRectangle` /
  `powerValueRectangleLength`: map candidates through the
  original `natPow`; candidate LIST size unchanged.
- `filterCandidate` / `filteredLengthAtMost`: any
  filtered candidate count ≤ initial list count.
- Proof-relevant membership `_member_` and
  `rowContainsIndex`, `rectangleContainsIndex`,
  `powerValueRectangleCovers`: each positive-base
  bounded exponent coordinate genuinely appears.
- `properPowerCoveredByRootRectangle`: if a proper
  positive-base power ≤U and its exponent offset k<E,
  the numerical power occurs in the exact mapped
  `floorSquareRoot(U)*E` rectangle. This is a FINITE
  membership proof, not a density assumption.
- `insertIfFresh`, `dedupPowerValues`,
  `insertIfFreshLengthAtMost`,
  `dedupLengthAtMost`,
  `properPowerCandidateDistinctCountBound`:
  a structurally-recursive duplicate-eliminating power
  image with upper count ≤ B*E. **Source repair**:
  the initial `dedupPowerValues` used recursion on an
  arbitrary filtered list, which would not satisfy
  structural Agda termination; replaced it with
  `insertIfFresh` over the input list. No
  TERMINATING pragma, axioms, or postulates.
  One inserted-duplicate length branch was also fixed
  to use `n≤1+n` rather than reflexivity.
- All new CT11 source imports are present exactly once
  in `EverythingTOESymmetryResolved369`,
  `Unifier`, and `Unified/Everything`.
  No protected ESD edits.

**ACTUALLY executed local Python**: 714 distinct upper bounds
`U=4,11,...,4995`, rectangle cardinality and deduplicated
image checks; 22,645 proof-model coordinate/value
membership checks of genuine proper prime powers;
all PASS. Independently verified the exact script's
logic in the container before committing the reproducible
`scripts/check_twin_prime_ct11_rectangle_membership.py`.
This is NOT Agda kernel typechecking or a universal
analytic error estimate.

**Precise remaining CT11 subcut**: prove
`dedupPowerValues` is NoDuplicates and preserves
every input value's list membership (the count
inequality alone does NOT prove distinct cardinality);
prove an explicit total `floorLog2Nat(U)` exponent
cutoff such that `natPow 2 e≤U ⇒ e≤floorLog2Nat U`.
Then connect to actual distinct proper-prime-power
support and the exact M15 residue error.

**CT12–CT14** remain: explicit ordered logarithmic weights,
certified uniform weighted error `O(sqrt U log^3 U)`,
sublinearity. **CT15** remains wholly unproved new
parity-sensitive mathematics. Signed Möbius
`CT15a` is exact FINITE computational
identity only; neither positive main term nor
uniform negative-remainder bound is certified.
Prove rather than assume both.
**CT01/G06** full `--safe` Agda kernel closure is unpaid;
Agda/Lean binaries unavailable locally. No CI run.
External sources (Song–Yue 2026, Wang 2026) provide
claims/method diagnostics, not proof of gap 2.

### 30 October 2026 — CT11 candidate-image uniqueness and soundness follow-on

Extended `TwinPrimeProperPowerRectangleEnumerationExact.agda`
with additional **source-written, kernel-pending** finite
proofs after the rectangular enumeration:

- Replaced an unguarded filtered-list recursion in
  `dedupPowerValues` by structural `insertIfFresh`,
  with `insertIfFreshLengthAtMost` and
  `dedupLengthAtMost`; removed the need for any
  `TERMINATING` escape.
- `insertContainsNew`, `insertPreservesOld`,
  `insertMembershipBack`: proof-bearing insertion
  preserves every old element, adds the requested
  element, and introduces no other element.
- `dedupPreservesMember` and
  `dedupMemberComesFromOriginal`: membership BIDI
  between the mapped power candidate list and the
  duplicate-eliminated list.
- `DistinctValues`, `insertPreservesDistinct`,
  `dedupValuesDistinct`: all output numeric values
  occur at most once; a separate top-level
  `insertedMemberContradiction` avoids nested
  Agda with-clause scoping ambiguities.
- The prior `properPowerCandidateDistinctCountBound`
  gives length of the duplicate-free candidate image
  ≤ B*E; combined with `powerValueRectangleCovers`
  this is the desired finite-image domination
  **once an exponent cutoff is established for every
  proper power under the target U**.

**Actually executed local arithmetic model:** 714
targets; 361,752 candidate coordinates; all
duplicate-free mapped numeric images preserved
their source sets and obeyed the B*E upper bound.
An independent 22,645 true proper-prime-power
coordinate/value-membership sweep also passed.
These were Python finite checks, not Agda kernel receipts.

**Remaining CT11:** discharge `k<E(U)` for all
proper powers under U with the concrete
`E(U)=floor(log2 U)`; the existing binary
envelope only proves `2^(k+2)≤U`.
Formalise exact universal length/cardinality of
actual distinct proper-prime-power support from
the constructed membership BIDI.
CT12–CT14 still require a concrete ordered
logarithmic scalar and sublinear error theorem.
CT15c genuine signed parity-sensitive shifted-prime
correlation estimate remains NEW MATH and OPEN.
No ESD changes or CI; preserve original mathematical,
Agda/Lean, Ibrahim and QID ownership.

### 30 October 2026 — CT10 numerical reuse of existing canonical Core pow2

Additional repository-first search located
`DASHI/Core/GeneralResidualFibreCardinalityExact.agda`
(the original numerical `pow2` owner), as well as
`DASHI/Cognition/PNF/OrientedZeroCeilLog2Exact.agda`
(a **fixed four-state** ceil-log certificate, NOT a
universal floor-log2 estimator). The latter cannot be
reinterpreted as a proof for arbitrary Nat U.

New source-written module (kernel pending):
`DASHI/Arithmetic/TwinPrimeProperPowerCoreBinaryCapacityReuseExact.agda`.
`numericPowTwoEqualsCoreCapacity` proves
`RiemannPrimePowerArithmetic.natPow 2 e =
 GeneralResidualFibreCardinalityExact.pow2 e`
by primitive exponent induction, so CT10 reuses
the existing generic binary capacity function.
`properPowerNeedsCoreBinaryCapacity` transports the
already source-written CT10b inequality to
`Core.pow2 (k+2)≤U`, with NO invented
same-object prime/future-fibre interpretation.
All three canonical TOE roots import the bridge.

**Still OPEN:** the actual total natural-number
log2 cutoff for U (the fixed-4 `CeilLog2Certificate`
does not solve it), full CT11 distinct power-value
count theorem and CT12–CT15 ordered/analytic bounds.
The deduplicated numeric candidate image was
tested on 714 finite bounds; the source-written
membership and no-duplicates proofs remain kernel
pending. Do not claim a twin-prime discovery.

## 30 October 2026 — CT11 universal binary cutoff + source-integrity repair (fresh repo/PR/Lean audit)

**Current verified PR:** #1408 `feat/twin-prime-six-wheel-bounded-gap-reuse-20261028`; inspected
the actual source of the existing `TwinPrimeProperPowerRectangleEnumerationExact`,
`FiniteNatFloorSquareRootExact`,
`FiniteWeightedReindexExact`,
`TwinPrimeProperPowerFloorRootBoundExact` and
`TwinPrimeProperPowerCoreBinaryCapacityReuseExact`.
Checked actual `dashi_lean4/MoonshineFractran.lean`,
`dashi_lean4/docs/DECLARATION_LANDSCAPE.md` and
`agda2lean/README.md`, plus current PR heads #1244/#1275/#1414
and original Ibrahim/QID/Pareto source. The Lean declaration map distinguishes
checked-in statements from candidate bundles; no twin-prime gap-two
positive theorem is thereby proved. Preserve original authorship.

**REAL SOURCE DEFECT FOUND AND FIXED:** the CT11 rectangle module contained
7 literal `\\n` sequences where Agda import lines should have had
line breaks, plus duplicate `Agda.Builtin.Equality` and propositional
equality imports. This is syntactically invalid Agda independent of
Python mathematics. Repaired the header and consolidated imports on
the PR. Added `scripts/check_twin_prime_agda_source_integrity.py` to
detect literal escaped import newlines, duplicate module imports,
postulates, explicit holes and termination pragmas; its four regex
patterns initially had extra escaping and were corrected. It has an
optional `--require-safe` check. It is a TEXT LINTER, not a kernel
certificate. Current new proof modules do not have explicit
`{-# OPTIONS --safe #-}` pragmas; do not promote them to Golden
kernel-checked status.

**NEW SOURCE-WRITTEN CT11:**
`TwinPrimeProperPowerBinaryCutoffNatExact.agda` uses the ORIGINAL
`GeneralResidualFibreCardinalityExact.pow2` and ORIGINAL floor-square-root
maximality pattern to construct `floorBinaryExponent U`, with:
`positiveBinaryPower`, `exponentLeBinaryPower`,
`binaryExponentUpToMaximal`,
`binaryPowerExponentBelowCutoff`,
`properPowerExponentBelowCutoff`.
The exact theorem is `pow2 e≤U ⇒ e≤floorBinaryExponent U`,
for every Nat U,e, without importing real logarithm or a
fixed-4-state logarithm certificate.

`TwinPrimeProperPowerUniversalRectangleCoverageExact.agda`
composes this computed cutoff with CT10 floor-square-root and the
already source-written rectangular enumeration:
`properPowerInComputedRectangle`,
`properPowerInDedupComputedRectangle`,
`computedCandidateDistinctCountBound`,
`computedCandidateImageNoDuplicates`. For EVERY
base b≥2, exponent k≥2 and upper bound U with
`b^k≤U`, the numeric value belongs to the deduplicated list and
the candidate-list size is at most
`floorSquareRoot(U) * floorBinaryExponent(U)`.
The list can overcount with composite base candidates or values >U,
never omit an actual bounded proper power.
Both modules have exactly one import in each of the three TOE roots.

**Executed independent local arithmetic oracle:** for U=0..2048,
2,049 computed cutoffs agreed with integer `bit_length-1` where
defined, and 97,619 actual (base, exponent, bound) proper-power
coordinate witnesses passed. This is finite computation, NOT Agda typing.
The earlier 714 rectangle tests and 22,645 actual proper-power membership
checks remain separate executed evidence.

**Exact outstanding tasks, ordered by alpha:**
CT01: compile the new Agda dependency chain under actual Golden `--safe`
imports; repair all compiler failures, no postulates or unsafe pragmas.
CT11: bridge proof-bearing actual `AllPrimeArithmetic.Prime` p≥2 to
this numeric representation; prove finite distinct-value support
cardinality in an explicit membership/counting predicate over [0,U].
CT12–CT14: instantiate ordered logarithms and prove the global
nonnegative proper-power weighted error bound and `o(X)`.
CT15a/b/c: rigorously establish exact shifted prime-correlation
signed expansion, positive main term, and unconditional one-sided
cancellation estimate. **CT15 remains genuinely unproved new research.**
CT16–CT18: unconditional positive prime-only sum, certified twin
witnesses and final infinitude, not merely a conditional
`UnboundedCertifiedCountJumps` field.

**Fresh external adversarial reference:** Wang, Zenodo 23694711
(27 Oct 2026), version 0.8, distinguishes proved-in-model parity
counterfeits, computational claims, and independently unverified
method-limit proposals. Lü–Wang–Wu, arXiv:2610.20242 (Oct 2026),
studies cancellation of `Λ(n)μ(n+2)` (one shifted Möbius factor);
that is NOT equivalent to a lower bound for
`Λ(n)Λ(n+2)`. Neither may be promoted to a twin-prime proof.
No ESD edits and no CI executed.

### 30 October 2026 — exact 43-file static audit and CT11 computed-count corollaries

After the CT11 import-header repair, **all 43 changed
Agda paths matching TwinPrime/Mangoldt/ProperPower** on
PR #1408 were freshly fetched from the branch and
examined in four batches. No remaining literal `\\n`
import corruption, duplicated exact import declarations,
postulate declarations or `TERMINATING`/`NON_TERMINATING`
pragmas were detected in that 43-file subset.
This is a STATIC text check; it does NOT find all
Agda elaboration/type errors, verify imports' entire
transitive closure, or produce a Golden kernel receipt.

The actual newly added `TwinPrimeProperPowerBinaryCutoffNatExact`
and `TwinPrimeProperPowerUniversalRectangleCoverageExact`
lack `{-# OPTIONS --safe #-}`; fixing the complete safe
dependency graph remains CT01. No local `agda`/`lean`
binaries and no network fetch of the repo were available
in the container; no CI was run.

New CT11 formalisation derives, from the original
`FiniteNatFloorSquareRootExact.floorSquareRoot`,
`GeneralResidualFibreCardinalityExact.pow2`,
`FiniteWeightedReindexExact.listLength`, and the
original `natPow`, a fully computed candidate-image
bound `length(dedup(image(rectangle(U))))
≤ floorSquareRoot(U)*floorBinaryExponent(U)`, alongside
membership and duplicate-free image witnesses for each
positive-base proper-power value ≤U. These are source-written,
NOT kernel-verified. They still need a final connection to
an explicitly enumerated predicate of distinct certified
prime powers in [0,U], including the original all-prime
ownership bridge.

The October 2026 primary literature check includes
Liang Wang's version-0.8 *Chowla expansion limitation*
(Zenodo 23694711, 27 Oct; explicitly AI-assisted
and not independently specialist-reviewed), and
Lü, Wang, Wu (arXiv:2610.20242) claiming shifted
`Λ(n)μ(n+2)` cancellation. Neither provides an unconditional
`Λ(n)Λ(n+2)` positive lower bound.
No QID record, Pareto quotient, Snowball provenance,
Ibrahim orbit, Monster 3B resemblance, or finite
CRT/FRACTRAN receipt is promoted into CT15.

**Next Pareto cut:** isolate a genuine ordered-log
scalar instance and the CT12 pointwise weight upper
bound; then prove CT13/CT14 from the now
candidate-bounded distinct proper-power support.
In parallel, attack CT15c's genuine shifted gap-two
signed cancellation; reject any bound relying only
on the finite wheel survivor count, which admits
composite–composite counterfeit pairs.

**Reproducibility addendum:** `scripts/check_twin_prime_ct11_binary_cutoff.py` now contains the independently run finite arithmetic experiment covering 2,049 bounds and 97,619 proper-power coordinate witnesses, using exact integer powers and no floating logarithms. The script was committed after the inline local algorithm was executed; the checked-in file has not been separately run from a local repository clone in this environment (network unavailable). No kernel receipt implied.

## 30 October 2026 — CT11 to M15 actual-error-support membership bridge

Added `DASHI/Arithmetic/TwinPrimeMangoldtProperPowerCandidateCoverageExact.agda` to the active #1408 head (source-written, Agda kernel pending). Reuses the original `VonMangoldtAt` prime-power support, the existing `errorNonzeroHasProperPower` / `errorZeroIfNoProper` theorems, and computed CT11 deduplicated finite power image. `properPowerAtCovered` maps an actual bounded `ProperPowerAt` into the image, `nonzeroErrorEndpointInCandidateImage` maps any nonzero retained error to at least one of the two endpoints in that same image, and `errorZeroOutsideComputedCandidateImage` gives the exclusion direction. These are source-facing logical membership statements, **not an analytic estimate**.

The original `AllPrimeArithmetic` contains only `toNat` and injectivity, **not** a proof that `toNat p >= 2`. The new bridge `PrimeBaseAtLeastTwo.baseAsTwoPlus` is therefore an explicit conditional proof input, to be discharged from the already-owned `ChebyshevPrimeOwnership.carrierIsPrime` and NatPrimality's minimum-prime theorem. The corresponding record is NOT constructed or assumed globally. An image containing composite-base and out-of-range candidates is an upper envelope only. Exact interval-position support cardinality (including duplicate-free endpoint-to-position indexing), ordered real logarithmic weights, CT13/CT14 sublinear bound and CT15 signed-correlation breakthrough remain **open**.

Actual repo inspection for this cut: fetched and read #1408's `RiemannVonMangoldtSpecification`, `RiemannPrimePowerArithmetic`, `TwinPrimeMangoldtExhaustiveSupportCaseExact`, `TwinPrimeMangoldtPrimeErrorFiniteSplitExact`, `TwinPrimeMangoldtErrorSupportProperExact`, `TwinPrimeProperPowerRectangleEnumerationExact`, `TwinPrimeProperPowerBinaryCutoffNatExact`, `TwinPrimeProperPowerUniversalRectangleCoverageExact`, `ChebyshevPrimeCounting`, `TwinPrimeMangoldtPrimeOneCertifiedBidiExact`; read `dashi_lean4/MoonshineFractran.lean` and its declaration landscape; checked active #1408, #1414, #1440 and #1439 heads. This source-to-source check is not a Golden `--safe` kernel receipt. No protected ESD source is edited; Ibrahim, Pareto, Snowball, QID and Monster-3B attribution and same-object non-promotion rules remain intact.

**External October 2026 adversarial reading:** Lü–Wang–Wu, `arXiv:2610.20242`, treats shifted `Λ(n)μ(n+2)` cancellation, not `Λ(n)Λ(n+2)≥cX`; Liang Wang, Zenodo 23694711 (version 0.8, 27 October), studies method-limit countermodels and does not prove twin-prime infinitude. Inherited claims remain attributed to their authors, separate from the new DASHI bridge source ownership.

### CT11/M15 certified-base closure (same 30 October cut)

Follow-up commit `f4a9e891` **discharges**, rather than merely carries, `PrimeBaseAtLeastTwo` when the *original* `ChebyshevPrimeOwnership` is supplied. `natPrimeBaseAsTwoPlus` excludes Nat 0 and 1 using standard-library `Data.Nat.Primality.¬prime[0]` and `¬prime[1]`; `primeBaseFromChebyshevOwnership` consumes the existing `carrierIsPrime` field, no new postulate or extra mathematical premise. New `nonzeroErrorEndpointFromCertifiedOwnership` and `errorZeroOutsideImageFromCertifiedOwnership` specialize support inclusion/exclusion. Ownership itself remains an explicit real carrier input (CT02); no concrete global `AllPrimeArithmetic` or ordered logarithm has been manufactured. The source is uncompiled. Numeric regression `check_twin_prime_ct11_to_m15_error_image.py` is committed; the independently executed local oracle covered 1,997 upper bounds / 1,995,003 pair positions with zero missed support; the checked-in file itself was not executed from a GitHub checkout in this environment. Composite-base example 36 and candidate values above U show that image membership is not equivalent to proper-prime-power membership. CT12–CT15 remain open.

### CT13 finite position-image max-cut (same branch, 30 October 2026)

Source-written `backTwoAfterPlusTwo`, `candidatePositionEnvelope` and `candidatePositionEnvelopeLength`: for every proper-power candidate value v, the only shifted-pair positions potentially affected are v and v-2 (the latter truncated to 0 for v<2; an overcount). The list has **exactly twice** the length of CT11's dedup value image, without using analytic estimates. `nonzeroErrorPositionInComputedEnvelope` maps each actual nonzero retained error in a bounded interval into that position list, using the genuine Chebyshev/NatPrime ownership, not an SSP residue filter. `computedPositionEnvelopeLengthBound` derives the finite numerical envelope `<= 2*floorSquareRoot(U)*floorBinaryExponent(U)`.

A further reuse of the *existing* `Rect.dedupPowerValues` proves `distinctErrorPositionNoDuplicates`, `nonzeroErrorPositionInDistinctEnvelope` and `distinctErrorPositionEnvelopeLengthBound`. Thus an **actual duplicate-free covering list of numeric positions** exists, with the above length cap and membership for any certified nonzero residual. This is closer to CT13 than counting unrestricted candidate powers, but the separate finite interval-position count predicate, the scalar upper log-weight and sum domination remain unproved. No Agda compiler was run. Independent local exact-number oracle: U=4..2000, 1,998,997 shifted pairs, 90,424 proper-power-support cases covered, 0 misses, duplicate-free position count never exceeds twice the candidate image count. The checked-in test was updated, but not separately executed from checkout here.

## 30 October 2026 — parity front / minimal separator / canonical logarithm reuse

**CT11:** added canonical stdlib floor-log₂ exponent cutoff, proof-level bridge from original `Core.pow2`, and expected extensional `customAndStdlibFloorLogAgree`; standard-library-log proper-power rectangle membership, duplicate-safe image and cardinality proof are source-written. Distinguish arithmetic Nat log₂ from actual ordered-real `log(p)`. Agda kernel pending.

**CT15new:** exact signed Möbius discriminator: for actual prime p, `μ(p+2)=-1` comprises genuine prime partners **or** squarefree partners with odd `ω≥3`. All odd composite counterfeits have a factor ≤ cube-root(p+2). Existing Agda no-go owner extended with concrete 103+2=105=3*5*7 versus 3+2=5, requiring original certified NatPrime, not a QID/geometry shortcut. New finite Python parity regression executed independently at 5 dyadic windows; last window X=1,000,000 has 6,702 true twin starts and 19,905 odd-composite false positives among 26,607 negative signs. Neither proportion nor a log-scale margin is proved asymptotically.

**CT15alt/CT16–CT18:** actual scalar identity `S=P+E` and left zero imply `S≠E → P≠0 → certified twin`. New existing-owner `totalErrorUnequalForcesPrimeOnlyNonzero`, `observedTotalErrorSeparationGivesBoundedTwin`, `cofinalObservedSeparationImpliesTwinInfinitude` retain explicit unproved cofinal mismatch (or observed mismatch) input, rather than fabricating a lower bound. A finite orbit/quotient/numerology observation does not distinguish the actual arithmetic sums unless a **typed, proved** observer with the required source compatibility is supplied.

**Lower-bound Pareto hierarchy:** original uniform linear `S(X)≥cX` is sufficient but not necessary. Positive correlation above the proper-power error at arbitrarily late scales suffices; with true `E=O(√X log³X)`, a cofinal `S(X)≫X^(1/2+δ)` would suffice. Research remains CT15, no unproved theorem promoted. Lü–Wang–Wu (14 Oct 2026) `Λμ` cancellation does not supply the `ΛΛ` lower bound. The original Yang–Mills/RH/geometry/Ibrahim/Pareto/Snowball/QID provenance and non-promotion laws apply unchanged.

**CT12/CT14:** examined actual `InverseLogarithmFromExponential`, `OrdinaryTranscendentalRealization`, `ConstructiveRealSpine`, `CanonicalDASHIRealBackendExact` and terminal one-point model; no admissible concrete *ordinary* ordered real logarithm instance yet. No kernel or CI pass; no ESD modifications.

### 30 October 2026 — deeper parity cube threshold and canonical CT13 count

- CT15-parity elementary owner: `TwinPrimeOddCompositeCubeRoughCutExact.agda` (`--safe`, source-written) proves the universal product-order cube bound `B³<=a*b*c*t` for a,b,c>=B and t>=1, and rules out a certified triple of big factors when `value < B³`. Original 103/105 Agda counterfeit imports the lemma and produces the explicit 105 bound. Generic actual Möbius squarefree factor-list reflection, short-divisor conditioning and a cofinal count of genuine rough shifted primes remain UNPROVED.
- CT11: `customAndStdlibFloorLogAgree` identifies old computed numeric cutoff with stdlib `⌊log₂⌋`, with `computedAndStdlibDedupPowerImagesAgree` identifying the full mapped/deduplicated candidate lists. CT13: the exact *numeric* covering position set obeys `<=2*floorSquareRoot(U)*⌊log₂U⌋`. It contains all certified error support; this is NOT a real upper-weight estimate.
- CT15/CT18 terminal missing mathematical theorem: establish cofinal `S_I≠E_I` for *actual* same-carrier Mangoldt scalar sums, or prove positive `S_I>E_I` using nondegenerate real logarithms. `cofinalObservedSeparationImpliesTwinInfinitude` is only a conditional compiler whose observer-disequality premise has no proof. No quotient/SSP/Monster/Ibrahim/QID source identity can serve as that premise.
- CT01: kernel `agda --safe`/Lean receipt unavailable in this runtime; static checks and executable exact-integer probes do not certify source proof terms. No CI and no protected ESD modifications.

### 2026-10-30 — FRACTRAN full-vs-compressed machine and Pickover fibred CT15 attack

- **New exact source owner:** `TwinPrimeFractranResidualHyperfabricExact.agda` consumes `SignedSSPFRACTRANWeaveExact` full fifteen prime lanes (7,47,59), `FRACDASHNumericInterpreterTargetExact` real first-applicable rule semantics, original `FractranCOL` 5-lane and `SSP15FractranCompression` non-promotion, `TwinPrimeNat270PeriodResidualBidiExact` full numeric q,r code, and existing 59/329 consumer collision. Actual (1/7,1/47) miniature rack chooses 1/7 for 329→47 and rejects 59; not an arbitrary twin program.
- **Concrete SIN-9999 reuse, no duplicate ontology:** inhabit `PickoverConsumerResidualFibreBridgeExact.SignedPhaseFibre` with a period/q repair of actual `Twin.twinStartBool`, prove both necessity from concrete 59/329 collision and sufficiency from inherited exact coarse/fine reconstruction. Original `ConsumerIndexedResidualRefinementExact` owns the generic collision/separation results.
- **Second axis / genuine arithmetic consumer:** exact original VonMangoldt pair correlation passes pointwise through the retained q,r fibre and over ANY finite start/count through `TwinPrimeResidualMangoldtFiniteSumBidiExact`, then rejoins original `finiteMangoldtPrimeErrorSplit`. This pays finite indexed-window *semantic compatibility* only, not cofinal analytic positivity.
- **Open real compiler gate:** supply an inhabited, sound `VerifiedFractranCrankPipeline.FractranMachine` and `SoundFractranTwinReadout` backed by real arithmetic and preserving ordered fraction step/run semantics. One finite factor receipt at 59/329 is not a general all-prime valuation interpreter. A finite fixed Ogg alphabet could compute arbitrary arithmetic with a *proved* general program, but it is not a direct all-prime factor-labelled sieve.
- **Open frontier math:** get a new unconditional cofinal actual-correlations-vs-proper-power-error separation or shifted-prime short-divisor exclusion; residue/fibre preservation and exact bounded trial division do not force infinitely many twin primes.
- Keep source Agda Golden, Lean follows, 0 postulates/metas/unsafe termination; all new source kernel pending, no CI and no ESD edits; attribution to Conway, mathematical originals, independent Ibrahim Monster 3B, Pareto/Snowball, QID and meta-introspector owners.
