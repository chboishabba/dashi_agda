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
