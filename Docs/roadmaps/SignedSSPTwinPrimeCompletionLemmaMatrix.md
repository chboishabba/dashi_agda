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
| T06 | `threeAxisCapacityIsTwentySeven`: derive 27 from 3³, not vice versa. | O + S: owner + export |
| T07 | `orderedPairAxisCountIsSix`: two ordered 3-coordinate points have six coordinates. | S; #1407 also has an exact `TritCube 6` BIDI owner, separate branch |
| T08 | `orderedPairCapacityIsSevenHundredTwentyNine`: 27×27 = 729 is a cardinality of typed ordered pairs. | S; #1407's independent 343/386 incidence result stays source-owned |

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
| E05 | Reconstruct residues from pairwise coprime prime moduli (CRT) | N: genuine arithmetic CRT, not a mixed-radix codec |
| E06 | Forward/reconstruction inverse laws | N: both directions with coprime witnesses |
| E07 | General finite pairwise-coprime prime product CRT | N: inductive step with a coprime-product proof |
| E08 | Exact total survivor count `∏(p−ν_p)` modulo product | N: leverage E02–E07 and `FinitePrimeProductSieveExact` |
| E09 | Product of any finite prime moduli is a sieve period | S: `CertifiedPrimePairPeriodExact` (even with repeated axes) |
| E10 | Filter order invariance | S: same owner; reordering conjunction |
| E11 | Duplicate prime filter idempotence | S: same owner |
| E12 | Fresh filters only remove candidates | P: monotonicity theorem / explicit refinement import |
| E13 | Genuine twin p,p+2 passes each proper finite small-modulus filter | N: handle modulus equal to endpoint and range assumptions correctly |
| E14 | Arbitrarily large double-composite survivors of each fixed finite sieve | P: independently executed CRT construction, Agda CRT proof outstanding |
| E15 | FRACTRAN decoded-exponent / CRT commuting square | S: signed ±2 both sides; raw (2^p) parity no-go; full VM interface outstanding |

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
