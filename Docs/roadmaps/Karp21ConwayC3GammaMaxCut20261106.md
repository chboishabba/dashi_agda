# Conway / C3 / primorial integration: exact Karp-head max-cut

Target source head: `730f62ed27a0c45d71c89e5cdbc61bd9f1e6ab2c`
on `chatgpt/karp21-reduction-transport`. This is a descendant branch
and leaves the existing original Karp proof owners unchanged except
`Karp21Everything.agda`, which now imports the new owners.

## Source provenance and distinctions

- J. H. Conway, chained arrow notation: finite positive chains and six rules
  (https://en.wikipedia.org/wiki/Conway_chained_arrow_notation).
- Stephen Cook (1971) and Richard Karp (1972): NP completeness,
  source/target languages and polynomial reductions.
- Peter Elias: gamma coding. Karp-21's original
  `Karp21GammaBinaryGoldenCoreExact.encodeGammaNat`,
  `Karp21GammaZigzagPartitionWordDecodeExact.readGamma`,
  `Karp21GammaBinaryRoundTripExact.gammaReadEncodeSuffix`
  are the actual transitive input/output owners.
- Existing DASHI `TriadicClosureTower`, `C3CubeFourier27Exact`,
  `VerifiedFiniteTritCoder`, and `PrimorialFactorAddressConcrete`
  are the original finite object/codec donors.

## K01 — total semantics

`Karp21ConwayTotalChainExact` uses a prefix state with:
- `value : Nat` = value of the prefix `X`;
- `extension : Nat -> Nat` = meaning of `X -> t`;
- `chainStep value extension q p` = meaning of `X -> p -> q`.

For q = 1, this is `extension p`. For q > 1 and p = 1,
this is `value`. For p,q > 1, it equals `iterate (chainStep
value extension (q-1)) (p-1) value`.

This is structural recursion in q, plus structural finite iteration
and a structural fold over the input list: no fuel, `TERMINATING`,
postulates or giant numeral reduction is used.
The original sixth Conway rule is source-written as
`chainRuleSix`, and first three-term examples are closed by
`refl`. The empty chain correctly evaluates to 1.
The `Positive` constructor and `evaluatePositive` avoid zero
as a semantic chain input. Full universal semantic correspondence
for all prefix rewrites (not only the source-written local rules)
remains part of exact-head proof verification.

## K02 — actual binary codec

`Karp21ConwayGammaChainCodecExact` reuses the SAME
`FiniteWordSizeExact.BitWord` and original Elias gamma owner:
`gamma(number-of-entries) ++ concat(gamma(entry))`.

Source-written:
- `chainReadEncodeSuffix`: decoder preserves any remaining suffix;
- `chainDecodeEncode`: full strict parse/encode roundtrip;
- `entryWireSizeExact` and `chainWireSizeExact`: literal bit-length equations;
- `positiveChainRoundTrip`: typed strictly-positive chain carrier.

`Karp21ConwayPrimorialGammaAdapterExact` reuses the existing
four-coordinate prime-exponent carrier and proves `factorDecodeEncode`.
A primorial address value, the prime-factor product, and a Conway
expression are three different semantic readings and are never
equated. More general variable-length prime exponent vector and
actual polynomial tape cost remain open.

## K04 — actual same-object bridge

`TriadicClosureTower.TriadicCube` and
`TriadicClosureTower.ThreeSuperThree` are both
`Trit -> Trit`, definitionally. The source proof is `refl`.
`ConwayC3SameObjectCodecExact` adds the explicitly invertible
`C3CubeFourier27Exact.Cube3 <-> Trit -> Trit` table map,
pointwise additive C3 transport, the original C3^3 character action
and character homomorphism, strict six-bit reverse decoding with malformed
reserved-word rejection, and reuse of
`VerifiedFiniteTritCoder.encodeTriple` (six-bit fixed width).

This identifies selected carriers with a proof of operation transport,
not merely two things counted as 27. It does not identify path-graph
adjacency with cyclic Cayley adjacency or preserve an arbitrary
biological/physical dynamics without separate verification.

## K03 / K05 / K06 — true original Karp gates

Do NOT replace the existing selected N21/E20 complete-graph/sparse
word semantics with a contrived `C3` equality problem. The original
branch already includes source candidates for:
- original SAT / guarded Cook-Levin machine and Cell/Bits,
- original signed PARTITION -> weighted MAX CUT E20,
- original sparse endpoint 2m-bit N21 witness and universal semantic iff,
- original gamma graph readers and Fin-free raw byte/verifier costs,
- original NP-completeness transport requiring all twenty real edges
  and twenty-one membership certificates.

An actual `PR.PolynomialManyOneReduction` on those selected words
still requires the exact original source and target language iff,
including malformed inputs, and real polynomial-time compilation
with full binary machine clock. A succinct Conway AST cannot stand
in for the actual output word if expansion is enormous. No SAT lower
bound, NP membership or full Karp network completion is inferred
from the symbolic coding bridge.

## K07 — acceptance

The expected head checker is the repository's `parallel_checker`
and the Karp referee target `scripts/referee_karp21_maxcut.sh all`.
The current tool environment has no local Agda executable, no
`parallel_checker` binary, and no local GitHub checkout/network.
The Agda theorem sources and original imports above are therefore
not independently kernel accepted in this work session.

The retained executable reference fixture is
\`scripts/check_karp21_conway_gamma_reference.py\`, now called by the
existing original \`referee_karp21_maxcut.sh\` preflight. The referee
also typechecks the new safe K01/K02 roots in golden mode.
A bounded independent reference check compared 103 finite chains
against a separate direct implementation of the six Conway rules;
18 chains with impractically large expansions were skipped.
The independent gamma token fixture passed 781 strict roundtrips
(including rejection of trailing bits). This is regression evidence,
not Agda acceptance. No claim is made about all 20 historical
reductions or a proof of P != NP.

## ZKP / O-R-C-S-L-P-G-F

O: repository Karp-21 and Conway symbolic cross-domain translation.
R: SHA above; the new integration branch must be reviewed relative
to the exact branch head, not silently rebased onto a different owner.
C: real original Gamma, Word, C3 and primorial owners.
S: source-written Agda with independent bounded numerical control.
L: positive Conway terms -> original binary gamma word -> strict parse
-> same positive syntax; separately cube -> trit lookup -> six bits.
P: original codecs and full grammar; no resource-bound assumption.
G: full strict roundtrip, source-level Conway recurrence, algebraic
C3 preservation and exact wire lengths.
F: Agda `--safe` receipt plus real Karp-21 reduction and machine
clock obligations, not fabricated by these representation theorems.

Priority: run the original golden referee on this head; resolve first
actual Agda diagnostics; only then promote C01/C02/C04. Continue
original N21/E20 machine-cost and Karp-21 network gates independently.

## 2026-11-06 — arbitrary-bit grammar strengthening and independent controls

K02 gains two additional SOURCE-WRITTEN universal theorems in the actual
gamma `BitWord` owner:

- `chainFullBinaryNoProperPrefix`: any raw bit suffix that makes a
  complete encoded chain equal a second complete encoded chain is empty.
  This is not restricted to whole three-bit or gamma tokens.
- `chainEncodeInjective`: two chain syntax lists with equal encoded words
  are equal lists, using the exact original suffix-preserving reader.

Independent local Python reference controls (not kernel proofs):
- 103 positive Conway rule agreements over 0–4 entries from {1,2,3};
  18 larger cases skipped under the explicit evaluation cap.
- 224 additional positive Conway rule agreements for 5–7 entries
  from {1,2}; zero skips in that tranche.
- 781 chain-gamma strict roundtrips with bounded lengths and values.
- Exhaustive 8,191 binary strings of lengths 0–12:
  133 canonical codewords re-encode identically, 8,058 rejected.

The checked Python reference and the exact Agda source are
different artifacts. The original `parallel_checker`/Agda 2.9
kernel acceptance is STILL required for promotion. The source
head of this branch must be pinned again after the final edit.

## 2026-11-07 — actual original N21 bitword comparison-count cost bridge

New owner `DASHI.Mathematics.Complexity.Karp21FinFreeOriginalWordComparisonBoundExact`
is imported in the actual Karp21Everything source root and Golden referee.

**ORIGINAL donors**, not alternative toy language:
- `Karp21FinFreeRawReaderSparseBudgetExact.actualFinFreeRawGraphSuccessHasSparseBudget`:
  for any successful parse of the original gamma graph word,
  `twoPerEdge m <= encodingSize word`.
- `Karp21FinFreePairwiseQuadraticCountExact.maxAddressComparisonsClosed`:
  `maxAddressComparisons m = 2*m*(m-1)` for the actual pairwise address loop.
- `EfficientRecoverableQuotientExact.PolynomialBound`,
  `PolynomialBoundClosureExact.productPolynomialBound` and
  `constantMultiplePolynomialBound`.

The new theorem first derives `m <= inputBitLength`, then
monotonicity of the original comparison count. It proves

```
maxAddressComparisons m
  <= maxAddressComparisons (encodingSize word)
  <= 2 * (encodingSize word)^2
```

for every original successful raw graph read, with a native
degree-two `PolynomialBound` witness. This is independent of
declared `n`, even for a graph with a huge binary vertex count
and one edge.

**Precisely not paid:** each binary vertex-equality test's
bit-operation cost; gamma and zigzag parsing in a fully specified
binary tape machine; signed score/threshold arithmetic cost;
strict full-word verification and compiler machine clock; actual
`PR.polynomialTimeVerifier` for N21; Agda 2.9/parallel_checker
kernel acceptance. These remain original K03/K05/K06/K07 gates.
Independent Python arithmetic checked 63,001 finite (m,L) pairs
with 2m <= L for m <= 250, L <= 500; this is not kernel evidence.

## 2026-11-07 — total original N21 comparison-count resource bound

The original-word N21 owner now defines `actualAllWordComparisonCount`
on *every* binary graph word, returning zero endpoint comparisons on
malformed raw input and the original `maxAddressComparisons m` after a
successful parse. It proves `allWordComparisonCountBound` and
`allWordComparisonPolynomialClock` from the source-owned read/parser,
2m witness budget and native degree-two polynomial witness.

This completes the **input-length polynomial endpoint-comparison-count
subgate** without assuming n <= input-length or inventing any generic
verifier cost oracle. The original `Karp21BinaryRuntimeEverything` and
`Karp21Everything` roots import the new owner.

Still required for full K05: native binary-value parsing and signed
addition/equality bit costs, executable bit-tape instruction count,
formal machine simulation and original `PR.polynomialTimeVerifier`
instantiation. All new proofs remain source-written until checked by
Agda 2.9 via the repository's parallel checker. No P != NP claim.

## 2026-11-07 — rediscovered original all-word N21 semantic equivalence

PR #1445 already contains the SOURCE-WRITTEN universal theorem
`Karp21FinFreeAllWordDecoderAgreementExact.n21FinFreeVerifierSameWord`.
It proves that the actual original typed N21 graph parser/verifier and
the actual fin-free verifier return the same Boolean for *every*
original binary graph word and *every* certificate word, including
malformed words. This is considerably stronger than the older
conditional E20 image equivalence. No different graph language or
oracle is introduced.

New owner `Karp21N21SameWordCountedAcceptanceExact` consumes this
exact original theorem and the new native `ERQ.PolynomialBound` for
the same original word's endpoint-comparison count. Its
`allWordsSameVerifierAndPolynomialComparisonCount` packages both
facts without extra assumptions, and both original `Karp21Everything`
and `Karp21BinaryRuntimeEverything` import it.

**Updated K06 source status:** original N21 all-word Boolean
semantics are **SOURCE-WRITTEN** (including malformed graph and
certificate words), not still awaiting a new semantic proof.
**Remaining K06:** kernel acceptance, original E20 output compiler's
fully costed all-word map and Cook–Levin transitive acceptance.
**Remaining K05:** binary tape step cost of gamma/signed parsing,
comparisons, signed score, and the explicit machine clock. The
operation-count polynomial does NOT turn unary Nat operations into
binary constant-time primitives.

## 2026-11-07 — original raw graph validator cost folded into N21 cut

Two new source-written ORIGINAL-source modules (imported by original
Karp21Everything and Karp21BinaryRuntimeEverything):

- `Karp21FinFreeRawValidatorComparisonCountExact` instruments the
  ACTUAL `Runtime.validRawEdges` decisions `u<v`, `v<n` and
  original `Graph.strictAfter`. `originalRawValidatorValueSame`
  states literal Boolean equivalence on any raw edge list, including
  invalid/unsorted/over-range edges. The actual short-circuiting
  validation count is at most `3*m` top-level predicates.
- `Karp21FinFreeOriginalGraphComparisonEnvelopeExact` composes
  the validation count with the genuine `2m(m-1)` original sparse
  history endpoint-equality count. For every original successfully
  parsed graph word of length L, it proves the combined count is
  bounded by `C(L)+5L` primitive comparisons, where `C(L)=2L(L-1)`.
  Thus the combined number of address/order comparisons is bounded
  by the explicit polynomial expression `2L(L-1)+5L`.

No separate fabricated finite graph verifier is introduced.
This joins the source-level original decision and address-operation
resource accounting. It is NOT yet a binary bit-operation or Turing
machine polynomial clock: gamma parsing, comparisons on arbitrary
binary integers, signed cut arithmetic, all malformed parser branches,
actual strict clock instantiation and Agda acceptance remain to pay.

**2026-11-07 comparator-cost correction:** The source's `Graph.strictAfter`
contains up to three primitive Nat comparisons (a<u, a=u, b<v),
not one. The independent `countedStrictAfter`, `strictAfterValueSame`
and `strictAfterPrimitiveCountBound` follow those exact branches.
`countedRawValidatorPrimitive`, `primitiveValidatorValueSame`
and `primitiveValidatorCountBound` now count the original u<v,
v<n and strictAfter's internal comparisons, yielding 5m rather
than the 3m *top-level predicate invocation* bound. The combined
original successful-word envelope is the corrected
`2L(L-1)+5L`. This is still not binary machine time.

## 2026-11-07 — all-original-input N21 primitive-count polynomial

The previous *successful graph word only* comparison envelope has now
been strengthened without changing the original parser or graph domain.

- `Karp21FinFreeAllWordValidationClockExact`: mirrors the ACTUAL
  `readRawGraphWord` original gamma(n), gamma(m), 3m guard,
  raw-edge read and positive W/suffix branches. It counts original
  primitive raw-validator comparisons **even when that validator
  rejects** a malformed graph, and proves for EVERY binary input word
  `rawValidationCount(word) <= 5 * encodingSize(word)` from the
  literal original source `readGammaSuffixWithinInput`,
  `readRawEdgesCountExact` and 3m guard.
- `Karp21FinFreeOriginalGraphComparisonEnvelopeExact`:
  `allWordCombinedComparisonCount = original sparse consistency count
  + original raw validator primitive count`; proves
  `allWordCombinedComparisonBound` against
  `C(L) + 5L = 2L(L-1) + 5L` and constructs an ACTUAL
  `ERQ.PolynomialBound` with coefficient 7/exponent 2:
  `count(word) <= 7*(1+L)^2` universally.
- `Karp21N21SameWordCountedAcceptanceExact` now packages that exact
  all-original-word primitive count with the original universal N21
  typed/fin-free same-word Boolean theorem. In both Karp source roots.

This is the strongest sound **operation-count** result of this tranche.
It does NOT yet provide a proper bit-machine runtime: decoding
`Nat` into unary values, binary comparisons and signed arithmetic
cannot be treated as unit-cost steps. Nor does it typecheck itself
without the exact Agda 2.9/parallel_checker receipt.

**Updated K05 status:** original N21 raw validation + endpoint-history
primitive-comparison count now SOURCE WRITTEN with an all-input
native quadratic polynomial witness. Remaining: binary implementation,
each arithmetic operation's bit-cost, end-to-end parser/score runtime,
and original PolynomialCostModel/InNP certificate.
**Updated K06 status:** original same-word verifier semantics source
written, kernel acceptance and full E20/Cook compiler still pending.

**Literal-source guard and referee:** The all-word raw-validator
clock follows the original `m * 3` header guard exactly; this
is deliberately not replaced by `3 * m` in Agda's dependent
`with` branches. `m <= m * 3` is proved separately using native
Nat order. The original `Graph.strictAfter` three-case decision
tree is preserved and its internal primitive comparisons counted.

A retained source-aligned independent Python model checked 26,214
small original `strictAfter`/raw-validator input cases, with literal
Boolean agreement and `cost <= 5m`. The repository's existing
`referee_karp21_maxcut.sh` now executes this regression in preflight,
alongside the prior 63,001 comparison-budget cases. These are
differential tests only, not Agda kernel acceptance or a Turing-machine
clock. The new all-word N21 sources are on PR #1474.

**Agda source-alignment repair:** `Karp21FinFreeAllWordValidationClockExact`
uses the EXACT original header guard `m * 3` and an explicit
`inputListLengthIsWordSize` proof because the original gamma parser
uses `Data.List.length`, while the existing complexity model uses
`FiniteWordSizeExact.encodingSize`. No definitional equality between
two separately recursive owners is assumed. This and the original
strictAfter internal primitive-guard proof are part of the exact-head
compiler acceptance cut, not already certified.

## 2026-11-06 — K05 N21 bit-weighted comparator and real bitword equality

Actual original Karp owners:
- `Karp21FinFreeOriginalGraphComparisonEnvelopeExact`:
  original graph-word raw-validator + endpoint-history comparison count for
  ALL words, including malformed, bounded by a degree-two polynomial.
- `Karp21N21SameWordCountedAcceptanceExact`:
  reuses `Karp21FinFreeAllWordDecoderAgreementExact.n21FinFreeVerifierSameWord`.
  The exact original fin-free and typed N21 Boolean verifiers agree
  for all literal graph/certificate words.
- New `Karp21N21BitWeightedComparisonEnvelopeExact`:
  charges each of the ORIGINAL counted primitive-comparison slots
  `1+Word.encodingSize word`; constructs a genuine native
  `ERQ.PolynomialBound` on the product envelope (degree three by
  product closure) and proves the all-word weighted bound.
  Its `OriginalN21ComparisonImplementationClock` contract is a real
  separate proof premise; there is NO supplied inhabitant for the
  original comparator's bit-machine implementation.
- New `Karp21BinaryWordEqualityPrimitiveExact`:
  actual structural bitword equality function with extensional
  soundness and completeness, exact bit-inspection count, and
  upper bound `1+length left` independently of decoded numeric
  magnitude. This is a comparator candidate on bit representations;
  the gamma-decoded Nat equality interface has NOT been swapped
  for this implementation or proved definitionally identical.

Existing original `Karp21BinaryRuntimeEverything` and
`Karp21Everything` import the weighted-count and comparator
sources; the Golden referee checks both additional focused roots.
Independent exhaustive reference: all 16,129 binary word pairs
of lengths 0..6 passed equality/inspection-count checks, executed
locally; the equivalent committed Python reference runs in preflight.

What is now exact at SOURCE level:
  primitive comparison count <= 7(1+L)^2;
  scheduled bit-weighted comparison count <= 7(1+L)^3;
  extensional equality and bit inspection cost for a selected
  separately defined binary-word comparator.

**Decisive remaining original-owner weld**:
  1. Preserve gamma payloads or reconstruct canonical binary operands,
     prove each original `NatP._≟_` / `NatP._<?_` /
     `Graph.strictAfter` result agrees with the selected
     bit-native comparator on ALL parsed inputs.
  2. Prove that operand descriptions inspected by original graph
     parsing are each O(L) bits, including malformed rejected paths.
  3. Prove concrete machine-clock costs for original gamma parsing,
     signed zigzag/large-integer addition and threshold comparison,
     certificate read and storage.
  4. Combine these into a true all-word N21 polynomial verifier,
     instantiate the original `PR.InNP` resource model and
     obtain `parallel_checker` kernel acceptance.
  5. Complete original E20 all-word bit transducer clock, guarded
     Cook–Levin and the remaining historical network.

The new degree-three expression is a polynomial schedule, NOT an
unconditional Turing-machine execution bound; no false claim that
native Agda `Nat` equality is constant time.

## 2026-11-07 — binary-native gamma and signed token readers

A concrete resource defect was identified in the original executable
`Karp21GammaZigzagPartitionWordDecodeExact.readGamma`: it
reconstructs `pow2 zeros` and the full decoded magnitude as Peano
`Nat`. A source proof of gamma token count alone is insufficient
to assert polynomial execution of that original implementation.

New:
- `Karp21GammaBinaryNativePayloadExact`:
  `readGammaBinary`, `readPayload` and `scanZeros` operate on the
  source's real `FiniteWordSizeExact.BitWord` and return the binary
  `n+1` representation plus the literal remaining suffix, without
  forming `n` as Peano `Nat`. `gammaOriginalEncodeNativeSuffix`
  proves the native parser reads outputs of the ORIGINAL Elias-gamma
  encoder. `gammaNativeInspectionLinear` proves its all-input
  recursive source-inspection work ≤1+input length, malformed
  strings included.
- `Karp21GammaBinaryNativeSignedExact`:
  `splitLast` and `readSignedBinary` directly derive the sign and
  magnitude of a signed zigzag value from `n+1`'s last binary bit:
  last=1 means nonnegative, last=0 means negative; preceding bits are
  floor((n+1)/2). `readSignedOriginalGammaEncodedExact` proves the
  original encoder-image bridge, and `splitLastInspectionLinear`
  bounds the structural inspections for the magnitude extraction.

Independent reference tests ACTUALLY EXECUTED: all 8,191 binary
strings with length ≤12 for each binary gamma and signed parser;
both agreed with the old numerical/zigzag parser and suffix on
every well-formed token and rejected every malformed token, and
the gamma inspection bound held. Retained
`scripts/check_karp21_gamma_binary_native*.py` are wired to the
original referee, with focused Agda roots in golden mode.

Still **not a full bit-machine clock**: all-input numerical
equivalence of the new binary reader to the original mathematical
`readGamma`; canonical binary comparison `<` and `strictAfter`;
multi-token graph parser; encoded endpoint bounds; signed binary
addition and threshold comparison; certificate loop; input/output
tape motion; E20 and original Cook–Levin. Neither these source
proofs nor the finite regressions are Agda-kernel certificates.

## 2026-11-07 — all-word native gamma numeric-observation equality

`Karp21GammaBinaryNativeAllWordNumericalWeldExact` is the original
gamma decoder's full input-domain source bridge, not only an
encoder-image or finite-regression statement.

- `readPayloadNativeNumericalSameAllWords` proves that reading
  k low bits into a native binary payload and interpreting that
  payload yields the exact source-owned `readLowBits` numeric value,
  with the same suffix, for every word and every k.
- `scanNativeNumericMatchesOriginal` lifts it through the literal
  `readGammaZeros` prefix scanner, including failure branches.
- `originalGammaSameAllWordNumericalObservation` identifies the
  complete original `readGamma` with a numeric OBSERVATION of
  the native grammar for every input word.

The normal N21 verifier must execute the binary parser, NOT the
numeric observation, which is used in Agda proof terms only.
The native signed-last-bit parser's corresponding all-word
numeric observation and the original `strictAfter` less-than
bridge are next. A full polynomial bit-tape clock still needs
signed big-integer operations, full graph/certificate loops
and machine-step correspondence. This source awaits Agda 2.9
kernel acceptance.

## 2026-11-07 — native gamma strict validity equivalence

New `Karp21GammaBinaryNativeAllWordValidityExact` closes a
different, direct all-word property:
`accepted (Native.readGammaBinary w) ≡ accepted (Old.readGamma w)`
for EVERY original literal bitword `w`, including early rejection,
truncated prefix/payload, and suffix-bearing words. The theorem
uses the native branch-control scan plus the previously written
all-word numeric-observation equality; the executable branch never
constructs `pow2`-sized Peano values.

The selected original N21 focused runtime and overall Karp21 root
import this source, and the unchanged-original referee flow now
checks its focused Agda owner. No claim of Agda kernel acceptance
without the original `parallel_checker` receipt.

Remaining exact machine gates have not changed: native binary
less-than for endpoints and canonical `strictAfter`, signed
accumulation, multi-token graph parser and certificate, exact tape
movement, `PR.polynomialTimeVerifier`, E20 clock, Cook–Levin
uniform compiler, historical network, and independent SAT lower
bound for P != NP.


## 2026-11-09 FRACDASH machine integration

Dedicated roadmap: [Karp21FRACDASHMachineMaxCut20261109.md](Karp21FRACDASHMachineMaxCut20261109.md).

New original-head `Karp21FractranPriorityFrontierExact.agda`: generic source-written `--safe` first-enabled FRACTRAN guard-cache refresh correctness and successor/halt preservation, under explicit unaffected-guard stability premises. Imported in both original Karp roots; focused Golden referee covers the new source.

This is *not* an original N21 instantiation or a polynomial-time Turing-machine witness. Preserve the existing gamma reader, signed ledger, trace factors, endpoint trie, original `rawSparseScore`, and original `PR.InNP` ownership. Exact unpaid lemma phases and FRACDASH source/attribution details live in the linked roadmap. Agda 2.9/parallel_checker acceptance OPEN; E20, Cook–Levin, remaining edges/memberships, independent SAT lower bound OPEN.


## 2026-11-09 continuation — original N21 endpoint/score guarded machine vertical slice

New original-owner integration `DASHI/Mathematics/Complexity/Karp21FractranN21EndpointScoreStepExact.agda` **actually imports** `Karp21FinFreeRawSparseWordVerifierExact.endpointConsistent`, `Karp21BoolGoldenExact.boolEqual`, the real `Karp21GammaBinaryNativeSignedExact.SignedMagnitudeBits`, the executable `Karp21BinaryNativeSignedLedgerExact.insertSigned`, and the FRACDASH-style `Karp21FractranPriorityFrontierExact.Machine`.

The source-written `N21Edge` instantiation fixes one original edge's u/v, certificate labels a/b, original chronological endpoint history and decoded binary signed weight. It exposes a **genuine priority-ordered two-rule machine** (`advance`, then `reject`) with first-rule guard equal to the original endpointConsistent checks and continuation status. Its rule action updates the binary positive/negative ledger if and only if original `boolEqual a b` is false. The fallback rejects. `karpFractranFirstEnabledSameN21EdgeStep` states exact same-step on this **one-edge original-guard score phase**. `unaffectedStable` is proved by case analysis on the concrete status-change dependency, and `scoreOnlyUnaffected`/ `scoreOnlyGuardStable` certify score-only binary updates cannot alter fixed endpoint guards. `karpN21CachedScoreUpdateSameStep` transports the generic first-enabled cached-step theorem to this concrete frame.

This is strictly narrower than `karpFractranFirstEnabledSameVerifierStep` on ALL original N21 words. The original `rawSparseScore` recursively validates the entire history and sums `Graph.RawEdge.weight : ℤ`, while this local machine consumes one native signed bit token. **Unpaid:** original gamma signed token value/suffix equality; one-edge raw signed-ℤ to native lane correspondence; induction over whole edge list and 2m certificate; parser malformed/suffix behavior; exact acceptance and trace replay; fully costed bit-machine verifier; `PR.InNP`. The local state does not assert a global graph cursor or output acceptance.

The module is imported by both original Karp roots and checked by `referee_karp21_maxcut.sh e20/all`; a bounded differential `scripts/check_karp21_fractran_n21_edge.py` is run in preflight. A local independent source-shaped Python reproduction passed **13,440** cases (two vertex addresses, both labels and live statuses, five signed weights, endpoint histories of length up to two, two small ledger lanes); conflicting-label negative control passed. This evidence **does not** typecheck Agda or prove the original word-level theorem.

**Phase ledger:** P0.2 = source-written concrete endpoint/score phase, **not full graph rules**. P0.3 = local first-enabled same-step SOURCE, full `karpFractranFirstEnabledSameVerifierStep` OPEN; P0.6 bit clock OPEN; all downstream P0–P3 remain OPEN. Exact-head Agda 2.9 and parallel_checker receipt not obtained.


## 2026-11-09 — Full original raw-score selected-trace reconstruction and all-word acceptance (SOURCE ONLY)

**New owner:** `DASHI/Mathematics/Complexity/Karp21FractranOriginalRawTraceReplayExact.agda`.

The runtime `rawSelectedTrace` traverses the ORIGINAL `Graph.RawEdge` list and the original **exactly two certificate bits per edge**, applies the original `Runtime.endpointConsistent` (including chronological history extensions) and `Boolean.boolEqual`, and emits just those original signed `ℤ` weights whose labels differ. It rejects inconsistent or short/long certificate lists with `nothing`. `replayOriginalSignedTrace` folds the original signed weights. Proposed source-written `rawSelectedTraceRebuildsOriginalScore` proves the full all-raw-list equality `decodeTraceScore (rawSelectedTrace edges bits history) ≡ Runtime.rawSparseScore edges bits history` via structural induction, including malformed bit lengths, all signed weights, and arbitrary histories.

The same source additionally defines `verifyOriginalGraphWordByTrace` using **the actual original** `Runtime.readRawGraphWord` rather than a replacement graph parser; `karpOriginalRawTraceAllWordAcceptance` is a source-written theorem asserting Bool equality against `Runtime.verifyFinFreeSparseGraphWord` for *every original graph-word and certificate bitword*. This is a trace/replay equality at the ORIGINAL `ℤ` representation, not native signed-gamma value equivalence, a binary FRACTRAN runtime, or a bit-machine complexity result.

**Independent executable evidence:** `scripts/check_karp21_fractran_original_raw_trace.py` reproduced the literal source-level branch order and checked **449,895** bounded raw edge/certificate cases (0–3 edges, small signed weights including negative, conflicting endpoint histories and malformed certificate lengths): 8,257 accepted, 441,638 rejected, all replayed decisions/scores agreed. This is a Python transcription of the original raw-language semantics, not direct execution of Agda, and does not test the complete all-word parser. Added to existing Golden roots and referee.

**Exact authority:** source-written proof candidate, **no Agda 2.9 kernel receipt**. The full target `karpSignedIRSameOriginalSparseScore` is STILL OPEN because the native binary sign/magnitude token values and gamma suffix must be welded to the original `ℤ` weights. The stronger `karpFractranFirstEnabledSameVerifierStep` is ALSO OPEN beyond the preceding one-edge original-guard instance. All-word original-ℤ trace acceptance is source-written but native-binary all-word acceptance is not. Full original N21 bit-machine clock, `PR.InNP`, E20, Cook–Levin and remaining Karp-21 reductions/memberships remain open.

**Next tight cut:** prove the actual original `readSignedGamma` / `readRawEdges` to native binary token value-and-suffix equivalence; use a mathematical signed-lane observation bridge to map replayed native selected tokens to this exact original signed selected trace; then instantiate a true bit-tape step bound and the original `PR.InNP`.


## 2026-11-09 continuation — original typed N21 all-word trace composition and paired binary projection

New source-written `Karp21FractranOriginalTypedTraceAcceptanceExact.agda` composes the existing source-owned `Karp21FinFreeAllWordDecoderAgreementExact.n21FinFreeVerifierSameWord` and `Karp21FractranOriginalRawTraceReplayExact.karpOriginalRawTraceAllWordAcceptance`. Its declaration `karpOriginalTraceSameTypedN21AllWords` states that the original signed-ℤ selected-trace evaluator has exactly the same Bool as `Graph.LiteralN21.verifyCanonicalSparseGraphWord` for all original graph words and certificate words, malformed included. **Composition of source-written theorems only, Agda kernel receipt not received.**

New `Karp21FractranPairedBinaryTraceExact.agda` retains each original `Graph.RawEdge` together with its corresponding actual `SignedMagnitudeBits`, preserving the original endpoint `Runtime.endpointConsistent` and `Boolean.boolEqual` selection and certificate-history update. `pairedTraceProjectsToOriginal` source-writes original signed-ℤ trace recovery for every aligned paired raw-edge list, arbitrary original history and certificate, with rejection exact. `pairedTraceOriginalScoreExact` composes this projection with the original `rawSparseScore` reconstruction. Native tokens can be projected for ledger replay without losing pairing identity. Neither theorem falsely presumes token magnitude/value equals the original signed-ℤ weight: **that equality is still a separate, open signed-gamma graph-reader weld.**

All sources are imported into both original Karp roots, and the exact-head referee checks each of them in e20/all. Local Python scripts already mounted in the runtime were directly executed this continuation: raw signed-score trace 449,895/449,895, original edge-guard phase 13,440/13,440, and priority frontier 38,860/38,860; passing tests are NOT Agda receipts.

**Remaining exact maximum cut**: (i) original graph signed-gamma `readRawEdges` → native binary signed token/suffix equality for all input words; (ii) original signed weight ↔ native signed value and threshold `P ≥ N+W` equality; (iii) use the paired full-edge trace to prove the actual native binary ledger and full FRACDASH step agree with `rawSparseScore` and the original typed N21 Bool for all words; (iv) bit-TM clock with parsing, update, selection, storage, motion and residual costs; (v) original `PR.InNP`; (vi) E20 and Cook–Levin; (vii) E01–E19/N01–N20 and `CertifiedKarpNetwork`; (viii) exact-head Agda 2.9/parallel_checker. These remain OPEN. The new source is *not* a verified NP-completeness proof.


## 2026-11-09 — P-vs-NP PR #1129 cross-pollination: executable verifier code transport

**Audited original `chboishabba/dashi_agda` PR #1129** (`agent/pnp-maxcut-20261012`, observed head `730ec95ce0442b8ab48a17a3cc9a3d1307ba8c76`) and the branch's existing `PNotEqualsNPExecutablePolynomialCostRefinementExact`, `PNotEqualsNPClayCoreExact`, `PolynomialReductionExact`, and original `Karp21SparseGraphWordNPBoundaryExact`. The P-vs-NP branch already distinguishes extensional `polynomialTimeVerifier` from executable finite code, actual halting versus estimated upper bound, and independent `SATNotInP` lower-bound obligations. **Do not mistake its behavioural self-specialization interfaces or Cook quotation boundaries for a proved SAT lower bound.** The existing Karp NP boundary already explicitly requires a physical verifier clock and certificate-bound witness to construct `PR.InNP`.

**New actual reuse, not a duplicate cost model:** `DASHI/Mathematics/Complexity/Karp21FractranPvsNPVerifierCodeTransportExact.agda` imports the SOURCE P-vs-NP `ExecutableVerifierCode` carrier, original typed N21, and this branch's all-word original signed-ℤ trace theorem. `karpTraceCodeRealizesOriginalTypedN21` transports a real concrete code, its interpreter, and its `codeSize` field from original trace verification to the actual typed N21 verifier. `karpTypedCodeRealizesOriginalTrace` transports the other way. Both update only `runExact` by transitivity/symmetry of the source-owned all-word Boolean equality; they do **not** synthesize a tape program or clock. `karpTraceRefinedToOriginalTyped` transports a P-vs-NP `ExecutablePolynomialTimeVerifier` *only when a separate original typed-verifier polynomial-time witness has been supplied*. This refuses to postulate that extensional code or numerical comparison count equals a bit-Turing-machine runtime.

The new module is imported by the original `Karp21Everything` root (not marked `--safe`, matching the historical P-vs-NP import closure) and checked by `referee_karp21_maxcut.sh e20/all`. The previous `Karp21FractranPairedBinaryTraceExact` had a missing `sym` import in its all-list proof; that import was repaired. Exact-head Agda 2.9 and `parallel_checker` unavailable here.

**Actually executed** bundled Python scripts in this working container this continuation: `check_karp21_fractran_priority_frontier.py` 38,860 PASS, `check_karp21_fractran_n21_edge.py` 13,440 PASS, `check_karp21_fractran_original_raw_trace.py` 449,895 PASS. These finite source-shaped tests are not Agda kernels or end-to-end N21 binary parser tests.

**Exact remaining maximum cut, unchanged by code-transport:** source signed-gamma `readRawEdges` and native bit-token value/suffix alignment; binary two-lane numeric representation equal to original signed-ℤ `rawSparseScore`; actual complete N21 FRACTRAN first-enabled original machine; native all-word acceptance and residual trace reconstruction; concrete bit-machine execution/bit width/heap/tape/head/priority-frontier polynomial cost; `PR.polynomialTimeVerifier` and original `PR.InNP`; E20, Cook–Levin original Cell/Bits and remaining E01–E19/N01–N20 network; independent behavioural self-specializer and resource fixed point to derive `SATNotInP` in separate P-vs-NP lane. Source written ≠ kernel accepted ≠ Clay result.

**Provenance:** Stephen Cook, Leonid Levin, Richard Karp, Elias gamma/Conway FRACTRAN; reuse of repository's original PR #1129 and PR #1445 authorship and FRACDASH compiled-machine work. No ESD paths touched.


## 2026-11-09 — Signed-gamma original/native all-word suffix and numerical-control cut

Canonical up-to-date status table and exact lemma chain: [Karp21FRACDASHMachineMaxCut20261109.md](Karp21FRACDASHMachineMaxCut20261109.md).

New `--safe` Agda source owner `Karp21GammaBinaryNativeSignedSuffixExact` directly reuses original gamma/zigzag, native gamma/signed parsers and the existing unsigned numerical weld. The code source-writes `nativeScanNumericSuffixSame`, `nativeGammaOriginalSuffixAllWords`, `nativeSignedSuffixEqualsNativeGamma`, `karpNativeSignedGammaSuffixSameOriginal` and `karpSignedNativeControlNumericViewSameOriginal`. Every input bitword is included, including malformed, truncated and suffix-bearing words. This **closes only the suffix branch at SOURCE level** and gives original-ℤ numerical observation of the native grammar's control path. It **does not prove actual executable signed-token `valueLE (reverse magnitude)` equals old `unzigzag`**. That token-value theorem and the original graph `readRawEdges` frame are the next precise gates.

Both original Karp roots and focused Golden referee import the owner. `scripts/check_karp21_signed_gamma_suffix_values.py` is in preflight; a local independent direct execution matched original/native value, sign, suffix and failure in **65,735 finite cases**, including 200 large inputs; this is regression evidence, not Agda semantics or polynomial runtime. Exact-head Agda 2.9 and parallel_checker are unavailable. All the original full native binary ledger/score, complete FRACTRAN N21 machine, polynomial bit-machine clock, N21 `PR.InNP`, E20/Cook–Levin, remaining network and P-vs-NP `SATNotInP` remain OPEN. Do not promote a finite test or the proof-only numeric observation into a code-to-proof execution receipt.


## 2026-11-09 exact original gamma payload / native ledger rejection cut

**Source-written and not kernel accepted:** `Karp21GammaBinarySignedPayloadValueCutExact.agda` computes the actual native `Signed.readSignedBinary` and original `Old.readSignedGamma` on the same complete source gamma frame with the exact unchanged suffix. It covers arbitrary nonempty successor payloads ending in either sign bit, plus a separate gamma-zero fixture. This is NOT the signed numerical value equality: the next required lemma equates `Value.valueLE(reverse (true ∷ prefix))` with the original `Old.unzigzag` magnitude formula, handling zero and both signs. All-word malformed/truncated suffix preservation is covered by the preceding signed-gamma suffix owner.

**Real native execution and rejection theorem:** `Karp21FractranPairedBinaryTraceExact.agda` now contains `nativePairedLedger`, which runs the actual `Ledger.accumulateSigned` over the selected native tokens after original endpoint/history and 2-bit certificate checks. `nativePairedLedgerSameOriginalRejection` source-writes same success/rejection as the actual original `Runtime.rawSparseScore` on **all supplied aligned raw-edge/token lists and all certificates**, without assuming unproved token numeric equality. It does NOT validate that supplied paired binary tokens were decoded from the original graph word; that original graph-reader weld remains unpaid.

Both source owners are reached through existing Karp Golden imports; signed payload owner additionally referenced in focused referee. Existing finite regression scripts directly rerun in the working container: 38,860 priority, 13,440 N21 edge and 449,895 original raw trace cases PASS. These tests are not Agda typechecks or full original/native binary score tests. Agda 2.9/parallel_checker unavailable. Current phase/status table and precise arithmetic obligation live in `Docs/roadmaps/Karp21FRACDASHMachineMaxCut20261109.md`. Original `PR.InNP`, E20, Cook–Levin, Karp network and independent P-vs-NP SAT lower bound remain OPEN.


## 2026-11-09 — Actual N21 signed-token numerical theorem and decisive remaining cut

Three new actual Agda arithmetic owners are committed on original Karp PR #1474:

1. `Karp21SignedGammaNumberTheoryExact`: source zigzag (2M/2M-1) positive/negative correction, including nonzero negative magnitude.
2. `Karp21SignedGammaBinaryValueArithmeticExact`: source original gamma BE `payloadValue` = actual native ledger `Value.valueLE(reverse bits)`; sign-bit append doubles magnitude; proves a leading-one magnitude is `suc k`.
3. `Karp21SignedGammaNativeOriginalValueExact`: `interpretNativeToken` uses the **actual** signed token's bit value, and `karpNativeSignedTokenValueMatchesOriginalEncodedFrame` source-writes exact equality of the original signed-ℤ `readSignedGamma` and the native signed binary decoder's numeric observation on EVERY COMPLETE original gamma frame, arbitrary positive/negative sign bit, prefix, suffix; separate gamma-zero theorem. Not just agreement on acceptance/suffixes.

**Status:** all new declarations **SOURCE-WRITTEN only**, Agda 2.9/`parallel_checker` exact-head unavailable; no kernel-green claim. A same-source numerical regression passed **66,334** independent finite cases for 0–14 prefix bits and 128–2048-bit additional magnitude tests, including negative and positive. This is not an Agda receipt.

**Do not overpromote:** the full all-input-word numerical weld is still OPEN until successful frame decomposition and original `Graph.readRawEdges` to native word/cursor/weight alignment are proved. The actual native two-lane signed-score equality to `rawSparseScore`, full original N21 compiled FRACTRAN simulation/acceptance/trace, physical polynomial bit-machine clock, original `PR.InNP`, E20/Cook–Levin, remaining Karp-21 edges and memberships, and separate P-vs-NP behavioural fixed point/resource lower bound `SATNotInP` remain OPEN.

The [canonical current phase and deliverables roadmap](Karp21FRACDASHMachineMaxCut20261109.md) has an IN-PLACE authoritative P0-A…P0-G, P1, P2, separate P-vs-NP and Golden lemma table. Earlier chronological OPEN entries in these documents may be historical and do not supersede the new canonical table. Original attribution preserved; no ESD files edited.


## 2026-11-09 — Full original signed-gamma native numerical equality: SOURCE-WRITTEN

Original PR #1474 now includes `Karp21SignedGammaAllWordFrameExtractionExact.agda`: actual native `readPayload`/ `scanZeros` successful-parse proof of the original gamma zero-prefix, exact length, leading-one, payload and suffix. `Karp21SignedGammaNativeOriginalValueExact.karpNativeSignedTokenValueMatchesOriginal` composes this with the genuine BE original payload / LE `Value.valueLE(reverse)` numerical arithmetic, original zigzag positive and negative (2M)/(2M-1) identities, gamma-zero case and all-word failure/suffix theorem. The declared result is equality of the optional **actual native signed token's observed ℤ integer and suffix** with original `Old.readSignedGamma` for all input bitwords. No fabricated value oracle. **Source-written, not Agda 2.9 kernel-checked.**

A separate source-aligned numerical differential passed **66,334 cases** including 2048-bit magnitudes; it is not a compiler receipt. The authoritative IN-PLACE [max-cut P0-A…P0-G, P1/P2 and separate P-vs-NP exact-lemma table](Karp21FRACDASHMachineMaxCut20261109.md) identifies **P0-B actual original `Graph.readRawEdges` native cursor/weight/endpoint weld** as next, then P0-C signed ledger versus original `rawSparseScore`, P0-D/E full N21 FRACTRAN machine/acceptance, P0-F bit-Turing polynomial time, P0-G original `PR.InNP`, P1 E20 and Cook–Levin, P2 remaining Karp network, separate P-vs-NP behavioural self-quotation/resource argument and `SATNotInP`. These remain OPEN. Attribution and Golden theorem authority preserved.


## 2026-11-09 source refresh — exact phases and new P0-C/E20 owners

Canonical up-to-date gate ledger: `Docs/roadmaps/Karp21FRACDASHMachineMaxCut20261109.md` (CURRENT CANONICAL PHASE / DELIVERABLE / EXACT-LEMMA CUT). Existing branch source `Karp21SignedGammaNativeOriginalValueExact.karpNativeSignedTokenValueMatchesOriginal` already asserts **all-word actual SignedMagnitudeBits ↔ original signed-ℤ result**, and `Karp21SignedGammaNativeRawEdgeStreamExact.nativePairedRawEdgesSameOriginal` already asserts original raw signed-edge stream identity, subject to exact-head Agda 2.9 kernel check. New `Karp21SignedGammaNativeItemStreamExact` source-writes `nativeObservedItemsSameOriginal` and `nativeObservedPartitionSameOriginal` on the ACTUAL signed-token parser plus proof-side values, original count and strict suffix rejection. New `Karp21NativeSelectedSignedScoreExact` source-writes `selectedTraceRetainsNativeNumericalAlignment`, `alignedSelectedSignedSum`, `nativeAlignedScoreSameOriginalRawSparseScore`, `nativeRawEdgeStreamIsAligned` and `nativeRawStreamSignedScoreSameOriginal`, carrying original signed-ℤ numerical score from ACTUAL native gamma raw-edge stream through original endpoint guard, two-bit certificate and selected cut traces.

**Not yet paid:** actual two-lane signed binary ledger numerical interpretation equals native ℤ trace sum; native bit-oriented endpoint/count and complete graph header/threshold; complete N21 FRACTRAN same-step, output/readout and trace; bit-tape physical polynomial clock; original `PR.InNP`; E20 fully bit-native costed compiler, Cook–Levin, all 21 historical NP reductions/memberships; separate behavioural fixed-point resource lower bound `SATNotInP`. Signed source semantics must not be mistaken for executable cost. All changes imported into Golden roots, focused referee updated; exact-head Agda 2.9/parallel_checker **not run/receipt OPEN**. No P≠NP proof claimed.


## 2026-11-09 latest P0-C: ACTUAL native two-register signed score ↔ original rawSparseScore

Canonical source-of-truth: `Docs/roadmaps/Karp21FRACDASHMachineMaxCut20261109.md` CURRENT CANONICAL PHASE table (supersedes older chronological OPEN rows).

New `Karp21NativeLedgerIntegerScoreExact.agda` imports real `Karp21BinaryNativeSignedLedgerExact.accumulateSigned` and existing `accumulateEmptyPositive`/`accumulateEmptyNegative`; `integerPositiveStep`, `integerNegativeStep`, `negativeTokenInteger`, `tokenClassesEqualOriginalSignedTrace` and `nativeSignedLedgerIntegerEqualsOriginalTraceScore` source-write the binary two-register numerical observation `(+ P) + (- (+ N))` as the exact signed ℤ token fold. Neither the executable parser nor accumulator performs proof-side unary-Nat subtraction.

New `Karp21NativeLedgerOriginalRawScoreExact.agda` composes `nativeLedgerScoreMatchesNativeSelectedTrace` and `nativeSignedLedgerIntegerEqualsOriginalRawSparseScore` with actual original endpoint/history/certificate selection and parser-produced native signed edge pairs. This is source-written equality with original `Runtime.rawSparseScore` **on successfully parsed source signed raw-edge streams**, including certificate failures; it is **not** the complete original graph-word / threshold decision.

**Remains OPEN**: Agda 2.9 exact-head and parallel_checker receipts; native bit-coded endpoint and full strict graph header/positive-threshold parsing; original binary threshold-comparator numeric theorem; complete first-enabled N21 FRACTRAN step and acceptance/trace; physical polynomial bit-machine clock and actual `PR.InNP`; costed E20/Cook–Levin; original Karp-21 network; independent P-vs-NP code-consuming behavioural fixed point, resource lower bound and `SATNotInP`.

Both new owners imported into the original Golden Karp roots and added to the focused Agda referee. A new reproducible bit-ripple two-register differential is tracked at `scripts/check_karp21_native_two_lane_raw_score.py` and called during preflight. An independently executed finite numerical differential passed 454,895 cases including 256-bit weights; the committed bit-ripple version has NOT been executed under this harness yet. No new Agda kernel receipt or Clay result.


## 2026-11-09 P0-E/F same-source binary comparator cut

New source-written `Karp21BinaryNativeThresholdStructuralExact.agda` uses the genuine `Karp21BinaryNativeThresholdExact.compareLE`, proving `compareLEReflexive`, `atLeastReflexive`, `compareLESameLowBit`, `atLeastSameLowBit`, high-priority select laws and `compareInspectionLinear` (actual source recursive comparisons ≤ combined operand width +1). Its `--safe` source is imported by original `Karp21Everything` and `Karp21BinaryRuntimeEverything` and checked by focused referee. Local independent numerical three-way ordering and atLeast differential: **71,025/71,025 PASS**, including exhaustive all bitwords of length 0..7 and 6,000 random operands up to 513 bits. Committed `scripts/check_karp21_native_comparator_exact.py`, wired into `referee_karp21_maxcut.sh`.

**Exact P0-E OPEN**: `compareLENumericalCorrect` for arbitrary bitwords (regression ≠ Agda theorem); `nativePositiveThresholdParserSameOriginal`, `nativeOriginalGraphWordFieldsSame`, `karpNativeThresholdDecisionSameOriginal`, `karpFractranDecodePreservesAcceptance`, `karpFractranTraceRebuildExact`. P0-F physical bit-Turing-machine movement/allocations/bit-width clock is NOT paid by primitive inspect counts. P0-D original N21 first-enabled machine, original `PR.InNP`, original E20/Cook–Levin, Karp-21 network and independent P-vs-NP `SATNotInP` remain OPEN. Exact-head Agda 2.9 / parallel_checker not run. Canonical CURRENT table and exact phase/lemma inventory: `Docs/roadmaps/Karp21FRACDASHMachineMaxCut20261109.md`.


## 9 November 2026 continuation — P0-D/E original comparator, source positive gamma, parsed-raw FRACTRAN terminal decision

**NEW SOURCE candidate** `Karp21BinaryNativeThresholdNumericalExact.agda`: `compareLENumericalCorrect` for all original bit lists (constructive strict Nat gap trichotomy, source `Compare.compareLE`, including unequal widths and zero padding); `atLeastTrueGivesNumericalOrder`, `atLeastFalseGivesNumericalOrder` follow actual `atLeast`. **NEW** `Karp21NativePositiveThresholdNonzeroExact.agda`: native bit test `anyOneFalseMeansZero`, `anyOneTrueMeansPositive`, `readPositiveGammaLEAlwaysPositive`. **NEW** `Karp21NativePositiveThresholdNumericFrameExact.agda`: `nativePredecessorValueSameOriginalGamma` pays gamma(n+1) successor correction for actual LE binary predecessor; `nativePositiveThresholdParserSameOriginal` source-writes all-word strict original gamma-positive threshold parser/number/suffix/rejection equality (no complete graph header).

**NEW P0-D** `Karp21FractranOriginalRawListMachineExact.agda` follows complete original parsed raw signed-edge list and exactly-two-label-bits-per-edge cursor, original endpoint-history, actual binary two-lane ledger and halt/reject; `karpFractranFirstEnabledSameRawCursorStep` checks independently defined raw list transition. **NEW** `Karp21FractranParsedRawThresholdMachineExact.agda`: positive native threshold decision on terminal cursor, `karpFractranFirstEnabledSameParsedRawVerifierStep` and cache version exact **for parsed raw inputs**. No artificial promise that this is the full `Runtime.readRawGraphWord` or typed original verifier step.

63,001-case independent full parsed raw-score + positive threshold machine regression PASS (including 7,000 random cases with 128-bit signed weights), committed `scripts/check_karp21_fractran_parsed_raw_threshold.py`, wired to focused preflight; existing 71,025 comparator and 454,895 native ripple-ledger differentials PASS independently. No Agda 2.9/parallel_checker executable; **new proof declarations are NOT kernel accepted**.

Full remaining max-cut: `nativeOriginalGraphWordFieldsSame` for original n/m, strict u<v<n ordering, full suffix/threshold and sparse budget, binary endpoint representation; `karpNativeThresholdDecisionSameOriginal` for signed ℤ versus exact LE atLeast; `karpFractranFirstEnabledSameVerifierStep` on COMPLETE original graph-word decoder; all-word acceptance and trace reconstruction; true polynomial bit-machine tape/motion/allocation clock; original `PR.InNP`; costed original E20/Cell Bits Cook–Levin; Karp-21 network; separate behavioural resource proof and `SATNotInP`. Canonical current phase/deliverable and exact remaining lemma table: `Docs/roadmaps/Karp21FRACDASHMachineMaxCut20261109.md`. No P≠NP theorem.


## 2026-11-09 current P0-B/D/E/F and original P1 prior-art cross-pollination

The canonical exact remaining cut, now authoritative over historical notes, is `Docs/roadmaps/Karp21FRACDASHMachineMaxCut20261109.md`. All newly added Agdas are SOURCE-WRITTEN, **not Agda kernel accepted**.

- **P0-B/E whole original graph**: `Karp21NativeWholeRawGraphWordExact` executes original literal gamma n/m, 3m short-word guard, counted native signed raw-edge token stream, positive native gamma threshold, strict original u<v<n/sorted-unique edge validation, and no trailing bits. `Karp21NativeOriginalWholeGraphFieldsWeldExact.nativeOriginalGraphWordFieldsSame` source-writes equality of **whole same-input original Fin-free graph fields** incl. malformed rejection, consuming existing all-word signed-edge and native positive gamma source correspondences. Original Nat-producing header/endpoints/validation and bit clock remain OPEN.
- **P0-D/E original FRACTRAN machine**: `Karp21FractranOriginalRawListMachineExact` implements actual remaining original raw-edge list/certificate cursor/history/two-register score/live-rejected-finished state and ordered `advance/finish/reject` priority; `karpFractranFirstEnabledSameRawCursorStep` source-writes exact direct step. `Karp21FractranParsedRawThresholdMachineExact.karpFractranFirstEnabledSameParsedRawVerifierStep` adds actual binary positive threshold terminal decision, separate direct reference and cached refresh. **This is parsed-raw scope only; original all-word `karpFractranFirstEnabledSameVerifierStep` remains OPEN.**
- **P0-F**: `Karp21FractranParsedRawStepPotentialExact.cursorPotential`, `originalParsedRawStepStrictPotential`, `karpFirstEnabledStepStrictPotential` source-write strict decrease of remaining-edge-count+1 for every real parsed-raw first-enabled step, bounding high-level rule firings ≤ m+1. This does NOT bound original endpoint Nat decoding, bit-TM memory movement/width, tape-head operations, graph parsing and physical verifier clock.
- **P0-E numerical**: `Karp21BinaryNativeThresholdNumericalExact.compareLENumericalCorrect` source-writes ALL-WORD constructive strict Nat gap trichotomy for actual `Compare.compareLE`. `Karp21NativePositiveThresholdNumericFrameExact.nativePositiveThresholdParserSameOriginal` source-writes strict all-word positive gamma numerical outcome/suffix/rejection. These remain Agda-kernel OPEN.
- **P1 canonical Cook-Levin prior art**: `ConcreteTapeCanonicalCellBitsExact.canonicalWindowCodec`, `ConcreteTapeRunCNFWeldExact.runToEncodedCNFPath`, and `ConcreteTapeFlatAssignmentExact.flatTableauAssignment` already existed; `Karp21ConcreteTapeCanonicalRunFlatWeldExact.canonicalSameRunCNFPacket` now consumes them for the EXACT SAME concrete tape run/start row/flat bits, with original run length and start-row pullback. Global clause coordinate placement, endpoint clauses, accepting-run iff SAT and costed original E20/Cook-Levin remain OPEN.
- **Separate P-vs-NP**: actual original `PNotEqualsNPClayCoreExact.SATNotInP` still requires an uninhabited lower-bound proof; existing equivalence compiler is conditional, and P0/P1/P2 constructive work does not imply `SATNotInP`.

**Differential evidence**: independently tested parsed-raw signed score vs high-level first-enabled native positive threshold machine 63,001/63,001 PASS, including 7,000 random 128-bit signed weights; script `scripts/check_karp21_fractran_parsed_raw_threshold.py` is committed and called by focused preflight. Existing separate 71,025 comparator and 454,895 ripple binary-ledger differentials PASS. These do not prove Agda kernel acceptance, a bit clock, NP-completeness or P≠NP. Both original Karp Golden roots and focused referee now reach the new source owners.
