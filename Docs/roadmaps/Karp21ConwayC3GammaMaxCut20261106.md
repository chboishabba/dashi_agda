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
