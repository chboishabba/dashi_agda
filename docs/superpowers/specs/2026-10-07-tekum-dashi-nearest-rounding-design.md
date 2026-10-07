# DASHI Exact Nearest Tékum Rounding Design

## Status

Architectural design for a new DASHI rounding semantics. This design is intentionally separate from Hunhold Proposition 5, whose raw-anchor-truncation nearest-rounding claim is refuted in the current branch.

## Goal

Define an exact rational nearest-rounding semantics from a higher-width ordinary finite Tékum value to the ordinary finite values at a lower width, derive a deterministic DASHI rounding operator from that semantics, characterize the relation between this new operator and raw anchor truncation, and prove or refute no-double-rounding for the new operator.

## Attribution Boundary

- Hunhold/source machinery remains authoritative only for the existing Tékum encoding, source parser, ordered semantics, and raw truncation structure already formalized in the repository.
- The exact-nearest semantics, tie policy, correction algorithm, and any no-double-rounding result are DASHI constructions.
- No theorem in this programme may be presented as a repair or proof of Hunhold Proposition 5.
- Existing canonical flags recording `sourceProp5NearestRoundingPaid = false` and `numericalNoDoubleRoundingPaid = false` retain their present meaning.

## Existing Reused Authorities

The programme must reuse, rather than duplicate:

- `TekumSourceWordDecodeExact.parseTekumWord` and the exact ordinary decoder;
- `TekumExactTriadicSemanticsExact.ordinaryRational` as numerical semantic authority;
- `TekumSourceOrderExact` / Proposition 4 source-order machinery for ordered finite candidates;
- `TekumTruncationRoundingExact.truncateTwo` as the raw structural truncation map;
- `TekumPrecisionCompositionExact.truncateTwoTwiceEqualsFour` as the structural composition theorem;
- the finite-word/balanced-ternary carrier machinery already present in the repo.

Machine floating point must not be used as semantic authority.

## Semantic Model

### Finite target carrier

For an admissible target width `m`, define the carrier of ordinary finite Tékum source words at that width. A member packages:

- a source word of width `m`;
- proof that the source parser decodes it as `Sem.ordinary ordinary`;
- the associated exact rational value `Exact.ordinaryRational ordinary`.

Special values NaR, zero-special, and infinity are not candidates in the ordinary finite nearest-rounding metric. Zero is included only if represented by an ordinary finite source word; the reserved special-zero source string remains outside the candidate carrier.

### Exact distance

For an ordinary finite source value `x` and an ordinary finite target candidate `y`, define

`tekumDistance x y = |decode(x) - decode(y)|`

in exact `ℚ`.

### Nearest set

For source `x` and target width `m`, define `NearestSet x m` as the ordinary finite target candidates with globally minimal exact rational distance. The semantic specification is set-valued: ties are represented honestly rather than eliminated by definition.

Required semantic properties:

- target carrier is finite;
- target carrier is nonempty at all supported target widths;
- nearest candidates exist;
- every member of `NearestSet` has the same minimal distance;
- every candidate outside `NearestSet` has distance at least that minimum.

## Canonical DASHI Rounding

Define two layers.

### Mathematical oracle

`exactNearestSet` computes/characterizes the complete minimizer set. It is the semantic oracle and does not encode a tie policy.

### Deterministic operator

`dashiNearestRound` chooses one member of `exactNearestSet` using a deterministic tie rule derived after enumeration of the exact tie surface.

The tie rule must satisfy:

- it is intrinsic to the target representation, not host enumeration order;
- it is deterministic;
- it is explicitly documented as DASHI policy;
- it is not chosen solely to force a no-double-rounding theorem;
- the theorem `dashiNearestRoundIsNearest` proves the chosen result is in `exactNearestSet`.

No concrete tie rule is fixed in advance. The implementation plan must first enumerate exact ties at small widths and then select the simplest representation-intrinsic rule consistent with those results.

## Raw-Truncation Comparison

Raw truncation remains a separate algorithm:

1. transform source to the source anchor representation;
2. drop the two low anchor trits with `truncateTwo`;
3. invert back to a lower-width source word using the existing fixed-width machinery.

Define comparison data:

- `rawTruncationCandidate`;
- whether the raw result is ordinary finite;
- whether the raw result belongs to `exactNearestSet`;
- an integer-code correction displacement from raw result to canonical nearest result whenever both are ordinary finite.

The programme must exhaustively measure the correction radius on tractable widths before introducing an efficient local algorithm.

## Efficient Implementation Strategy

The semantic oracle is allowed to be exhaustive and computationally expensive. The production theorem target is an efficient algorithm proved equivalent to the oracle.

Preferred approach:

1. raw truncate to obtain a provisional lower-width candidate when ordinary finite;
2. inspect a finite local neighbourhood in source integer-code order around that provisional result;
3. choose the exact-rational nearest local candidate, using the canonical tie rule;
4. prove the search radius is sufficient globally using source-order monotonicity / one-dimensional rational ordering.

The implementation plan must determine the minimal proved radius from exhaustive small-width data. Do not assume radius one. If regime/special boundaries require a larger bounded radius, use the smallest radius supported by evidence and proof. If no uniform small radius exists, retain the exhaustive oracle as the only canonical implementation and record the efficient-local route as refuted or open.

## Exact Correction Questions

The implementation must measure and either prove or falsify the following increasingly strong hypotheses:

1. whenever raw truncation lands ordinary finite, the exact nearest result differs by source-code displacement in `{-1,0,+1}`;
2. there exists a uniform finite correction radius independent of source width;
3. the correction rule can be expressed from only discarded trits plus local regime data;
4. a direct regime-aware closed formula exists.

Only hypotheses supported by exact computation and proof may be promoted.

## No-Double-Rounding Programme

For widths `n > m > k`, compare:

`dashiNearestRound m→k (dashiNearestRound n→m x)`

with

`dashiNearestRound n→k x`.

The programme must first perform exact exhaustive searches at the smallest informative width chains (at least 10→8→6 and, if computationally practical, 12→10→8). The outcome determines the theorem lane:

### If equality holds on exhaustive probes

Attempt a global proof using the exact-nearest characterization and canonical tie policy.

### If equality fails

Formalize the lexicographically/source-code minimal exact counterexample, including:

- source same-object decoder receipt;
- intermediate same-object decoder receipt;
- direct target same-object decoder receipt;
- exact rational values;
- exact distance comparisons proving both stagewise choices are locally nearest;
- inequality of two-stage and direct canonical results.

The final owner must therefore expose either a theorem or a falsifier, never an unqualified boolean claim.

## Proposed File Responsibilities

- `DASHI/ComputerScience/TekumExactNearestRoundingSemantics.agda`
  - finite target carrier;
  - exact rational distance;
  - nearest predicate/set;
  - existence/minimum semantic statements.

- `DASHI/ComputerScience/TekumNearestRoundingEnumerationExact.agda`
  - executable finite enumeration surface;
  - small-width exact fixtures;
  - tie and correction-radius receipts.

- `DASHI/ComputerScience/TekumRawNearestCorrectionExact.agda`
  - raw candidate reconstruction;
  - raw-vs-nearest comparison;
  - displacement/correction analysis.

- `DASHI/ComputerScience/TekumCanonicalNearestTieExact.agda`
  - deterministic tie policy selected from enumeration evidence;
  - proof that tie resolution chooses a member of the nearest set.

- `DASHI/ComputerScience/TekumEfficientNearestRoundingExact.agda`
  - bounded local correction algorithm if such a bound survives;
  - theorem equating efficient result with canonical exact nearest rounding.

- `DASHI/ComputerScience/TekumNearestNoDoubleRoundingExact.agda`
  - exhaustive width-chain probes;
  - global theorem or exact minimal counterexample.

- `DASHI/ComputerScience/TekumDASHIRoundingBoundaryExact.agda`
  - explicit truth boundary separating Hunhold raw truncation from DASHI exact-nearest semantics.

Existing Hunhold owners are not renamed or repurposed.

## Canonical Boundary Fields

The new boundary owner should distinguish at least:

- `hunholdRawTruncationNearestRefuted`;
- `dashiExactNearestSemanticsPresent`;
- `nearestExistencePaid`;
- `canonicalTieRulePaid`;
- `rawCorrectionRadiusCharacterized`;
- `efficientNearestImplementationPaid`;
- `efficientNearestEqualsSemanticOraclePaid`;
- `nearestNoDoubleRoundingPaid`;
- `nearestNoDoubleRoundingRefuted`.

The last two are mutually exclusive in the final accepted state.

## Max-Cut Order

A. Build exact finite target carrier and exact-rational distance.

B. Build nearest-set oracle and existence/minimum witnesses.

C. Exhaustively enumerate small widths to map ties and raw-to-nearest displacement.

D. Select and formalize the canonical tie rule from actual tie data.

E. Determine the smallest viable local correction radius; prove it sufficient or refute a uniform-local implementation.

F. Prove `dashiNearestRoundIsNearest` and, if an efficient algorithm survives, `efficientNearestEqualsCanonicalNearest`.

G. Exhaustively test 10→8→6 and larger practical chains for no-double-rounding.

H. Close with either a global no-double-rounding theorem or an exact minimal counterexample/no-go owner.

## Stopping Rules

Stop a proposed theorem lane immediately when an exact same-object counterexample is found. Promote the counterexample to an Agda no-go owner and continue only on weaker claims that remain logically possible.

Do not rescue a failed theorem by silently shrinking the domain, changing the metric, coercing special values, or choosing an ad-hoc tie rule. Any such change is a new explicitly named DASHI semantics and requires a separate theorem boundary.

## Success Criteria

The programme is complete when the repository has:

1. one exact set-valued nearest-rounding semantic oracle over ordinary finite targets;
2. one deterministic DASHI rounding operator with explicit tie policy and proof of nearestness;
3. an exact characterization of how raw truncation differs from canonical nearest rounding;
4. either a proved efficient local correction algorithm equivalent to the oracle or an exact no-go/open boundary explaining why not;
5. either a proved no-double-rounding theorem for the deterministic operator or an exact same-object counterexample;
6. a canonical boundary owner keeping all DASHI claims separate from Hunhold/source claims.
