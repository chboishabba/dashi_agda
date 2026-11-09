# DASHI Bishop / Hyperform 13 — maximum-cut proof programme
Date: 2026-11-09
Working branch: `feat/twin-prime-six-wheel-bounded-gap-reuse-20261028` (PR #1408)
Status convention: OWNED = existing source; SOURCE = new implementation without Agda acceptance; OPEN = mathematical work not discharged.

## Attribution and typed boundaries

The existing **original** hyperfabric/fibre owners are:
- `DASHI/Wikimedia/IbrahimEnZeroToThirteenNDimOEISHyperfabricSnowballExact.agda`: fixed ternary cardinalities `3^12=531441`, `3^13=1594323`.
- `DASHI/Wikimedia/IbrahimZeroToThirteenTernaryCarryNDimFibreSnowballExact.agda`: 13 = 9+3+1, ternary numeral 111.
- `DASHI/Biology/RelationalAppraisalPointedPhaseExact.agda`: twelve-axis cycle, central completion **count**, not a constructed 13-trit carrier.
- `DASHI/Foundations/StageTwelveGrothendieckRelationHyperformExact.agda`: 12-axis relational site, cardinal crosswalk, non-descent witnesses.
- `DASHI/Moonshine/OggSSPP2BalancedTernaryPuncturedPlaneExact.agda`: actual T^2 puncture (8 nonzero points), and duplicated centre. NOT a proof that the thirteenth hyperfabric coordinate is punctured.

`T^12 × T` has 3^13 elements. The **punctured last coordinate** `T^12 × (T\\{0})` has `2·3^12`; the **punctured global origin** `T^13\\{0^13}` has `3^13−1`. Neither is equal to the original central-completion count. Do not silently identify these three objects or the ordinal Janko stage with an exponent.

## Phases, deliverables, exact declarations

| Priority | ID | Exact declaration | Deliverable | Initial state |
|---|---|---|---|---|
| P0 | H0.01 | `ternaryThirteenSplitTwelvePlusOne`, `ternaryThirteenJoinTwelvePlusOne` | Original-trit typed maps | OPEN |
| P0 | H0.02 | `ternaryThirteenSplitNineThreeOne`, `ternaryThirteenJoinNineThreeOne` | 9+3+1 typed map | OPEN |
| P0 | H0.03 | `ternaryThirteenSplitRoundTrip`, `ternaryThirteenJoinRoundTrip`, `ternaryNineThreeOneRoundTrips` | Full two-sided inverses | OPEN |
| P1 | H1.01 | `centralCompletionIsThirteenTritFibre` | Semantic carrier equivalence to source relational-completion type, if such a type exists; cannot derive from cardinality | OPEN |
| P1 | H1.02 | `centralCoordinateZeroSection`, `centralCoordinateZeroSectionSplit` | Chosen neutral last coordinate | OPEN |
| P1 | H1.03 | `centralCoordinatePunctureComplement`, `centralPunctureSplitRoundTrip`, `centralPunctureJoinRoundTrip` | Two-state last-coordinate typed carrier and inverse maps | OPEN |
| P1 | H1.04 | `globalOriginPuncture`, `lastCoordinatePunctureImpliesGlobalPuncture` | Distinguish puncture of last coordinate vs entire 13-fibre | OPEN |
| P2 | H2.01 | `centralPunctureObserverDescent` | Identify observer and decide non-descent by an actual pair of witnesses, not a count | OPEN |
| P2 | H2.02 | `centralPunctureGluingCompatibility` | Original hyperfabric/sheaf gluing laws and commuting naturality | OPEN |
| P1 | B-P1.01 | `originalNestedAtanExpFiniteCoefficientIdentity` | Actual source nested exp(2i atan_B(t)) denominator equation | OPEN |
| P1 | B-P1.02 | `originalNestedAtanExpAbsoluteEvaluation` | convergence and composition/reindex | OPEN |
| P1 | B-P1.03 | `originalAtanToCayleyOnHalfBall` | analytic equality on source half-ball | OPEN |
| P1 | B-P1.04 | `OriginalAtanFiveCayleyEvaluation` | selected t=1/5 witness | OPEN |
| P1 | B-P1.05 | `OriginalAtan239CayleyEvaluation` | selected t=1/239 witness | OPEN |
| P2 | B-P2.02 | `originalDirichletTermEqualsCanonicalNatPower` | all-index source canonical power identification | OPEN |
| P2 | B-P2.03 | `selectedZetaIsOriginalDirichletOnAboveTwo` | independent selected zeta identification | OPEN |
| P2 | B-P2.04 | `originalZetaAboveTwoAnalyticIdentification` | analytic function equality | OPEN |
| P3 | B-P3.01–07 | `originalBishopGammaMellinConverges`, `originalBishopGammaMellinFunctionalEquation`, `originalBishopComplexPiPowerPrefactor`, `originalBishopZetaAnalyticContinuation`, `originalBishopGammaZetaFunctionalEquation`, `originalXiIsOriginalCompletedProduct`, `originalXiEntireAndReflection` | Gamma/continuation/completed Xi | OPEN |

B-P0 terminal Bishop log and source above-two zeta are source-written in their existing owners. The previous Cayley forced-coefficient recurrence and 4-cycle are source-written. No kernel acceptance assertion is implied.

## Highest-alpha execution order

1. H0.01/02/03 generic original-trit finite-word iso; retain the same trit constructors and avoid cardinal-only proof.
2. H1.02/03/04 zero section, puncture, and global distinction, with explicit inverse laws and no semantic carrier coercion.
3. H1.01 source-specific carrier equality (requires actual relation-completion semantics); H2 original observer/gluing laws.
4. B-P1 analytic same-object exp/atan Cayley identity; then B-P2 source zeta and B-P3 Gamma/Xi.

Record actual commit IDs and update states after every source implementation; **no synthetic postulates** or record fields asserting the result without construction.


## Execution receipt: source-written H0/H1/H2, 2026-11-09

The implementation follows the initial maximum cut above. It is *not* a proof of full semantic completion or kernel acceptance.

### Source modules and completed *source-level* lemmas

1. `DASHI/Foundations/TernaryThirteenFibreSplitExact.agda`
   - `splitTritAfterJoin`, `joinTritAfterSplit`: general inverse laws on actual finite length-indexed trit words.
   - `ternaryThirteenSplitTwelvePlusOne`, `ternaryThirteenJoinTwelvePlusOne`;
     `ternaryThirteenSplitRoundTrip`, `ternaryThirteenJoinRoundTrip`.
   - `ternaryThirteenSplitNineThreeOne`, `ternaryThirteenJoinNineThreeOne`;
     `ternaryNineThreeOneSplitRoundTrip`, `ternaryNineThreeOneJoinRoundTrip`.
   - H0.01–H0.03: **SOURCE**.
2. `DASHI/Foundations/TernaryThirteenFibrePunctureExact.agda`
   - `centralCoordinateZeroSection` and `centralCoordinateZeroSectionSplit`.
   - `nonzeroFromNotNeutralRoundTrip` and `nonzeroToFromNotNeutral`.
   - `centralCoordinatePunctureComplement`, `centralCoordinatePunctureSplit`,
     `centralPunctureSplitRoundTrip`, `centralPunctureJoinRoundTrip`.
   - `lastCoordinatePunctureImpliesGlobalPuncture` and
     `globalPunctureDoesNotForceLastPuncture`: explicit counterexample to the reverse implication.
   - H1.02–H1.04: **SOURCE on the constructed word carrier**.
3. `DASHI/Foundations/TernaryThirteenFibreObserverNonDescentExact.agda`
   - `centralPunctureObserverDescent`: any map factoring the selected final-coordinate consumer through the 12-prefix observer is impossible, by two explicit 13-words.
   - H2.01: **SOURCE for the constructed prefix observer**; the original 12-axis semantic observer is not yet identified.
4. The three canonical `EverythingTOESymmetryResolved369`, `Unifier`, `Unified/Everything` import roots now import these modules.

### Revised *decisive* unpaid maximum cut

| Priority | ID | Exact next mathematical obligation | State |
|---|---|---|---|
| P0 | H1.01 | `centralCompletionIsThirteenTritFibre`: build/select the source semantic completion *carrier* (currently only `centralCompletionGroupOrderPattern : Nat` is present) and prove actual equivalence with the trit word model | OPEN |
| P0 | H2.01-source | `originalCentralPunctureObserverDescent`: transport the non-descent witnesses through actual source observer and consumer identifications | OPEN |
| P0 | H2.02 | `centralPunctureGluingCompatibility`: construct original site/refinement morphisms and the commuting condition for the particular central complement | OPEN |
| P1 | B-P1.01–05 | Original nested Bishop exp/atan finite coefficient identity; absolute evaluation; half-ball Cayley; then genuine five and 239 point witnesses | OPEN |
| P2 | B-P2.02–04 | source canonical power, independently selected zeta semantic identity, analytic equality | OPEN |
| P3 | B-P3.01–07 | Gamma Mellin, continuation, functional equation and completed Xi | OPEN |

New code is a **constructed trit-word model**. `Rank.fixedTernaryProfileCount rank13 = 1594323` and `Rel.centralCompletionGroupOrderPattern = 1594323` remain original count identities, not a claimed carrier equality. The new two puncture notions are distinct. The proposed original thirteenth-coordinate puncture remains a semantic question, not an established consequence of the count.

### Source commit receipts

- roadmap created: `17be788`
- generic typed factorisations: `3c29724`
- puncture and complement: `b7189aa`
- finite non-descent initial source: `012c572`, proof transport correction `8b4d6eb`
- golden root imports: `e2e390a`, `9b7710f`, `9b9448b`

Agda kernel check deferred at user request. No proof of H1.01, original source observer descent, H2.02 or remaining Bishop analytic/zeta/Xi gates is claimed.
