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
