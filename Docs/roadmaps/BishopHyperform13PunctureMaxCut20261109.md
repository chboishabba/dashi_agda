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


## Max-cut continuation: source StageAtlas valuation construction and transport

Source committed after the preceding execution receipt:

- `DASHI/Biology/RelationalAppraisalPointedPhaseExact.agda`: now **constructs** `SourceTwelveAxisValuation = StageAtlasZeroToEleven → Base369.TriTruth` and `SourceCentralCompletionCarrier = SourceTwelveAxisValuation × Base369.TriTruth`, plus central projection/coordinate and chosen neutral section. This is a source-grounded **valuation model** and is NOT identified with the pre-existing numeric `centralCompletionGroupOrderPattern` by group/Monster semantics.
- `DASHI/Foundations/TernaryThirteenOriginalAxisValuationBridgeExact.agda`: exact original-truth/trit bijection, `wordToValuation`, `valuationToWord`, `valuationWordRoundTrip`, `valuationPointwiseRoundTrip`; `sourceCentralToThirteen`, `thirteenToSourceCentral`, `sourceCentralRoundTripOnAxis`, `sourceCentralRoundTripOnCentre`, `thirteenSourceRoundTrip`, `sourceNeutralSectionCommutes`. Function-valued valuation round-trip is intentionally *pointwise*: no extensionality postulate is introduced.
- `DASHI/Foundations/TernaryThirteenOriginalSourceObserverDescentExact.agda`: explicit pair of original `StageAtlasZeroToEleven` valuation states differing only in the central original `TriTruth`; `originalSourceCentralNonDescentWitness`, `originalCentralPunctureObserverDescent` and `originalCentralPunctureObserverCannotFactor` reuse the original DASHI consumer-descent theorem and record.
- `DASHI/Foundations/TernaryThirteenOriginalSourceRefinementExact.agda`: a concrete involutive original-axis chart permutation; `centralProjectionCommutesWithRefinement`, `centralCoordinatePreservedByRefinement`, `neutralSectionCommutesWithRefinement`, `punctureRefinementForward`, `punctureRefinementBackward`, `refineTwicePointwise`. This is a **specific chart-refinement naturality test**, not proof of all original site coverings or sheaf gluing.
- Canonical three TOE root imports updated; temporary `--safe` options removed from three new finite-model modules because their existing `DASHI.Core.Prelude` imports are not declared safe.

### Revised precise obligations

| Gate | New state | Narrowest unpaid mathematical leaf |
|---|---|---|
| H1.01 model | SOURCE | A source-grounded 12-axis valuation × central original `TriTruth` carrier exists, and has full word-side and pointwise valuation-side inverses. |
| H1.01 semantic | **OPEN** | Construct and prove that the **original intended relational/group central completion** is this particular valuation model, rather than merely sharing the number `3^13`. Requires actual source semantics or a selected identification. |
| H2.01 model | SOURCE | Non-descent is proved on the original atlas/tri-truth **constructed completion carrier**, and on the generic 13-word representation. |
| H2.01 original operational | **OPEN** | Establish the same non-descent for an independently selected full relational or world-model observer/consumer, if its domain differs from the constructed source valuation model. |
| H2.02 concrete | SOURCE | Central coordinate and puncture predicate commute with one explicit involutive chart change. |
| H2.02 site | **OPEN** | Full site morphisms, cover families, restriction maps, central-section compatibility and sheaf matching-family gluing; cannot be derived from one chart permutation. |
| B-P1.01–05 | OPEN | Original analytic exp_C(2i atan_B) = Cayley t and selected Machin 1/5, 1/239. |
| B-P2.02–04 | OPEN | Original canonical powers and independently selected zeta equality. |
| B-P3.01–07 | OPEN | Gamma, analytic continuation, functional equation and Xi. |

All new implementations are **source-written; Agda 2.9 acceptance deliberately unclaimed**. Names in the table not implemented remain proposals, not fake discharge receipts.

### Continuation commits

- `4bc4936` source original StageAtlas valuation/centre
- `9ba4dea`, `6db4a0c` original 12-axis/13-trit round-trip and generic inverse correction
- `6e25017` original DASHI consumer non-descent
- `1114e5d` concrete original-axis chart refinement naturality
- `ec9aa35`, `ade7b0b`, `964fa62` source module option alignment
- `cf00a3f`, `71b7b61`, `a6ead48` root imports


## 2026-11-09 continuation: source StageBundleSheaf matching and puncture gluing

This pass advances H2.02 from a lone chart permutation to a **genuine instance
of the original `StageValuationBundleAtlas.BundleSheaf`**, on the existing
`StageAtlasZeroToEleven` and `Base369.TriTruth` carriers. It does
**not** claim a sheaf on an independently sourced nontrivial covering
topology, on a Monster group, or on the original 144-*relation-cell*
carrier. The stage-site owner already provides `maximalOnlyStageTopology`
(a conservative discrete site), which is the only topology selected here.

New owner:
`DASHI/Foundations/TernaryThirteenCentralCompletionBundleSheafExact.agda`.

Exact newly source-written declarations:
- `centralFamilyCompatible`: local observations `(axis value, centre)`
  at all twelve axes must agree on their central trit at `atlas-0`.
- `restrictCentral`, `glueCentral`, `centralGlueRestricts`:
  actual restrictions, compatible gluing, and pointwise restriction law.
- `sourceCentralCompletionBundleSheaf` and
  `sourceCentralCompletionStageSheaf`: reuse BOTH original sheaf
  interfaces, not a replacement record.
- `centralRestrictsCompatible`,
  `centralGlueReturnsCentre`,
  `centralGlueReturnsValuationPointwise`: genuine local/global
  reciprocity without function-extensionality postulates.
- `neutralSectionGluedCentre`: neutral section is globally
  valid; full completion is therefore not inherently punctured.
- `centralPunctureGluingForward`,
  `centralPunctureGluingBackward`,
  `centralPunctureGluingAtEveryAxis`: compatibility of the
  nonneutral central puncture with matching/gluing.
- `badLocalFamilyNotCompatible`: an explicit incompatible family
  with two different central trits; matching is substantive.

Second owner:
`DASHI/Foundations/TernaryThirteenCentralCompletionSheafNaturalityExact.agda`.

- `refineLocalFamilyCompatible`: the existing stage 0↔1 chart
  involution preserves the exact matching-family predicate.
- `refineRestrictPointwise`,
  `refineGlueValuationPointwise`, `refineGlueCentre`:
  restriction and gluing commute with chart reindexing in the
  appropriate pointwise / centre senses.
- `refineMatchingPuncturePreservation`: puncture survives the
  chart change **after gluing**, not just on individual states.

### Decisive remaining maximum cut (supersedes earlier H2.02 wording)

| Priority | Gate | Narrowest remaining obligation | Status |
|---|---|---|---|
| P0 | H2.02 constructed 12-axis site | Original `StageBundleSheaf` restriction, nontrivial matching, gluing, chart naturality, puncture preservation | SOURCE-WRITTEN |
| P0 | H1.01 semantic | Show independently intended relational/group central-completion semantics is the constructed 12-axis valuation × central trit *carrier*, not merely equal in cardinality | OPEN |
| P0 | H2.01 operational | Transport counterexample to independently selected world/relational observer and consumer on its actual state | OPEN |
| P0 | H2.02 independent topology | Upgrade from the conservative **discrete maximal-only** original site to the actually selected nontrivial covers/restrictions, if justified, and prove matching-family gluing on those covers | OPEN |
| P1 | B-P1.01–05 | Original nested atan-exp coefficients, absolutely justified evaluation, half-ball Cayley, two original point witnesses | OPEN |
| P2 | B-P2.02–04 | Original canonical Nat powers and selected zeta same-object identification | OPEN |
| P3 | B-P3.01–07 | Original Gamma/continuation/completed Xi | OPEN |

Source commits: `4f30630` central `BundleSheaf`, `e663b38`
naturality, `6291999` source import repair; three TOE imports
`bbe7fac`, `3fffa4d`, `33cd80b`. The statements are
**source-written**, not Agda-kernel accepted (deferred per user
request). This pass does **not** discharge P1–P3.


## 2026-11-09 highest-alpha follow-through: original pants/cylinder frontier

**Donor audit** (reuse original owners instead of duplicating pants):
- `DASHI/Topology/TernaryCylinderPantsGeometryExact.agda` proves `Digit369 ↔ BranchSlot`, three explicit outputs of the actual composed finite 1→3 pants carrier and refinement-prefix compatibility. Its cobordism statements are finite combinatorial statements; no smooth surface is established.
- `DASHI/Topology/TernaryPantsFrontierExact.agda` gives `Address n ↔ PantsPath n`, both round trips, and `addressToPantsPathAppend` and `pantsPathToAddressAppend` for every finite depth.
- `DASHI/Reasoning/TypedHyperfabricPantsGluingBridgeExact.agda` requires a **five-coordinate `InterfaceMatch`** on *interpreted edge stalks* before a seam can be admitted; a seam certificate does not construct a new `TypedHyperfabric`. That side condition remains in force here.
- `DASHI/Foundations/HyperformChartGluingExact.agda` likewise distinguishes chart overlap, observer fibres, and independent fabric context. Do not promote a matching profile count to a same-object theorem.

### New exact source declarations

`DASHI/Foundations/TernaryThirteenOriginalPantsFrontierBridgeExact.agda`:

- `tritToSlot`, `slotToTrit`, `tritSlotRoundTrip`, `slotTritRoundTrip`.
- `wordToPants`, `pantsToWord`, `wordPantsRoundTrip`, `pantsWordRoundTrip` for **all n**.
- `wordToCylinder`, `cylinderToWord`, `wordCylinderRoundTrip`, `cylinderWordRoundTrip` reuse the pre-existing original Frontier cylinder/pants isomorphism for all n.
- `sourceCentralToPants13`, `pants13ToSourceCentral`, `pants13SourceRoundTrip`, `sourcePantsRoundTripOnAxis`, `sourcePantsRoundTripOnCentre` carry the original StageAtlas/tri-truth central valuation representation to actual depth-13 pants paths. Valuation equality is pointwise; no function extensionality axiom.
- `wordToPantsAppend`, `originalTwelvePlusOnePantsGluing`, and `originalCentralBranchNegative`/`Neutral`/`Positive` prove that the *new central trit is literally the original ternary pants refinement branch*. The three branch slots are `slot3`, `slot6`, `slot9`, respectively, and all match the actual original cylinder refinement via the Frontier theorem.
- `neutralSourcePantsEndsAtMiddleSlot` and `sourceCentralPantsCentreCanBeNeutral` witness that a valid global state may have a neutral (not punctured) centre.

`DASHI/Foundations/TernaryThirteenOriginalPantsObserverPunctureExact.agda`:

- `originalPantsCentralNonDescentWitness`, `originalPantsCentralCannotFactor` and `originalPantsCentralObserverInsufficient` provide genuine explicit-witness DASHI consumer non-descent on the **existing pants-path carrier**.
- `pantsPunctureFromWord`, `pantsPunctureToWord`, `pantsPuncturePreservedUnderCylinder` prove preservation of the selected final-coordinate puncture across the *original* path/cylinder round trip. This is not the global-origin puncture.

The three golden TOE import roots now reuse both modules.

### Updated decisive cut

| Priority | Gate | Remaining precise statement | Status |
|---|---|---|---|
| P0 | H1.01 address-level | Original StageAtlas central valuation ↔ `TritWord 13` ↔ original `PantsPath 13` ↔ original `Address 13` with constructive word and path round trips, and pointwise valuation round trips | SOURCE-WRITTEN |
| P0 | H1.01 semantic | Show the independently intended **relational/group/Monster or actual world-model completion** has precisely this selected valuation and its pant seams, including source-bound identification of boundary channels | OPEN |
| P0 | H2.01 pants operational | Source-pants-path central observer non-descent and puncture transport | SOURCE-WRITTEN |
| P0 | H2.01 independent operational | Select original world-model observers/consumers and prove their actual state and observation maps factor through (or commute with) the pants carrier; avoid inventing attribution | OPEN |
| P0 | H2.02 discrete StageBundleSheaf | Explicit matching, nontrivial compatibility, gluing, chart naturality and puncture preservation on original conservative stage site | SOURCE-WRITTEN |
| P0 | H2.02 original pants seam | Construct independently justified `Pants.InterfaceMatch` for the source's actual edge stalk values and prove the post-gluing fabric's incidence/restriction laws; the original donor explicitly warns the seam itself doesn't construct a new fabric | OPEN |
| P0 | H2.02 nontrivial site | Prove matching-family gluing for selected nontrivial cover families beyond maximal-only discrete topology, if sourced | OPEN |
| P1 | Bishop Cayley | Original analytic nested `exp_C(2i atan_B(t))` Cayley identity at both Machin points | OPEN |
| P2 | Zeta | Canonical power identity; original-source selected zeta same-object theorem | OPEN |
| P3 | Gamma/Xi | Original Gamma and analytic continuation, functional equation, completed Xi | OPEN |

**Commits:** `8c324c3` new original all-depth pants bridge, `c267f7d` original 12+1 append/refinement, `1256f30` pants observer non-descent/puncture; TOE roots `2bbe1ab`, `ac67a39`, `2fd3c13`. Source-written only; no Agda kernel receipt claimed. Crucially the 13th trit is the *selected branch*, not intrinsically punctured: `slot6` is a legal central neutral branch.

This advancement addresses the highest-alpha finite **pants gluing** reuse but cannot solve mathematical analysis P1–P3 by index coincidence.


### Direct original pants ↔ source sheaf gluing transport

`DASHI/Foundations/TernaryThirteenPantsSheafGluingTransportExact.agda`
adds `glueCompatibleLocalsToPants`,
`gluedPantsSelectsCommonCentralBranch`,
`originalPantsGlueRestricts`,
and `neutralGlobalPantsLastSlot`.

For every original `StageAtlasZeroToEleven` local matching family
`locals : Axis12 → TriTruth × TriTruth` with a common central trit,
construct the original depth-13 `TernaryPantsFrontier.PantsPath`
through `BundleSheaf.glue`, then prove the decoded original local
restrictions equal the supplied locals **at every axis**. The path
chooses exactly the matching family's common central branch, while
the neutral source section remains an admissible `slot6`.

This is a genuine local-to-pants-frontier commuting theorem. It does
not construct physical pants surfaces, nontrivial covers, arbitrary
typed-hyperfabric boundary `InterfaceMatch` or group equality.
Source commits: `4ac0860` followed by `e7033e4` import correction;
TOE imports `d1139a1`, `d4c5bab`, `8b221cd`.

**Updated H2.02 maximal cut:** Source StageBundleSheaf matching/gluing,
actual pants frontier refinement and source matching-family-to-pants
restriction recovery are SOURCE-WRITTEN. Unpaid: original independent
edge-stalk `InterfaceMatch`, topology mutation/reorganization
preserving incidence and restriction, and justified nontrivial
Grothendieck covers / full matching-family descent.


## Max-cut continuation: nonvacuous seam quotient and two-chart cover

**This pass targets the two independently outstanding H2.02 leaves rather
than adding another cardinal-only interface.** Both modules are
source-written, not Agda-kernel checked.

### H2.02 seam — real incidence merge, not vacuous boundary matching

`DASHI/Reasoning/TypedHyperfabricPantsNonvacuousSeamQuotientExact.agda`

- Source: **original** `RelationalBranchCobordismGeometry.outerInnerMatch`,
  `selectedChannel2`, `innerInputChannel2`; original
  `TypedHyperfabricCore.TypedHyperfabric` and `GlobalSection`.
- `SeamSignature`, `boundarySignature`,
  `interfaceMatchImpliesSignatureEquality`: construct and prove equality
  of the exact five matched observables (proposition, capacity, phase,
  wave, openness), **not** full channel records or source labels.
- `BeforeIncidence`: two *real* vertex–edge incidences,
  distinct edge identities and source channels.
- `AfterIncidence`: the two original vertices both incident to
  **one** seam edge; `mergeEdge`, `mergeIncidence` map the
  original incidence geometry.
- `beforePantsFabric`, `beforePantsSection`,
  `afterPantsFabric`, `afterPantsSection`: actual original
  `TypedHyperfabric` and compatible `GlobalSection` values.
- `seamRestrictionPreserved`, `seamEdgeValuePreserved`:
  prove transport of the five-field source edge values and vertex
  restrictions through the noninjective edge quotient.
- `sourceEdgesDistinct`, `sourceEdgesHaveSameMergedAddress`,
  `mergedOuterProvenanceRetained`,
  `outerIsIncidentAfterMerge`, `innerIsIncidentAfterMerge`.
- Source branch commit: `cda3dbf`.

**Limit:** the quotient is a *specific original two-channel specimen*.
A free theorem merging arbitrary original hyperfabric edges requires
their specific stalk interpretation, five-field `InterfaceMatch`,
and a stated strategy to preserve full original edge values that the
five-field signature intentionally forgets.

### H2.02 overlap — genuine proper two-chart matching family

`DASHI/Foundations/TernaryThirteenTwoChartOverlapGluingExact.agda`

- `LeftChartAxis` indexes original stage axes 0..6, and
  `RightChartAxis` indexes original axes 6..11: both are proper
  subcharts and they overlap at **axis 6**, unlike the previous
  maximal-only discrete site. They cover all twelve atlas axes.
- `TwoChartCentralFamily` retains separate valuations and central
  trits; `TwoChartMatches` requires *both* same valuation at axis 6
  **and** equality of the two centres.
- `glueTwoChartCentral`, `twoChartLeftRestricts`,
  `twoChartRightRestricts`, `twoChartLeftCentreRestricts`,
  `twoChartRightCentreRestricts`: construct a single original
  `SourceCentralCompletionCarrier` and prove exact chart recovery.
- `restrictToTwoCharts`, `restrictedTwoChartsMatch`,
  `sourceTwoChartGluingRoundTripPointwise`,
  `sourceTwoChartGluingCentreRoundTrip`: global-to-local-to-global
  pointwise and central inverse.
- `badOverlapCannotGlue` and `badCentreCannotGlue` distinguish
  the valuation-overlap obstruction from a contradictory shared
  central-coordinate obstruction.
- `twoChartPunctureGluing` transports the selected puncture.
- `glueTwoChartsToOriginalPants`,
  `twoChartPantsLeftRestrictions`,
  `twoChartPantsRightRestrictions`,
  `twoChartPantsCentreRestrictions`: transport the nontrivial
  matching-family glue into the **original** depth-13 pants frontier
  with exact re-restriction.
- Source commits `92f6a7c`, `c2a3c53`.

The two source modules are imported into all three TOE roots
(`24d8348`, `8f2e4c8`, `fc46aae`).

### Narrowed exact remaining maximum cut

| Gate | Exact narrowest unpaid theorem | Status |
|---|---|---|
| H2.02 selected finite seam | Nonvacuous topology change, incidence and five-field restriction preserved in original source pants specimen | SOURCE-WRITTEN |
| H2.02 selected finite overlap | Two proper overlapping original atlas charts and exact centre/valuation matching, glue/restrict, pants transport | SOURCE-WRITTEN |
| H2.02 general nontrivial site | Build an independently justified **full** Grothendieck topology of nontrivial covering sieves over original chart objects, and show stability/transitivity and all-cover descent; a single two-chart set cover is not yet this theorem | OPEN |
| H2.02 arbitrary seam | Arbitrary selected original edge stalk `InterfaceMatch` plus incidence/restriction preservation under selected noninjective edge quotient, including source-bound provenance semantics | OPEN |
| H1.01 semantic | Independently select and identify intended relational/group completion with actual original StageAtlas valuation × central trit, not merely finite address or pattern count | OPEN |
| H2.01 operational | Transport non-descent to independently selected full world/relational observer+consumer, not only the source StageAtlas and pants models | OPEN |
| B-P1 | Actual Bishop original nested atan/exponential same-object analytic Cayley identity and both Machin evaluations | OPEN |
| B-P2 | Original canonical Nat-power and independent selected zeta equality | OPEN |
| B-P3 | Original Gamma/Mellin, continuation, functional equation, completed Xi | OPEN |

**Important boundary:** these are finite, theorem-bearing reorganisation
and gluing examples. They neither establish a smooth pants/cobordism
surface nor identify the group completion, the original world model,
analytic modular j, or the source Bishop zeta/Xi objects.


## 2026-11-09 maximum-cut generalization: arbitrary matched seam and binary covers

This continuation replaces two isolated examples with **quantified theorem
sources**, without collapsing the original semantic firewalls.

### H2.02 arbitrary *matched* two-edge seam — source-written

`DASHI/Reasoning/TypedHyperfabricPantsParametricSeamQuotientExact.agda`
committed as `aa675839`.

`module MatchedSeam (left right : Pants.BranchChannel)
(matched : Pants.InterfaceMatch left right)` constructs **for
every such original channel pair**:
- `beforeFabric` and `beforeSection` with two real incidences;
- `afterFabric` and `afterSection` with one seam edge and both
  original vertices incident;
- `matchedSignatures` proved by the original
  `interfaceMatchImpliesSignatureEquality`;
- `preserveIncidence`, `preserveVertexRestriction`,
  `preserveEdgeValue` and `bothOriginalEdgesIdentify`;
- exact specialization to the canonical donor's
  `selectedChannel2`, `innerInputChannel2`,
  `outerInnerMatch`.

No equality of full `BranchChannel` data is assumed: the seam
stalk is precisely the five-field signature. The remaining
**independent edge-source** obligation is a theorem turning actual
heterogeneous `TypedHyperfabric.edgeStalk` values into this
`Pants.InterfaceMatch` with source provenance, plus a general
incidence rewrite for a selected larger fabric.

### H2.02 arbitrary decidable *binary* site cover — source-written

`DASHI/Foundations/TernaryThirteenArbitraryBinaryCoverDescentExact.agda`
committed as `f4ef9ed`.

- `BinaryCover` supplies arbitrary predicates for left/right
  chart membership at each ORIGINAL `StageAtlasZeroToEleven`
  axis, with a constructive proof every axis is in at least
  one chart. No fixed {0..6}/{6..11} partition remains.
- `BinaryLocalFamily`, `BinaryMatching` require the
  left/right valuations to agree on *every overlapping axis*
  and both local centres to agree.
- `glueValue`, `glueBinaryCentral`, `leftRecovers`,
  `rightRecovers`, `leftGlobalRestriction`,
  `rightGlobalRestriction`, `leftCentralRestriction`,
  `rightCentralRestriction` prove constructive gluing and
  local recovery for **every binary cover** and matching family.
- `restrictBinaryCentral`, `restrictedBinaryMatches`,
  `glueRestrictedPointwise`, `glueRestrictedCentre`
  prove global-to-local-to-global recovery.
- `binaryCoverPuncturePreserved` proves the common centre
  remains nonneutral when punctured before gluing.

This is stronger than a fixed two-chart overlap. It does NOT
give arbitrary covering *sieves* in the original
`StageTwelveGrothendieckRelationHyperformExact.SmallCategory`,
or cover stability/transitivity under pullback. That is the
precisely outstanding Grothendieck-topology theorem.

### Remaining decisive leaves (after this pass)

| Gate | Source status | Exact outstanding source proof |
|---|---|---|
| H2.02 two-edge seam for any five-field matched channels | SOURCE-WRITTEN | Supply actual heterogeneous hyperfabric edge-stalk-to-channel interpretation and `InterfaceMatch` from independently selected world/relational edge data; implement generalized fabric topology rewrite beyond the two-edge specimen |
| H2.02 binary original-axis covering descent | SOURCE-WRITTEN | Build a coherent nontrivial Grothendieck topology over original chart morphisms, prove pullback stability/transitivity and all-sieve matching-family uniqueness/descent |
| H1.01 | OPEN | Independently identify intended relational/group completion with constructed 12-stage valuation plus centre and original pants path |
| H2.01 world | OPEN | Transport non-descent to independently selected world-model observer, original state and actual consumer |
| Bishop P1 | OPEN | Prove actual nested original exponential–atan same-object analytic identity and 1/5,1/239 Machin witnesses |
| Zeta P2 | OPEN | All Nat canonical powers, independent selected zeta function equality |
| Gamma/Xi P3 | OPEN | Genuine source Gamma integral, continuation, functional equation, entire completed Xi |

Root imports committed `f73607c`, `fdaaf93`, `feb63c5`.
All statuses describe **source-written** statements without a
kernel acceptance receipt. No analytic gate is marked paid by the
hyperfabric lemmas.


## 2026-11-09: prior-art pullback/pushforward correction and original triadic-site glue

**Crucial correction to earlier roadmap:** the non-discrete Grothendieck
category and topology are ALREADY owned by
`DASHI/Foundations/RelationalStageTwelveGrothendieckExtensionExact.agda`:
`RelObj` includes global ABC, edge charts AB/BC/CA, and overlap
vertices A/B/C; `RelHom` includes nonidentity restrictions.
`relationalPatchCategory`, `triadicRelationalSieve`,
`relationalTriadicTopology`, `triadicRelationalSieveCovers`,
`pullbackOfMaximalIsMaximal`, `stableTriadic` and
`transitiveCover` supply a genuine non-discrete site with
pullback stability and transitivity through the original Stage-12
`SmallCategory` / `Sieve` / `GrothendieckTopology` APIs.
**Never count constructing a new category/topology as an unpaid lemma.**

### Source-written: glued selected central fibre over existing triadic cover

New owner
`DASHI/Foundations/TernaryThirteenOriginalTriadicSiteGluingExact.agda`.

- `GlobalTwelveCentre = (Block4 × (Block4 × Block4)) × TriTruth`
  gives twelve actual trits grouped A/B/C as 4+4+4 and the
  independently retained thirteenth central value.
- `restrictAB`, `restrictBC`, `restrictCA`, and
  `TriadicMatching`: agreement at all three four-coordinate
  overlaps (A/B/C) and **two independent central matching laws**.
- `glueTriadic`, `triadicABGlueRestricts`,
  `triadicBCGlueRestricts`, `triadicCAGlueRestricts`:
  explicit constructive descent for the **selected original
  triadic covering family**.
- `triadicGlobalRestrictionMatches`,
  `triadicGlobalRoundTrip`: full global-to-local-to-global
  identity on the grouped source carrier.
- `selectedOriginalTriadicCover`,
  `selectedOriginalTriadicPullbackStable`: direct theorem reuse
  of the already existing non-discrete Grothendieck site.
- `globalToSource`, `sourceToGlobal`,
  `sourceGlobalPointwiseRoundTrip`,
  `sourceGlobalCentreRoundTrip`, `globalSourceRoundTrip`
  connect the 4+4+4 grouping to actual original
  `StageAtlasZeroToEleven` valuation and central `TriTruth`;
  valuation recovery remains pointwise without assuming functional
  extensionality.
- `originalTriadicGlueToPants`,
  `originalTriadicPantsRecoverAtlas`,
  `originalTriadicPantsRecoverCentre`: source triadic-site
  matched local charts glue into the ORIGINAL depth-13 pants
  frontier with atlas/centre recovery.
- `triadicPunctureGlue`: nonneutral central match persists.

Commits: `82538ec` initial source; `8346538` source typed
atlas import; `5490be6` original pants gluing transport.

### Source-written: use genuine existing pullback / representative
### pushforward / residual operator, not newly invented adapters

New owner
`DASHI/Foundations/TernaryThirteenOriginalPullbackPushforwardWeldExact.agda`.

- `sourceCentralSectionedProjection` instantiates the **original**
  `SectionedProjectionProvenanceBridgeExact.SectionedProjection`
  with the chosen neutral section.
- `sourcePullbackObservable`,
  `selectedRepresentativePushforward`,
  `pushforwardAfterPullback`,
  `pullbackOfPushforwardForFibreConstant` reuse the original
  pullback/fibre-constant and representative operations.
  The 'pushforward' here is the **chosen representative**
  `observable ∘ sourceNeutralSection`, not a claim of a
  categorical direct-image functor or Kan extension.
- `sourcePullbackPredicate`, `sourcePullbackMeet`,
  `sourcePullbackJoin` reuse
  `PredicatePullbackLatticeExact`, with true pointwise
  meet/join transport.
- `sourceCentralResidual`, `sourceCentralReopen`,
  `sourceResidualExact`, `sourceCentralResidualReopening`,
  `sourceCentralProvenanceBearingQuotient` provide the
  original provenance-bearing full fine-state reopening by
  retaining the actually omitted central trit. This is the
  missing exact inverse beyond neutral section alone.

Commits: `a247bb9` original pullback/pushforward weld;
`8316f39` explicit original quotient type signature.
All three canonical TOE import roots updated:
`47b09b1`, `bf73a63`, `4016fff`.

### Corrected narrowest unpaid mathematical cut

| Gate | Updated source state | Exact next unpaid theorem |
|---|---|---|
| H2.02 non-discrete topology | EXISTING ORIGINAL OWNER | `RelationalStageTwelveGrothendieckExtensionExact` already pays the actual A/B/C category, nontrivial sieve, pullback stability and transitivity; DO NOT repeat |
| H2.02 triadic selected-cover central gluing | SOURCE-WRITTEN | Extend matched local sections and descent from the selected 3-chart triadic cover to **every** covering sieve of the original non-discrete site, with explicit restriction functoriality and uniqueness |
| H2.02 typed pants seams | SOURCE-WRITTEN in two-edge matched-channel specimen | Independently select and interpret original heterogeneous world/relational edge stalks, pay `Pants.InterfaceMatch` from their original properties, then prove topology quotient on the selected full fabric |
| H1.01 semantic | OPEN | Independently prove the intended relational/group completion equals the original 12-axis valuation + centre, including selected context/provenance |
| H2.01 operational | OPEN | Identify and use the independently intended world-model state, observer and consumer; transport the actual non-descent counterexample |
| Bishop P1 | OPEN | Original analytic nested exp(2i atan) = rational Cayley; 1/5, 1/239 analytic Machin witnesses |
| Zeta P2 | OPEN | Actual source Nat-power and independent selected zeta function same-object identification |
| Gamma/Xi P3 | OPEN | Source Gamma, continuation, functional equation, Xi |

**Verification status:** source-written, no Agda kernel execution
claimed. The installed environment did not expose an `agda`
executable; keep all kernel-acceptance flags open. The original
non-discrete site is not the maximal-only discrete site; the two
owners must remain distinguished.


### 2026-11-09 addendum: original morphism-indexed presheaf and UNIQUE descent

`DASHI/Foundations/TernaryThirteenOriginalTriadicPresheafExact.agda`
is now the actual original-site indexed operator, not just a stand-alone
cover-family construction:

- `Section : RelObj → Set` assigns the 12+centre carrier at
  `globalABC`, paired four-trit charts at `edgeAB/BC/CA`,
  and four-trit-plus-centre overlap stalks at `vertexA/B/C`.
- `restrictAlong : RelHom V U → Section U → Section V`
  supplies explicit restriction maps on **every** original
  `RelationalStageTwelveGrothendieckExtensionExact.RelHom`,
  including six proper overlap morphisms and three global-to-chart
  morphisms.
- `restrictIdentity` and `restrictComposition`:
  source-written contravariant presheaf functoriality, including
  actual two-stage restriction composites.
- `aOverlapAgrees`, `bOverlapAgrees`, `cOverlapAgrees`:
  matching for restrictions of any global source state.
- `CoverTripleMatches`, `coverTripleToTriadicMatching`:
  full equality of actual overlap stalks implies both the
  corresponding four-coordinate overlaps and the matching
  centre; no independent agreement law is silently assumed.
- `glueCoverTriple`, `glueCoverTripleAB/BC/CA`:
  construct and re-restrict the selected original triadic
  covering-family glue.

Existing selected-cover owner
`TernaryThirteenOriginalTriadicSiteGluingExact.agda` now has
`triadicGluingUnique`: **every** global state having these three
prescribed chart restrictions equals the constructed glue.
That closes existence AND uniqueness for this selected cover,
on the constructed same-object source section family.

Commits: `9310ae6` (original presheaf),
`6cb6f23` (uniqueness), golden roots
`f774a45`, `b424d5f`, `e794452`.

**Revised H2.02 status:** original seven-object A/B/C topology,
pullback stability, transitivity: ALREADY OWNED; original indexed
presheaf restrictions, functoriality, selected nontrivial triadic
cover matching, unique gluing and pants transport: SOURCE-WRITTEN.
Remaining: prove sheaf descent for **all covering sieves**, not
only the distinguished triadic generator, and supply independently
intended source semantics to identify the constructed section
presheaf with the intended relational/world/Monster completion.

No top-level original analytic Bishop P1, zeta P2 or Gamma/Xi P3
status changes.


## Highest-alpha source tranche: ALL original relational covering sieves

New owner:
`DASHI/Foundations/TernaryThirteenOriginalTriadicAllSieveSheafExact.agda`.

The previously open **all-covering-sieve** mathematical obligation
has a source-written proof construction on the already existing
`RelationalStageTwelveGrothendieckExtensionExact.relationalTriadicTopology`.
It does NOT build another site.

Exact declarations:
- `SieveMatching sieve`: value for every sieve arrow, proof-of-
  membership independence, and compatibility with the ACTUAL
  `RelHom` restrictions and `Site.composeRel`.
- `restrictToSieve`: any global presheaf section restricts to a
  matching family on any original sieve.
- `triadicMatchingFromSieve`: derive AB/BC/CA overlap equality
  from arrow-natural matching and proof independence at the
  original vertex overlap arrows.
- `glueSieve`: case distinction on original
  `Site.RelCover` constructors. The maximal case reconstructs
  from the identity arrow; the genuine nontrivial global
  triadic case calls the existing concrete matching/gluing
  theorem.
- `triadicGlueRestrictsEveryMember`: full recovery at every
  original sieve member, including the global identity if
  admitted, the three chart maps and the three vertex-to-global
  maps. The proof uses the original `Sieve.closed` and
  `proofIndependent`.
- `allCoverGlueRestricts`: selected glue restricts to every
  local value of an arbitrary **covering sieve**.
- `allCoverGlueUnique`: an arbitrary competing global section
  with the same sieve restrictions is equal to the constructed
  glue, using the selected triple's
  `triadicGluingUnique` theorem.

These declarations are quantified over the original `Site.RelCover`,
not only a fixed ABC triple or a binary set cover. Thus H2.02
**all-covering-sieve sheaf descent on the constructed central-trit
presheaf** is now **SOURCE-WRITTEN**, while Agda kernel acceptance
remains unverified as requested.

Commits: `8be0475` source, `f5bef7d` typed topology
alias repair, `0a83255` locally scoped exact type contracts;
golden roots `b024523`, `cfdd31f`, `661228f`.

### Current remaining decisive original maximum cut

| Priority | Gate | Exact unpaid proof |
|---|---|---|
| P0 | H1.01 semantic | The independently intended **original** relational/group completion is the constructed `StageAtlasZeroToEleven → TriTruth` plus central `TriTruth` source carrier; evidence of semantic equivalence, not count |
| P0 | H2.01 independent operational | The actual world-model/relational observer and consumer map commute with or are equivalent to the selected StageAtlas/pants observer, so the concrete non-descent witness is valid for the same state |
| P0 | H2.02 source seams | Independent heterogeneous original edge-stalk interpretations and genuine five-coordinate `InterfaceMatch` on the selected larger hyperfabric; preserve actual full topology/provenance semantics under induced quotient |
| P0 | H2.02 formal acceptance | Agda kernel check (deferred); source-written all-sieve proof should not be described as kernel certified |
| P1 | Bishop Cayley | Original nested Bishop exp/atan analytic same-object identity; its actual 1/5 and 1/239 evaluations |
| P2 | Zeta | Canonical Nat powers and identification with independently selected original zeta |
| P3 | Gamma/Xi | Source Gamma integral, analytic continuation, functional equation and completed Xi |

The original A/B/C topology and `pullbackSieve` laws were
previously paid and must remain attributed to
`RelationalStageTwelveGrothendieckExtensionExact`.
The source of `selectedRepresentativePushforward` is still
the original sectioned representative operation, not a claim
about a categorical pushforward on arbitrary sheaves.


## Continuation: original ITIR semantic-node observer transport and minimal repair

This pass targeted H2.01 on the **actual** original ITIR world-node
carrier, rather than building a fabricated world/Monster semantic
completion. The original selected type is
`DASHI.Interop.ITIRFederatedTypedWorldProjectionExact.SourceAddressableSemanticNode`,
with source identity, revision, anchors, producer/reviewer references
and projection/authority boundaries. Its data cannot be interpreted
as 12 ternary valuations plus a thirteenth central trit by
cardinality or string labels.

New owner:
`DASHI/Foundations/TernaryThirteenOriginalConsumerRepairAndWorldTransportExact.agda`.

Source-written proofs on the constructed source-valuation carrier:
- `repairedCentralObserver`: canonical
  `ObserverRefinementLatticeExact.pairObserver` of source
  12-coordinate projection and original `Base369.TriTruth` centre.
- `centralRepairIsSufficient`,
  `centralRepairFactors`: selected consumer becomes sufficient
  and factors through the *repaired* observer, reusing original
  `ConsumerDescentMinimalObserverExact` and
  `SectionedProjectionProvenanceBridgeExact`.
- `sourceTwelveAloneCannotSuffice`,
  `centralRepairStrictlyRefinesTwelve`:
  original StageAtlas projection alone remains insufficient, and
  the repaired observer strictly refines it by explicit neutral/
  positive central collision.
- `everySufficientRepairSeparatesCentralCollision`,
  `centralCoordinateIsNecessaryForThisRepair`:
  any alternative repair for this consumer must separate the
  original witnessed collision; separation alone is NOT claimed
  to prove global sufficiency.

Conditional exact original-world transport:
- `ITIRWorldState`: aliases the actual
  `ITIR.SourceAddressableSemanticNode`.
- `OriginalWorldCentralTransport` is a **source-admission record**,
  requiring an independent `worldToSource` map, actual
  `worldNeutral/worldPositive` nodes whose source-state identities
  match the selected pair, and commuting actual
  `worldObserve/worldConsume` maps.
- `worldPairSameObservation`,
  `worldPairDifferentConsumer`,
  `originalWorldNonDescentFromPaidCorrespondence`,
  `originalWorldCannotFactorAfterPaidCorrespondence`,
  `originalWorldObserverInsufficientAfterPaidCorrespondence`:
  genuine original-world consumer non-descent **conditional upon**
  the above original-source witness record being instantiated.

There is deliberately **no canonical inhabitant** of
`OriginalWorldCentralTransport`. This pass pays the transport
lemma but not the empirical/operational identification of two
independent semantic-world nodes or their source evidence.

Source commit receipts: `d06fdaa` original world/repair contract;
`cce2df5` import repair; `b5783f4` strict-refinement and
repair necessity; three canonical TOE imports `69bb637`,
`bb334be`, `4b7c53d`.

### Revised outstanding mathematical gates

| Gate | Most precise remaining work | Source status |
|---|---|---|
| H2.01 selected source repair | Strict refinement, sufficient repaired consumer and necessity of separating central collision | SOURCE-WRITTEN |
| H2.01 original-world transport | Conditional non-descent on the ACTUAL ITIR semantic-node type after paid selection of original world nodes and commuting observers | SOURCE-WRITTEN CONDITIONAL |
| H2.01 independent instantiation | Select and justify genuine original world nodes and actual world-observer / consumer mapping; instantiate `OriginalWorldCentralTransport` | OPEN |
| H1.01 semantics | Independently identify the intended full relational/group completion with the source StageAtlas 12+1 central model, not from equal counts | OPEN |
| H2.02 source seams | Actual heterogeneous selected world/relational edge-stalk interpretations and `Pants.InterfaceMatch` in the selected full fabric, beyond abstract matched pairs | OPEN |
| Bishop P1 | Original nested analytic exponential/atan Cayley identity and both original Machin point witnesses | OPEN |
| Zeta P2 | Original canonical Nat powers and selected independently sourced zeta | OPEN |
| Gamma/Xi P3 | Original Gamma integral, analytic continuation, functional equation, entire completed Xi | OPEN |

All commits remain **source-written, not Agda-kernel accepted**.
The all-sieve non-discrete constructed-site theorem of the prior
round remains source-written; no assertion about full original
world semantics, modular j, Monster representation or analytic
Bishop objects follows from this observer bridge.


## 2026-11-09 decisive highest-alpha gate: H2.02 selected heterogeneous original relational pants seam

**Selected finite original-source H2.02 gate: SOURCE-COMPLETE.**
This specifically pays the previously missing heterogeneity + exact donor match
+ nonvacuous incidence rewrite + source provenance transport in the ORIGINAL
selected relational-pants specimen. Kernel acceptance is **NOT** claimed.

Owner:
`DASHI/Reasoning/TypedHyperfabricOriginalHeterogeneousPantsSeamExact.agda`.

Unlike the earlier uniform `BranchChannel` specimen, this new source uses
`OriginalHeterogeneousEdgeStalk outerEdge = Pants.BoundaryInterface`
and `OriginalHeterogeneousEdgeStalk innerEdge = Pants.BranchChannel`.
These are *different source types*, with real original selected values
`Pants.selectedBoundary2`, `Pants.selectedChannel2` and
`Pants.innerInputChannel2`.

Exact source proof inventory:
- `realizeOriginalBoundary` and `realizeSourceEdge`: reconstruct
  the original selected-leg channel from the boundary stalk and the
  actually original selected-leg wave, basin and receipt; interpret
  the other original edge stalk directly.
- `originalOuterRealization`, `originalInnerRealization`: exact
  same-source identities of BOTH original channel values.
- `heterogeneousBeforeFabric`, `heterogeneousBeforeSection`:
  actual two-edge heterogeneous original `TypedHyperfabric` and
  compatible `GlobalSection` with two nonempty incidences.
- `selectedHeterogeneousPantsGluing` and
  `originalHeterogeneousInterfaceIsDonor`: an **inhabited**
  original `TypedHyperfabricPantsGluingBridgeExact.HyperfabricPantsGluing`
  using `Pants.outerInnerMatch` rather than inventing five
  equalities or assuming all arbitrary boundary channels match.
- `sourceRealizedEdgesMatch`: the actual admitted original seam
  preserves the full five-coordinate matched signature.
- `heterogeneousMergedFabric`, `heterogeneousMergedSection`:
  new single-seam edge, with both original endpoints incident,
  exact five-field transport and a compatible global section.
- `heterogeneousMergeIncidence`,
  `heterogeneousMergePreservesRestrictions`,
  `heterogeneousMergePreservesEdgeValues`: source-bound
  incidence and section/restriction commutation on BOTH edges.
- `heterogeneousMergedProvenanceExact`: provenance after the
  quotient is exactly the concatenation of BOTH original source
  provenance lists, not a generic claim of erasure or
  unsupported one-to-one full-channel equality.
- `heterogeneousEdgesReallyMerge` and the two
  `heterogeneous*IncidenceNonempty` declarations: merge is real.

Source commits: `cc75fba`, `610c2b5`. Canonical TOE imports:
`1abdc73`, `c3b7ba6`, `7ee44f8`.

### What is now closed and what is not

| Gate | Source-level verdict | Remaining qualification |
|---|---|---|
| **H2.02 selected original relational-pants heterogeneous seam** | **SOURCE-COMPLETE**: actual source-selected unequal edge stalks, full original five-field match, topology quotient, both restrictions and both original provenance lists | Agda 2.9 kernel check still open |
| H2.02 arbitrary heterogeneous *world* fabric | OPEN | independent ITIR/world original edge stalk maps, own empirical/source-proven channel match, full selected-world topology/provenance identification |
| H1.01 semantic | OPEN | original independent relational/group/Monster intended carrier equivalence, not numerical count or pants-address similarity |
| H2.01 operational | OPEN | genuine original ITIR nodes and selected commuting witness inhabiting `OriginalWorldCentralTransport` |
| Bishop P1 | OPEN | original source nested exp/atan analytic identity and Machin 1/5, 1/239 |
| Zeta P2 | OPEN | source canonical Nat powers and independently selected zeta equality |
| Gamma/Xi P3 | OPEN | source Gamma integral/continuation/functional equation/completed Xi |

Do not say the *entire H2.02 source-world programme* is closed:
this payment specifically closes the **original relational-pants
selected finite specimen**, not unsourced world-model semantics.
The mandatory source/kernal distinction remains explicit.


## Highest-alpha next tranche: signature-complete heterogeneous seam and Machin exact points

Source-writing date: 2026-11-09. **Neither new module has an Agda kernel
acceptance receipt.** Explicit tests, witness assumptions and attribution
boundaries are preserved below.

### H2.02 — original five-field signature is complete for InterfaceMatch

`DASHI/Reasoning/TypedHyperfabricPantsSignatureCompletenessExact.agda`
(source commit `55e311c`) proves
`signatureEqualityImpliesInterfaceMatch`:
equality of the original packed five-field boundary signature implies
the ORIGINAL
`RelationalBranchCobordismGeometry.InterfaceMatch`, by projecting
each of proposition, capacity, phase, wave and openness.

The converse is the original pre-existing
`TypedHyperfabricPantsNonvacuousSeamQuotientExact.interfaceMatchImpliesSignatureEquality`.
The new owner reuses it as
`signatureMatchSound` and `signatureMatchComplete`; additionally
`signatureMismatchBlocksInterfaceMatch` rules out any certificate
when packed signatures differ. This makes *one proved signature equality*
a sufficient source proof of the interface, rather than an unrelated
opaque field for each original observable. Labels/provenance are not
promoted into equalities.

### H2.02 — independent heterogeneous stalk types and all needed transport

`DASHI/Reasoning/TypedHyperfabricPantsSourceHeterogeneousTransportExact.agda`
(source commit `dcb9d9a`) contains parameterized
`HeterogeneousMatchedSource` with:
- independent types `LeftStalk` and `RightStalk`;
- original chosen `leftValue`, `rightValue`;
- original-source interpretation maps to existing
  `Pants.BranchChannel`;
- a **paid equality of the original five-field signatures**;
- two separately retained original source provenance lists.

For *every* such source payment, it constructs
`beforeFabric`, `beforeSection`,
`originalInterface`,
`admittedOriginalPantsSeam`,
`afterFabric`, `afterSection`,
`incidencePreserved`, `restrictionPreserved`,
`edgeValuePreserved`, `entireSourceProvenanceRetained`
and `bothSourceEdgesReallyMerge`.
This is a true two-incidence noninjective edge quotient on
the ORIGINAL `TypedHyperfabric` interface with genuinely
differently typed stalks. The named
`OriginalRelationalPants` specialization uses the original
`BoundaryInterface` / `BranchChannel` pair, original
`selectedBoundary2`, `innerInputChannel2`, original donor
realization, original `sourceRealizedEdgesMatch`, and actual
source provenance from the preceding selected H2.02 owner.
**No ITIR-world node, physical observation or group carrier is asserted.**

### P1 — original rational Gaussian Cayley evaluations at Machin points

`DASHI/Foundations/BishopMachinOriginalCayleyRationalPointAlgebraExact.agda`
(source commit `5779296`, import-mode correction `25e96c9`) proves
the ORIGINAL rational (Q[i]) denominator equations
`originalCayleyFiveDenominatorEquation` and
`originalCayley239DenominatorEquation` at the selected
original inputs (1/5) and (1/239).

The explicit target pairs are
`cayleyAtOneFifth = (12/13, 5/13)` and
`cayleyAtOneTwoHundredThirtyNinth = (28560/28561, 239/28561)`,
with all four coordinate declarations.
They solve ((1-it)z=1+it) using the repo's ORIGINAL rational
complex multiplication and solver. They are **finite rational
point algebra**, not evaluations of the original Bishop
`exp_B(2i atan_B(t))` analytic functions.
The convergence/composition/reindexing and actual source
same-function analytic identity remain OPEN.

Both H2.02 and P1 owners were imported in the three canonical TOE roots:
`c3df083`, `8dd914f`, `b305474`.

### Narrow exact remaining maximum cut

| Priority | Gate | Remaining actual theorem/evidence | Status |
|---|---|---|---|
| P0 | H2.02 selected typed heterogeneous pants | Original 5-field comparison ↔ InterfaceMatch, two source types, actual signature-paid seam, nonempty incidence quotient, restrictions, full source provenance lists | SOURCE-WRITTEN |
| P0 | H2.02 independently selected world fabric | Original ITIR/world edge-stalk interpretations, independently evidenced signature agreement, authentic topology/provenance transport beyond the two-incidence template | OPEN |
| P0 | H1.01 semantic | Original independent relational/group central completion as the constructed source 12+1 carrier, actual same-object identification | OPEN |
| P0 | H2.01 world | Independently supplied real world nodes and commuting observation/consumer maps to instantiate `OriginalWorldCentralTransport` | OPEN |
| P1 | Machin rational Cayley points | Original finite (Q[i]) denominator equations at 1/5 and 1/239 | SOURCE-WRITTEN |
| P1 | Bishop actual analytic Cayley | **Original nested** exp_C(2i atan_B(t)) identity as an analytic Bishop same-object equality; genuine limit/composition and the two actual analytic point witnesses | OPEN |
| P2 | Zeta | Source canonical-power identification and independently selected zeta equality | OPEN |
| P3 | Gamma/Xi | Original Mellin integral, continuation, functional equation and completed Xi | OPEN |

**No Agda 2.9 typechecking performed** on this tranche. Do not
promote SOURCE-WRITTEN into KERNEL-CHECKED or promote the finite
rational-point Cayley result into original analytic Machin.


## 2026-11-10 max-cut: exact SAME-SOURCE Machin phase and pre-existing P2 canonical powers

### P1: full finite rational Machin composition is now SOURCE-WRITTEN

New source owner:
`DASHI/Foundations/BishopMachinOriginalCayleyPhaseCompositionExact.agda`.

It reuses the original *same* Gaussian rational `Q[i]` carrier and the
two source-selected exact point values already paid in
`BishopMachinOriginalCayleyRationalPointAlgebraExact.agda`.

- `twoC`, `fourC` use the original `CD._*c_` with no shadow algebra.
- `originalFourfoldFiveEqualsImaginaryTimes239` proves literally
  `C(1/5)^4 = i × C(1/239)` for the original selected source
  Gaussian Cayley values.
- `originalCayleyMachinGaussianPhase` defines the entire
  original rational Machin phase product
  `C(1/5)^4 × conjugate(C(1/239))`.
- `originalCayleyMachinPhaseIsImaginaryUnit` proves that product
  is exactly the source original imaginary unit.
- `originalCayleyMachinPhaseRealIsZero` and
  `originalCayleyMachinPhaseImaginaryIsOne` expose both
  coordinate consequences by congruence.

Independent exact-fraction arithmetic checked:
`C(1/5)^4 = -239/28561 + (28560/28561)i`,
`C(1/239) = 28560/28561 + (239/28561)i`,
and the product with the conjugate is exactly `i`.
No numerical tolerance, π axiom or analytic arctangent shortcut.

Commits: `866ad95` original same-source phase proof;
`1185469` stronger fourfold identity;
golden TOE imports `68afac0`, `cab8a39`, `541dcc7`.

**Critical boundary:** this closes the actual exact finite Q[i]
Machin phase-composition *algebra*, NOT the original Bishop
same-function analytic theorem identifying
`exp_B(2i atan_B(t))` with `(1+it)/(1-it)`.
That still needs the original complex-valued Bishop exponential,
composition/convergence of the nested series, uniqueness and
the analytic point evaluation with its branch theorem.

### P2 prior-art attribution correction: canonical Nat powers ALREADY OWNED

Original source `DASHI/Foundations/BishopNatEmbeddingPowerExact.agda`
already proves `natRealPowNat` for **all Nat bases/exponents**,
commuting `DASHI.Mathematics.NumberTheory.FiniteDivisorPowerSumExact.powNat`
with the actual Bishop `Real.pow` on the original
`BishopCubicTranslationIteratedExact.natReal` embedding.
It also proves `natRealPowNatTimesBase`.
`DASHI/Foundations/BishopNatEmbeddingPowerValidation.agda`
already reuses both as regression theorems.

Thus the P2 *canonical power identification* was an **existing paid
mathematical theorem**, not an open challenge and not new work here.
The missing P2 theorem is **independently selected same-function
Riemann zeta equality** on the actual original analytic complex
carrier and its convergence/continuation domain, not a power lemma.
The existing `DASHI.Analysis.RiemannAnalyticSubstrate` explicitly
keeps those analytic fields uninhabited at this source level.

### Revised highest-alpha remaining leaves

| Priority | Gate | Exact outstanding mathematical proof |
|---|---|---|
| P0 | H1.01 | Independent original relational/group completion semantic equivalence, not count |
| P0 | H2.01 | Actually selected source-addressable ITIR nodes and commuting world observer/consumer |
| P0 | H2.02 world | Original independently evidenced world edge-stalk signatures and full-fabric topology/provenance identification |
| P1 | Bishop analytic | `exp_C(2i atan_B(t)) = C(t)` as a constructive Bishop same-function equality, followed by actual analytic evaluation at 1/5 and 1/239 and branch identification |
| P1 | Rational Machin algebra | Exact two point denominators, fourfold identity and full Gaussian phase product | 
| P2 | Canonical Nat powers | **ALREADY PAID IN ORIGINAL OWNER**, no new wrapper necessary |
| P2 | Same-function zeta | Independently selected analytic zeta equality, required half-plane convergence/continuation |
| P3 | Gamma/Xi | Actual source Mellin/Gamma integral, analytic continuation, functional equation, completed Xi |

**Verification:** source-written new declarations; a Python exact-fraction
calculation checked numerical rational identities independently.
Agda kernel acceptance is NOT claimed: no `agda` or `nix`
binary is present in the execution environment. No original world
nodes or analytic-source proof has been fabricated.


## 2026-11-10 decisive H1.01 original relational 144-to-13 semantic obstruction

**Prior-art audit correction: Machin already existed extensively in the repository.**
Do NOT attribute the original 1706 Machin construction, the convergent Bishop
arctangents, exact tangent arithmetic, branch control, Archimedes window or
Round11 setoid-complex source semantics to the 2026-11-09 Cayley-point work.
The original owners are:
- `BishopMachinArctanConstructionExact`: actual convergent Bishop arctans at
  1/5 and 1/239 and `bishopMachinPi`;
- `BishopMachinRationalTangentAlgebraExact`: two tangent doublings,
  subtraction and exact Machin rational identity;
- `BishopMachinQuarterAngleBranchExact`,
  `BishopMachinPiRationalWindowExact`,
  `BishopMachinPiArchimedesWindowExact`: branch and quantitative bounds;
- `BishopRound11MachinSetoidComplexInstanceExact`,
  `BishopRound11MachinEisensteinRouteBExact`, and
  `LeanRound11MachinCanonicalRouteBParityExact`: existing same-source
  transcendental packaging and Lean parity receipts, subject to the
  explicitly recorded exact-head replay/kernel caveats.
The recent `BishopMachinOriginalCayleyRationalPointAlgebraExact` and
`BishopMachinOriginalCayleyPhaseCompositionExact` are limited
Q[i] **finite-algebra** additions, NOT discovery of Machin or completion
of the original Bishop `exp(2i atan)` same-function proof.

### New highest-alpha H1.01 source proof: obstruction, section, selected image

`DASHI/Foundations/TernaryThirteenOriginalRelational144NonIdentificationExact.agda`
is a SAME-SOURCE theorem using the original `StageRelation144`
and `StageRelationField = (StageAxis12 × StageAxis12) → TriTruth` from
`StageTwelveGrothendieckRelationHyperformExact`.
It does not invent a group carrier or pretend equal counts identify
the original relational semantics.

- `relationToThirteen` observes all 12 original diagonal cells
  plus the selected ORIGINAL off-diagonal cell (0,1), encoding
  via the pre-existing `sourceCentralToThirteen`.
- `reverseCellRaised` changes only the *other ordered* cell
  (1,0) to `tri-high`, leaving the original diagonal and
  selected central (0,1) cell neutral.
- `diagonalCodesAgree`, `centralCellCodesAgree`,
  `originalThirteenCodeCollision` prove equality of the
  encoded 13-trit observations of `flatRelation` and
  `reverseCellRaised`.
- `reverseCellReallyDiffers` proves the selected original
  (1,0) relational consumer separates those states.
- `originalRelation144NonDescent`,
  `sourceThirteenCannotDetermineReverseCell`,
  `sourceThirteenCannotFactorReverseCell`:
  actual constructive counterexample to consumer descent
  from the original full relation field through the
  13-coordinate observation.
- `sourceThirteenCannotBeLosslessLeftInverse`:
  no reconstruction from this 13-trit code can recover ALL
  original ordered relational cells pointwise.
- `selectedRelationFromCentral` explicitly embeds the
  constructed original 12+1 source carrier into the original
  144-cell relational field, keeping diagonal entries,
  selected (0,1) centre, and choosing neutral for all other
  ordered relation cells.
- `selectedRelationDiagonalRecovers`,
  `selectedRelationCentreRecovers`,
  `selectedRelationThirteenCodeRoundTrip`:
  exact original diagonal and central recovery.
- `SelectedSourceRelation` and
  `selectedRelationImageInhabited`: witness-bearing
  **actual source subcarrier**, not all of the 144 fields.
- `thirteenCodeToSelectedRelation` and
  `sourceRelationCodeHasSection`: every 13-code has a
  canonical selected 144-field representative (split
  epimorphism for the coarse observation).
- `sameCanonicalRepresentativeForCollision` and
  `noPointwiseFullRelationReconstruction`: this section
  is not an inverse on the full 144-field, which retains
  independent relational information.

The correct H1.01 statement can therefore NOT be an
unqualified identification of the intended full 144-cell
relational field with the constructed 12+1 carrier via this
natural diagonal+one-cell observer. The user must select an
original *restricted relational subcarrier* (or an explicit
lossy quotient/consumer), prove it independently satisfies the
semantic group/relational contracts, and only THEN seek a
same-object identification. The available original owner
shows why cardinality alone cannot pay this.

Source commits: `3e9614c` counterexample,
`1c5a601` selected original subcarrier,
`317be40` explicit pair reduction corrections,
`bbc7be0` split observation section vs no full inverse.
Golden TOE roots: `10da9f9`, `cc91a7a`, `dbd6438`.

**H1.01 selected-observer nonidentification is SOURCE-WRITTEN;
not Agda-kernel checked.** No 144-field-to-13 isomorphism,
full-world semantics, Monster group identification, or analytic
Bishop evaluation is claimed. H2.01 still requires actual
independent ITIR world nodes and commuting maps; H2.02 still
requires source evidence for the independently selected world
fabric, not merely the pants specimen.

Remaining analytic P1: original Bishop nested exp/atan-to-Cayley
equality and the same-function analytic point witnesses.
P2: original canonical Nat powers were pre-existing and paid;
independent analytic zeta equality remains open.
P3: original Gamma integral, continuation, functional equation,
completed Xi remain open.


## 2026-11-11 highest-alpha: ORIGINAL relational 144 = observed 13 + residual 131 (pointwise)

New source owner:
`DASHI/Foundations/TernaryThirteenOriginalRelationResidualReopeningExact.agda`.

**Actual original object:** the 144-cell ordered `StageRelationField`
from `StageTwelveGrothendieckRelationHyperformExact`. The observed
13 cells are all 12 original diagonals and the specific directed
(0,1) relation; the residual is the other **131 independently
addressable ordered cells**, not a Monster or group completion.

- `maskUnobserved` makes the original 13 observed cells neutral,
  retaining the other 131 relation cells exactly.
- `reopenRelation` reconstructs the original 144 field by taking
  the 13 observed values from the existing `relationToThirteen`
  and the omitted cells from the actual masked residual.
- `reopenExactlyPointwise`: explicit proof for **all 144 ordered
  source addresses**, with 12 `valuationPointwiseRoundTrip`
  uses, one `toFromSource` at the central cell and 131 literal
  unchanged-cell cases.
- `reopenPreservesCoarseCode`: for **any** supplied residual,
  the 13-code obtained by reopening equals the starting code.
- `Residual131`: witness-bearing normalized residual, with
  neutrality proof for all twelve diagonal cells and the chosen
  central (0,1) cell. `maskToResidual131` inhabits it.
- `reopenNormalizedExact`,
  `reopenNormalizedCoarseRecovers` and
  `reopenNormalizedResidualRecoversAt`: both inverse
  directions for an **arbitrary code and normalized residual**,
  using 144 complete address cases in the second direction.
- `OriginalRelationalProductNormalForm` and
  `originalRelationalProductNormalForm`: explicit pointwise
  normal-form record for the original relational field.
  This is a (T^{13} × T^{131}) decomposition **at the level
  of addressed values and normalized residual evidence**, not a
  claim of propositional function equality or a semantic
  group/Monster isomorphism. No funext or postulates added.
- `fullRelationalObserver` and
  `allOriginalRelationCellsSufficient`: the pair of observed
  13-code + normalized 131-cell residual is sufficient for
  **every original indexed relation-cell consumer**.
- `originalRelationCodeSectioned`,
  `originalRelationFibreConstantRecovery` reuse the actual
  `SectionedProjectionProvenanceBridgeExact` to reconstruct
  precisely the observables which are constant on 13-code
  fibres. `reverseCellIsNotCoarseFibreConstant` gives the
  independently selected (1,0) counterexample.
- `differentOriginalResiduals` proves residuals separate
  exactly the two previously colliding original fields.

Commits `ddc73ee` (all original 144 cell recovery),
`cb6f5c1` (coarse-recovery + residual necessity),
`a577beb` (witness-normalized 131-residual and product
normal form), `326a77d` (all cell-consumer sufficiency
and original SectionedProjection weld). Golden imports:
`a460251`, `a39319d`, `59a635c`.

### Decisive status distinction

**SOURCE-WRITTEN**: exact observation+residual reopening of
the full original 144-cell relational source field, complete
pointwise both directions; arbitrary original relation-cell
consumers now descend through this lossless pair. This
closes the *finite relational reconstruction/residual
accounting* leaf of H1.01/H2.01.

**OPEN**: independently identify the intended relational/group
completion with a selected **semantic** 13-coordinate subcarrier
(or quotient with an explicitly limited consumer), or with this
larger exact 13+131 product; instantiate original ITIR-world
nodes and commuting observation/consumer fields; source-select
the full heterogeneous ITIR/world fabric edge matches.
No construction here provides an ITIR node, independent
Monster representation, legal/physical world authority,
or actual group equivalence.

P1 Bishop nested exp/atan analytic same-function identity,
P2 original independently selected analytic zeta equality,
and P3 Gamma/Xi original integral/continuation/functional
equation are unchanged and OPEN.

**Verification:** all new declarations are source-written;
Agda kernel typechecking has NOT run. Do not call the full
original 144 field equivalent to (T^{13}) alone. The
pointwise 13+131 reconstruction is the correct finite
information decomposition for the selected observation.


## 2026-11-11 continuation: universal original consumer factorization and relational transpose

**This tranche closes two precise source-level H1.01/H2.01 leaves, not the
independent ITIR/Monster semantic admission. Kernel checking remains open.**

### 1. Every pointwise-extensional original relational consumer factors

New owner:
`DASHI/Foundations/TernaryThirteenOriginalRelationConsumerUniversalityExact.agda`
(commit `c84d4c9`).

- `PointwiseEqual` is explicit equality at **each** original
  `StageRelation144` cell, not intensional equality of functions.
- `PointwiseExtensionalConsumer` retains both original
  `StageRelationField → Outcome` and evidence the consumer respects
  this pointwise relation.
- `reopenedFieldIsPointwiseOriginal` reuses the paid 144-address
  residual reopening theorem.
- `reconstructConsumer` explicitly evaluates the selected consumer
  on the decoded 13+131 state.
- `reconstructConsumerCommutes` proves that this is the
  original consumer on the original field.
- `everyExtensionalConsumerFactors` constructs the **original**
  `ObserverFactorizedRefinementExact.FactorizedRefinement`,
  not a weakened wrapper or new unverified admission record.
- `everyExtensionalConsumerIsSufficient` proves sufficiency through
  the original consumer-descent API.
- `originalCellConsumerExtensional`,
  `everyOriginalCellExplicitlyFactors`: same-source complete
  144-cell indexed consumer instantiation.
- `reverseCellStillDoesNotFactorThroughCoarse` explicitly retains
  the original (1,0) counterexample for the 13-code alone.

This is universal **for independently supplied pointwise-extensional
consumers on the original relation field**, and does not assert that
all external world/ITIR consumers are the same field functions.

### 2. Original relation transpose makes the coarse quotient non-functorial

New owner:
`DASHI/Foundations/TernaryThirteenOriginalRelationalTransposeDescentExact.agda`
(commit `08275e5`).

- `transposeCentralConsumer`, `transposeCentralIsReverseCell`
  use the ORIGINAL `StageTwelveGrothendieckRelationHyperformExact.transposeRelation`,
  whose directed transposition sends the *unobserved* (1,0)
  cell into the selected central (0,1) cell.
- `transposedCentralNonDescent` and
  `transposeCentralCannotFactorThroughCoarse` prove the original
  central consumer AFTER transpose does not descend through the
  13-code observer BEFORE transpose.
- `originalRelationCodeCentralRecovers` recovers the actual
  source selected centre from the original word codec.
- `transposeCodeCannotDescend` is strictly stronger: **no**
  `TritWord 13 → TritWord 13` map can commute with the
  original 144-field transpose on all source fields.
- `transposeOnFullObservation` is an actual operation on the
  full 13-code+normalized-131 residual carrier.
- `transposeFullObservationRecoversAt` proves its decoded
  output equals the original transposed source field at every
  original relation cell. This is exact, pointwise, and
  assumes no funext.

This is a specific mathematical explanation for the retained
residual: it is necessary even to preserve an ORIGINAL
relational symmetry/dynamics operation. Thus a proposed
semantic 13-dimensional quotient must independently specify
which transformations and consumers it is allowed to discard.

### 3. Finite independent data regression

New executable original-data-model regression:
`scripts/check_ternary13_original_relation_residual.py`
(commit `9969acf`).

- Enumerates all 144 source ordered addresses,
  13 retained and 131 residual.
- Checks exactly 864 single-address trit basis and inverse
  cases, plus zero-field.
- Confirms that changing source (1,0) leaves the coarse
  observation unchanged while changing the residual.
- The standalone finite arithmetic regression passed locally;
  this is **not an Agda kernel proof** and does not certify
  the Agda source imports.

TOE roots: consumer module `afa7140`, `c999240`,
`885ed81`; transpose module `37af950`, `5818e96`,
`f42c9d4`.

### Corrected remaining highest-alpha exact cut

| Priority | Gate | Precise status and next unpaid work |
|---|---|---|
| P0 | H1.01 original source relational information | **SOURCE-WRITTEN** pointwise 13+131 normal form and universal extensional-consumer factorization |
| P0 | H1.01 original relation transpose | **SOURCE-WRITTEN** proof transpose cannot descend through coarse 13 alone; does transport over full 13+131 |
| P0 | H1.01 independently intended group completion | OPEN: identify a specifically selected original relational subcarrier/quotient and independently justify its group action, intended semantics and allowed consumers |
| P0 | H2.01 original 144-cell consumers | **SOURCE-WRITTEN** all indexed cells and any explicitly pointwise-extensional consumer factor through full 13+131 |
| P0 | H2.01 ITIR-world node bridge | OPEN: genuine original nodes, independent world→source mapping, commuting consumer/observer maps and appropriate world operational evidence |
| P0 | H2.02 independently selected world-fabric seam | OPEN: actual independently sourced heterogeneous world edge-stalk maps and complete 5-field evidence, larger-fabric topology/provenance transport |
| P1 | Bishop analytic Cayley | OPEN: original source analytic nested exponential/atan same-function equality; do not duplicate pre-existing Machin construction |
| P2 | Independently selected zeta | OPEN: original analytic zeta equality with independently validated convergence/continuation (Nat power lemma already owned) |
| P3 | Gamma/Xi | OPEN: original Gamma integral, analytic continuation, functional equation, completed Xi |

**Verification:** source-written (no Agda binary available); do not
promote to KERNEL-CHECKED. The Python finite regression is a separate
algorithmic cross-check and carries no original-world semantic claim.


## 2026-11-11 original finite Heisenberg group owner: H1.01 SAME-CARRIER result

**Prior-art correction and highest-alpha proof:** the repository already
has the ACTUAL finite 3B Heisenberg central extension
`DASHI/Moonshine/Monster3BFiniteHeisenbergCentralExtensionExact.agda`:
`Heisenberg6` is six translation plus six modulation coordinates
over F3, together with a central F3 phase. `compose` includes
the genuine `dot6` cocycle. The original associativity and inverse
theorem owners are
`Monster3BFiniteHeisenbergAssociativityExact` and
`Monster3BFiniteHeisenbergInverseExact`. DO NOT mistake
`RelationalAppraisalPointedPhaseExact.centralCompletionGroupOrderPattern`
(a count) for proof of this original group law.

New source owner:
`DASHI/Foundations/TernaryThirteenOriginalHeisenbergGroupCarrierExact.agda`.

The construction uses original group/source types only, not a
cardinality-only group placeholder:

- `toWordTrit`/`fromWordTrit` with both three-case inverses
  between original `DASHI.Algebra.Trit.Trit` and existing
  thirteen-fibre `Trit`.
- `x6ToWord`/`wordToX6` with both six-coordinate inverse
  theorems for the original finite `Monster3BFiniteHeisenbergGeneratorsExact.X6`.
- `originalGroupToWord`/`wordToOriginalGroup` use the
  actual six+six+one quotient/centre split and the original
  `TritWord 13`, with **both full inductive word/group round
  trips** `originalGroupRoundTrip`, `originalWordRoundTrip`.
- `wordCompose`, `wordIdentity`, `wordInverse` are
  *transported from the original nonabelian cocycle-bearing
  `Heisenberg6`*, not componentwise ternary addition;
  `originalMultiplicationRespected`,
  `wordMultiplicationDecoded`,
  `originalIdentityRespected`,
  `originalInverseRespected`,
  `originalAssociativityRespected` reuse original laws.
- `sourceTranslation`/`sourceModulation` specialize the
  original nontrivial dual generator pair at `axis0`;
  `sourceTranslationModulationPhase`,
  `sourceModulationTranslationPhase`,
  `originalGeneratorOrderMatters`,
  `wordGeneratorOrderMatters` give an explicit
  noncommuting witness after transporting the true group law.
- `originalGroupToSource`/`sourceToOriginalGroup` compose
  the actual finite group coding with the already-owned
  `TernaryThirteenOriginalAxisValuationBridgeExact` and
  original `Rel.SourceCentralCompletionCarrier`.
  `originalGroupSourceRoundTrip` is an exact group-side
  equality. `sourceOriginalGroupRoundTripAxis` is the
  original twelve-axis pointwise inverse and
  `sourceOriginalGroupRoundTripCentre` is the exact centre
  inverse (no unproved function extensionality).
- `sourceCentralCompose` and
  `sourceCentralGroupCompositionOnAxes/OnCentre` establish
  the cocycle-bearing group multiplication transported into
  the originally constructed 12+centre valuation.

Commits `469e89d` original 13-word Heisenberg carrier,
`e7fd2a9` actual source 12+centre correspondence and
transported multiplication, `758ec77` explicit inverse-based
noncommutativity argument. Golden roots:
`36be2ef`, `0d67633`, `a444539`.

### What this pays, and what remains independent

**SOURCE-WRITTEN H1.01 finite group SAME-CARRIER gate:**
the independently existing, nonabelian *finite Heisenberg group*
has an exact 13-word representation and a pointwise same-carrier
identification with the already-constructed original twelve-axis
plus central trit valuation. This is stronger than merely
matching `3^(1+12)`: its original nontrivial group law and
generator commutator are preserved.

**NOT PAID:** an independently sourced claim that the
biological/appraisal relation semantically **is** this Heisenberg
group; identity with the full original 144-cell relation field
(previously disproved for the diagonal+centre observer);
the specific Monster 3B group or VOA action identification;
a genuine ITIR semantic-world state correspondence and consumer;
or independently selected full world-fabric edge-stalk match.
Those are different same-object/physical/epistemic admissions.
The transported operation is NOT coordinatewise ternary addition.

P1 original Bishop analytic exp/atan Cayley, P2 selected analytic
zeta identity and P3 source Gamma/Xi remain OPEN.
**Kernel status:** source-written only, no Agda compiler acceptance
receipt. The original finite Heisenberg group laws' older source
owners are reused but this new bridge has not been typechecked.


### 2026-11-11: the genuine original Heisenberg law on the selected 144-relation IMAGE

Additional new source:
`DASHI/Foundations/TernaryThirteenOriginalHeisenbergRelationalImageExact.agda`
(commit `dec862d`).

This takes the actual original `Heisenberg6` group
and embeds its exact thirteen-coordinate code into the
**selected** image of the original
`StageTwelveGrothendieckRelationHyperformExact.StageRelationField`.

- `sourceGroupToOriginalRelation`: genuine original group
  element -> original 12+centre valuation -> 144-address relation,
  with the other 131 original ordered cells neutral.
- `originalRelationToSelectedGroup`: original directed relation
  observation -> 13-code -> actual original finite group element.
- `originalGroupRecoveredFromSelectedRelation`: full equality
  of original Heisenberg group elements after that selected
  original-relation embedding/recovery.
- `groupImageIsOriginalSelectedRelation`: embeds each group element
  as a witness-bearing inhabitant of the original
  `SelectedSourceRelation` subcarrier.
- `selectedRelationGroupCompose`: original cocycle-bearing
  group composition transported to the selected relation image.
- `selectedRelationProductIsGroupProductAt`: exact same
  source multiplication at **every one of the 144 original
  ordered relation addresses**.
- `selectedRelationProductIsSelected`: the group operation
  is closed under the selected *actual original relational
  image*, not merely a stand-alone 13-word type.

All three canonical TOE roots import the source (`7002576`,
`1371457`, `286b3d4`).

**Updated P0 gate: H1.01 original finite group carrier and
selected 144-relation-image multiplication = SOURCE-WRITTEN.**
The group-side carrier round trip and cocycle are genuine source
results. **Still OPEN:** independent evidence that the intended
*relational/appraisal/group/Monster semantics* selects precisely
this group/operation (rather than a different quotient),
actual ITIR nodes and observer/consumer maps, and heterogeneous
world-edge-fabric source admission. The entire arbitrary
144-relation field remains a larger carrier with 131 independent
residual values; the selected group multiplication is not claimed
as an existing group operation on the unrestricted 144-field.

Kernel receipt: none in the current environment. Do not label
new group bridge Agda-verified until Nix/Agda 2.9 checks imports.
