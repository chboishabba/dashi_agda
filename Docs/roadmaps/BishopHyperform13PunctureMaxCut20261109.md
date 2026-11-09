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
