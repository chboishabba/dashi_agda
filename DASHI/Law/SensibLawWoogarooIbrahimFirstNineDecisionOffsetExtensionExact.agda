module DASHI.Law.SensibLawWoogarooIbrahimFirstNineDecisionOffsetExtensionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Wikimedia.IdentifierExact as Id
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Ibrahim
import DASHI.Law.SensibLawWoogarooIbrahimDeweyQidLegalAtomExact as Canonical
import DASHI.Law.SensibLawWoogarooIbrahimFirstNineMonitoringExtensionExact as FirstNine
import DASHI.Law.SensibLawWoogarooLegalConsumerAtomCompletionExact as Atom

------------------------------------------------------------------------
-- THIN FIRST NINE DECISION / OFFSET COMPARATOR EXTENSION
--
-- Primary Commonwealth FOI decision material for EPBC 2016/7676 adds a useful
-- nearby comparator: the recommendation capped clearing at 46.2 ha of Koala
-- habitat and required an offset gain in habitat quality within 20 years.
-- This remains a different approval and does not become the legal standard or
-- factual offset performance for EPBC 2019/8575.
------------------------------------------------------------------------

brookwaterQid : Id.ItemId
brookwaterQid = Id.itemId "Q4975216"

koalaQid : Id.ItemId
koalaQid = Id.itemId "Q36101"

lawDewey : String
lawDewey = "344.046"

conservationDewey : String
conservationDewey = "333.95"

firstNineRecommendationSource : Source.AttributedSource
firstNineRecommendationSource = Source.mkNoDOISource
  "Department of the Environment and Energy"
  "Recommendation Report — First Nine master planned residential development, Brookwater, Qld (EPBC 2016/7676)"
  "FOI disclosure 190207, Part 5"
  "2019"
  "https://www.agriculture.gov.au/sites/default/files/documents/190207-part5.pdf"
  Source.governmentSource
  "Primary Commonwealth decision-record carrier. The recommendation records a condition that no more than 46.2 ha of Koala habitat be cleared and an offset condition requiring a gain in Koala habitat quality across the offset site within 20 years of decision. Used as an adjacent-project comparator for decision architecture, offset timing and restoration lag; not as the governing condition for 2019/8575."
  Source.publicAttribution

firstNineProposedDecisionSource : Source.AttributedSource
firstNineProposedDecisionSource = Source.mkNoDOISource
  "Department of the Environment and Energy"
  "Proposed Approval — First Nine master planned residential development, Brookwater, Qld (EPBC 2016/7676)"
  "FOI disclosure 190207, Part 6"
  "2019"
  "https://www.agriculture.gov.au/sites/default/files/documents/190207-part6.pdf"
  Source.governmentSource
  "Primary Commonwealth proposed-decision carrier identifying the approval holder, action, ss 18/18A approval pathway and proposed conditions. Used for exact approval-object lineage only; proposed-decision status must not be collapsed into the signed final decision without the signed carrier."
  Source.publicAttribution

foi190207Source : Source.AttributedSource
foi190207Source = Source.mkNoDOISource
  "Department of Agriculture, Fisheries and Forestry — disclosure log for former Department of the Environment and Energy records"
  "FOI 190207 — signed proposed approval decision briefs and final approval decision briefs"
  "Commonwealth FOI disclosure log"
  "2019"
  "https://www.agriculture.gov.au/about-us/freedom-information/foi-disclosure-log/190207"
  Source.governmentSource
  "Primary provenance/index carrier identifying EPBC 2016/7676 among the released decision-brief document set. It establishes acquisition lineage, not ecological or legal conclusions by itself."
  Source.publicAttribution

firstNineDecisionAtlas : Source.AttributedSourceAtlas
firstNineDecisionAtlas = Source.mkSourceAtlas
  "Woogaroo First Nine Commonwealth decision/offset comparator"
  "DASHI.Law.SensibLawWoogarooIbrahimFirstNineDecisionOffsetExtensionExact"
  (foi190207Source ∷ firstNineRecommendationSource ∷ firstNineProposedDecisionSource ∷ [])
  "Primary Commonwealth FOI/decision carriers for a nearby but different EPBC project. DOI is not applicable. Brookwater QID Q4975216, Koala QID Q36101 and Dewey coordinates are navigation only; the comparator does not set the legal or factual outcome for 2019/8575."

firstNineDecisionCoordinate : Ibrahim.DashiKnowledgeCoordinate
firstNineDecisionCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimFirstNineDecisionOffsetExtensionExact.agda"
  "EPBC 2016/7676 First Nine decision/offset architecture"
  lawDewey
  (Id.rawItemId brookwaterQid)
  "primary: Commonwealth FOI 190207 decision records"

firstNineOffsetCoordinate : Ibrahim.DashiKnowledgeCoordinate
firstNineOffsetCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimFirstNineDecisionOffsetExtensionExact.agda"
  "First Nine Koala offset gain / restoration-time comparator"
  conservationDewey
  (Id.rawItemId koalaQid)
  "primary: FOI 190207 Part 5 recommendation report"

firstNineDecisionToCurrentOffsetAudit : Ibrahim.DashiFirstLinkEdge
firstNineDecisionToCurrentOffsetAudit = Ibrahim.dashi-first-link-edge
  firstNineOffsetCoordinate Canonical.s102StatutoryCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "A nearby approval expressly allowed a long period for offset habitat-quality gain, illustrating that restoration function may be temporally delayed. This is useful when framing restoration-lag questions but does not determine s 102 or current-project offset adequacy."
  true

record FirstNineDecisionReceipt : Set where
  constructor first-nine-decision-receipt
  field
    epbcReference : String
    maximumKoalaHabitatClearingHa : String
    offsetGainPeriodYears : String
    sameObjectAs2019_8575 : Bool
    sameProducerAsSpringviewEcology : Bool
    independentCommonwealthDecisionCarrier : Bool

open FirstNineDecisionReceipt public

currentFirstNineDecisionReceipt : FirstNineDecisionReceipt
currentFirstNineDecisionReceipt = first-nine-decision-receipt
  "EPBC 2016/7676"
  "46.2"
  "20"
  false
  false
  true

record ComparatorAtomBinding : Set where
  constructor comparator-atom-binding
  field
    atom : Atom.LegalExecutionAtom
    consumer : Atom.LegalExecutionConsumer
    admissibleAsComparator : Bool
    sameObjectPaid : Bool
    consumerComplete : Bool
    contribution : String
    residual : String

open ComparatorAtomBinding public

firstNineToOffsetLag : ComparatorAtomBinding
firstNineToOffsetLag = comparator-atom-binding
  Atom.offsetRestorationLagAtom
  Atom.epbc8575OffsetAdequacyConsumer
  true false false
  "A primary Commonwealth recommendation for the nearby First Nine approval expressly contemplated up to 20 years to achieve offset habitat-quality gain. This source-pays the existence of a long restoration horizon in that adjacent approval."
  "Obtain the actual 2019/8575 final offset conditions, baseline condition, maturity, management actions and performance timeframes. Do not transfer the 20-year First Nine condition into the current project."

firstNineToOffsetMaturity : ComparatorAtomBinding
firstNineToOffsetMaturity = comparator-atom-binding
  Atom.offsetVegetationMaturityAtom
  Atom.epbc8575OffsetAdequacyConsumer
  true false false
  "The First Nine decision plus later monitoring create a local longitudinal comparator for the distinction between an offset commitment and later realised habitat function."
  "Compare the final 2019/8575 offset parcels against the mature-existing Springview impact habitat on condition, existing protection, planted/regrowth status and time to demonstrated Koala use."

existingMonitoringReceipt : FirstNine.FirstNineKoalaMonitoringReceipt
existingMonitoringReceipt = FirstNine.currentFirstNineReceipt

------------------------------------------------------------------------
-- Investigative consequence.
------------------------------------------------------------------------

record FirstNineDecisionPareto : Set where
  constructor first-nine-decision-pareto
  field
    primaryDecisionRecordLocated : Bool
    clearingCapLocated : Bool
    longOffsetGainPeriodLocated : Bool
    adjacentMonitoringLocated : Bool
    auditSummaryLocated : Bool
    exactAuditConditionIdentityLocated : Bool
    nextCut : String

currentFirstNineDecisionPareto : FirstNineDecisionPareto
currentFirstNineDecisionPareto = first-nine-decision-pareto
  true true true true true false
  "The comparator is now sufficiently paid for offset-time/maturity questions. Do not spend more time on generic First Nine material unless the exact 2025 audit conditions surface cheaply; return to local WildNet/Biolink population drill-down and the final 2019/8575 offset carrier."

------------------------------------------------------------------------
-- WrongType / attribution boundaries.
------------------------------------------------------------------------

data FirstNineClearingCapEqualsSpringviewCap : Set where
data FirstNineOffsetPeriodEquals2019_8575OffsetPeriod : Set where
data NearbyDecisionEqualsLegalPrecedentBindingCurrentDecision : Set where
data ProposedDecisionEqualsSignedFinalDecision : Set where
data TwentyYearsEqualsOffsetAdequacy : Set where

firstNineCapDoesNotBecomeSpringviewCap : FirstNineClearingCapEqualsSpringviewCap → ⊥
firstNineCapDoesNotBecomeSpringviewCap ()

firstNinePeriodDoesNotBecomeCurrentPeriod : FirstNineOffsetPeriodEquals2019_8575OffsetPeriod → ⊥
firstNinePeriodDoesNotBecomeCurrentPeriod ()

nearbyDecisionDoesNotBindCurrentDecision : NearbyDecisionEqualsLegalPrecedentBindingCurrentDecision → ⊥
nearbyDecisionDoesNotBindCurrentDecision ()

proposedDoesNotBecomeSignedFinal : ProposedDecisionEqualsSignedFinalDecision → ⊥
proposedDoesNotBecomeSignedFinal ()

longPeriodDoesNotProveAdequacy : TwentyYearsEqualsOffsetAdequacy → ⊥
longPeriodDoesNotProveAdequacy ()
