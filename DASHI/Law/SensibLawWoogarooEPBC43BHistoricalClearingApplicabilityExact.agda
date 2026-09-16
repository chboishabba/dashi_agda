module DASHI.Law.SensibLawWoogarooEPBC43BHistoricalClearingApplicabilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Law.SensibLawWoogarooEPBC43BLongUnclearedClearingExact as S43B

------------------------------------------------------------------------
-- WOOGAROO EPBC s 43B HISTORICAL-CLEARING APPLICABILITY
--
-- This owner answers a narrower question than the Part 9 merits case:
-- is there presently any identified Woogaroo/Springview clearing action for
-- which reliance on the lawful-continuation exemption under s 43B is actually
-- in issue? If so, what historical facts must be proved after the 15-year
-- carve-out introduced from 1 December 2025?
------------------------------------------------------------------------

data ApplicabilityState : Set where
  reliedUpon : ApplicabilityState
  plausibleButUnproved : ApplicabilityState
  noCurrentRelianceLocated : ApplicabilityState
  notApplicable : ApplicabilityState

record S43BApplicabilityGate : Set where
  constructor s43b-applicability-gate
  field
    currentState : ApplicabilityState
    exactClearingActionIdentified : Bool
    s43BRelianceDocumentIdentified : Bool
    planningExemptionIsSeparate : Bool
    alreadyReferredPart9ActionIsSeparate : Bool
    historicalClearingAnalysisWorthRunning : Bool
    nextTrigger : String

open S43BApplicabilityGate public

currentWoogarooS43BGate : S43BApplicabilityGate
currentWoogarooS43BGate = s43b-applicability-gate
  noCurrentRelianceLocated
  true
  false
  true
  true
  true
  "Activate the full s 43B parcel-history test only if a proponent/agency/council record relies on lawful continuation of pre-EPBC land use, or if a distinct clearing action is said not to require Part 9 approval for that reason. The present 2019/8575 referral is already a controlled action and its merits are a separate consumer."

------------------------------------------------------------------------
-- Historical evidence needed if the exemption is invoked.
------------------------------------------------------------------------

data HistoricalClearingEvidenceKind : Set where
  exactActionPolygon : HistoricalClearingEvidenceKind
  pre2000LandUseEvidence : HistoricalClearingEvidenceKind
  clearingHistory15Years : HistoricalClearingEvidenceKind
  forestryStatus : HistoricalClearingEvidenceKind
  specificEnvironmentalAuthorisation : HistoricalClearingEvidenceKind
  significantImpactContext : HistoricalClearingEvidenceKind

record HistoricalClearingRequirement : Set where
  constructor historical-clearing-requirement
  field
    kind : HistoricalClearingEvidenceKind
    currentPaid : Bool
    requirement : String
    whyNeeded : String
    boundary : String

open HistoricalClearingRequirement public

exactActionPolygonRequirement : HistoricalClearingRequirement
exactActionPolygonRequirement = historical-clearing-requirement
  exactActionPolygon
  true
  "Use the exact clearing action under examination, not the whole estate or referral area. A12705838 provides an approved local works/clearing surface for 9281, but a claimed s 43B exemption must still be tied to the specific Commonwealth action said to be exempt."
  "The 15-year history applies to the land from which vegetation is proposed to be cleared."
  "Local approved geometry does not prove that s 43B is being relied on for that same action."

pre2000UseRequirement : HistoricalClearingRequirement
pre2000UseRequirement = historical-clearing-requirement
  pre2000LandUseEvidence
  false
  "Identify the exact use of land said to have been occurring immediately before commencement of the EPBC Act and show that the present action is genuinely a continuation of that use."
  "Section 43B is a continuation-of-use exemption, not a generic old-development-approval exemption."
  "An old planning approval, estate masterplan or historical ownership record does not by itself prove continuity of the relevant pre-EPBC use."

fifteenYearHistoryRequirement : HistoricalClearingRequirement
fifteenYearHistoryRequirement = historical-clearing-requirement
  clearingHistory15Years
  false
  "For each exact clearing area, reconstruct whether the land has been cleared of vegetation at any time during the 15 years before the proposed action."
  "From 1 December 2025, s 43B(1) cannot be relied on for vegetation clearing where the land has not been cleared for at least 15 years, unless the forestry-operation exception applies."
  "Mature-looking forest, canopy height or one historical aerial image is not enough to establish the complete legal clearing history."

forestryRequirement : HistoricalClearingRequirement
forestryRequirement = historical-clearing-requirement
  forestryStatus
  false
  "Determine whether the exact action is a forestry operation for the statutory exception."
  "The 15-year carve-out contains a forestry-operation exception."
  "Presence of planted trees, regrowth or timber species does not automatically make the action a forestry operation."

authorisationRequirement : HistoricalClearingRequirement
authorisationRequirement = historical-clearing-requirement
  specificEnvironmentalAuthorisation
  false
  "Check whether the pre-EPBC action was authorised by a specific environmental authorisation that remains in force, because that points to s 43A rather than s 43B."
  "The Act itself separates the specific-authorisation and lawful-continuation routes."
  "Local planning approval is not automatically the specific environmental authorisation contemplated by the Commonwealth provision."

------------------------------------------------------------------------
-- Current Woogaroo conclusion.
------------------------------------------------------------------------

record CurrentS43BConclusion : Set where
  constructor current-s43b-conclusion
  field
    livePart9MeritsRouteDominates : Bool
    currentS43BRelianceLocated : Bool
    historicalAerialWorkStillUseful : Bool
    currentExemptionOutcomeEstablished : Bool
    practicalUse : String

currentS43BConclusion : CurrentS43BConclusion
currentS43BConclusion = current-s43b-conclusion
  true
  false
  true
  false
  "Treat s 43B as a conditional exemption-audit lane, not as the main Woogaroo merits argument. Historical aerials/canopy-change data should be preserved because they can later test the 15-year carve-out if reliance on s 43B appears, while also serving habitat-maturity/restoration-lag analysis."

------------------------------------------------------------------------
-- Attribution.
------------------------------------------------------------------------

epbc43BSource : Source.AttributedSource
epbc43BSource = Source.mkNoDOISource
  "Office of Parliamentary Counsel / Commonwealth of Australia"
  "Environment Protection and Biodiversity Conservation Act 1999 — section 43B"
  "Federal Register of Legislation — current compiled Act"
  "2026"
  "https://www.legislation.gov.au/C2004A00485/latest/text"
  Source.governmentSource
  "Primary statutory source for lawful continuation of land use, the specific-authorisation exclusion, the 15-year vegetation-clearing carve-out and the forestry exception."
  Source.publicAttribution

dcceew43BGuidance : Source.AttributedSource
dcceew43BGuidance = Source.mkNoDOISource
  "Department of Climate Change, Energy, the Environment and Water"
  "Reforms to land clearing exemptions"
  "DCCEEW EPBC reform guidance"
  "2026"
  "https://www.dcceew.gov.au/environment/epbc/epbc-act-reform/agricultural-action-exemptions"
  Source.governmentSource
  "Official guidance explaining the 1 December 2025 commencement and the 15-year vegetation-clearing limit on reliance on s 43B."
  Source.publicAttribution

s43BApplicabilitySourceAtlas : Source.AttributedSourceAtlas
s43BApplicabilitySourceAtlas = Source.mkSourceAtlas
  "Woogaroo s 43B historical-clearing applicability source atlas"
  "DASHI.Law.SensibLawWoogarooEPBC43BHistoricalClearingApplicabilityExact"
  (epbc43BSource ∷ dcceew43BGuidance ∷ [])
  "No source presently located shows that the proponent relies on s 43B for the 2019/8575 action. The module therefore keeps the historical-clearing lane conditional."

------------------------------------------------------------------------
-- WrongType / no-promotion boundaries.
------------------------------------------------------------------------

data PlanningExemptionEqualsS43B : Set where
data ControlledActionEqualsS43BIrrelevantEverywhere : Set where
data FifteenYearForestEqualsS43BFailureWithoutUseAnalysis : Set where
data HistoricalCanopyEqualsContinuousLandUse : Set where

data NoS43BRelianceLocatedEqualsNoPossibleS43BIssue : Set where

planningExemptionDoesNotEqualS43B : PlanningExemptionEqualsS43B → ⊥
planningExemptionDoesNotEqualS43B ()

controlledActionDoesNotEraseSeparateS43BIssues : ControlledActionEqualsS43BIrrelevantEverywhere → ⊥
controlledActionDoesNotEraseSeparateS43BIssues ()

fifteenYearForestDoesNotFinishTheAnalysis : FifteenYearForestEqualsS43BFailureWithoutUseAnalysis → ⊥
fifteenYearForestDoesNotFinishTheAnalysis ()

historicalCanopyDoesNotProveContinuousUse : HistoricalCanopyEqualsContinuousLandUse → ⊥
historicalCanopyDoesNotProveContinuousUse ()

noCurrentRelianceDoesNotProveImpossible : NoS43BRelianceLocatedEqualsNoPossibleS43BIssue → ⊥
noCurrentRelianceDoesNotProveImpossible ()
