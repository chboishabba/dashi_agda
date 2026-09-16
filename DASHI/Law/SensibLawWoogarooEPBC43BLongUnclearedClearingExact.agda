module DASHI.Law.SensibLawWoogarooEPBC43BLongUnclearedClearingExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- EPBC s 43B — LONG-UNCLEARED LAND / CONTINUATION-OF-USE BOUNDARY
--
-- Source-level formalisation of the post-1-December-2025 narrowing of the
-- lawful-continuation exemption. This is a separate consumer from the live
-- Part 9 merits decision for EPBC 2019/8575 and does not by itself determine
-- whether any Springview clearing is exempt, approved, prohibited or unlawful.
------------------------------------------------------------------------

record S43BCurrentRule : Set where
  constructor s43b-current-rule
  field
    continuationExemptionExists : Bool
    longUnclearedCarveoutExists : Bool
    longUnclearedThresholdYears : String
    forestryOperationExceptionExists : Bool
    gbr50mCarveoutExists : Bool
    changeEffectiveDate : String

open S43BCurrentRule public

currentS43BRule : S43BCurrentRule
currentS43BRule = s43b-current-rule
  true
  true
  "15"
  true
  true
  "1 December 2025"

record Woogaroo43BQuestion : Set where
  constructor woogaroo43b-question
  field
    exactAction : String
    exactParcelHistoryNeeded : Bool
    fifteenYearClearingHistoryNeeded : Bool
    forestryOperationStatusNeeded : Bool
    significantImpactQuestionStillSeparate : Bool
    currentAnswerProved : Bool
    nextEvidence : String

open Woogaroo43BQuestion public

woogaroo43BQuestion : Woogaroo43BQuestion
woogaroo43BQuestion = woogaroo43b-question
  "Any present or future clearing action for which a party might rely on EPBC Act s 43B lawful-continuation-of-use rather than Part 9 approval."
  true
  true
  true
  true
  false
  "For each exact clearing area, obtain historical aerial/vegetation-clearance evidence covering at least the preceding 15 years, identify the claimed pre-EPBC land use and any specific environmental authorisation, and determine whether the action is a forestry operation."

------------------------------------------------------------------------
-- Why this is not automatically the main 2019/8575 merits route.
------------------------------------------------------------------------

record ConsumerSeparation : Set where
  constructor consumer-separation
  field
    s43BExemptionConsumer : String
    epbc8575Part9Consumer : String
    sameFactsMayInformBoth : Bool
    oneDeterminesTheOther : Bool

currentConsumerSeparation : ConsumerSeparation
currentConsumerSeparation = consumer-separation
  "Does s 43B exempt a particular clearing action from needing Part 9 approval as a lawful continuation of pre-EPBC land use?"
  "Should the already-referred EPBC 2019/8575 action be approved, refused or conditioned under the applicable Part 9 framework?"
  true
  false

------------------------------------------------------------------------
-- Source attribution.
------------------------------------------------------------------------

epbcActCurrentSource : Source.AttributedSource
epbcActCurrentSource = Source.mkNoDOISource
  "Office of Parliamentary Counsel / Commonwealth of Australia"
  "Environment Protection and Biodiversity Conservation Act 1999 — section 43B"
  "Federal Register of Legislation, current compiled Act"
  "2026"
  "https://www.legislation.gov.au/C2004A00485/latest/text"
  Source.governmentSource
  "Primary statutory source for the lawful-continuation exemption and the 15-year/forestry-operation and GBR-catchment carve-outs."
  Source.publicAttribution

dcceewLandClearingSource : Source.AttributedSource
dcceewLandClearingSource = Source.mkNoDOISource
  "Department of Climate Change, Energy, the Environment and Water"
  "Reforms to land clearing exemptions"
  "DCCEEW EPBC Act reform guidance"
  "2026"
  "https://www.dcceew.gov.au/environment/epbc/epbc-act-reform/agricultural-action-exemptions"
  Source.governmentSource
  "Official explanatory guidance stating that from 1 December 2025 the s 43B continuation exemption cannot be relied on for vegetation not cleared in the previous 15 years, unless the action is a forestry operation, and explaining the separate GBR 50 m carve-out."
  Source.publicAttribution

s43BSourceAtlas : Source.AttributedSourceAtlas
s43BSourceAtlas = Source.mkSourceAtlas
  "Woogaroo EPBC s 43B long-uncleared clearing source atlas"
  "DASHI.Law.SensibLawWoogarooEPBC43BLongUnclearedClearingExact"
  (epbcActCurrentSource ∷ dcceewLandClearingSource ∷ [])
  "Primary law plus official explanatory guidance. Neither source determines the historical clearing state, claimed land-use continuation, forestry status, significant-impact consequence or application to a particular Woogaroo parcel."

------------------------------------------------------------------------
-- WrongType / no-promotion boundaries.
------------------------------------------------------------------------

data FifteenYearsUnclearedEqualsAutomaticEPBCProhibition : Set where
data FifteenYearsUnclearedEqualsAutomaticPart9ApprovalRequired : Set where
data LocalPlanningApprovalEqualsS43BExemption : Set where
data OldDevelopmentApprovalEqualsContinuousPre2000LandUse : Set where
data S43BCarveoutEqualsEPBC8575Refusal : Set where
data MatureForestEqualsFifteenYearsUncleared : Set where
data HistoricalAerialEqualsLegalClearingHistory : Set where

longUnclearedDoesNotCreateAutomaticProhibition : FifteenYearsUnclearedEqualsAutomaticEPBCProhibition → ⊥
longUnclearedDoesNotCreateAutomaticProhibition ()

longUnclearedDoesNotByItselfCreateApprovalRequirement : FifteenYearsUnclearedEqualsAutomaticPart9ApprovalRequired → ⊥
longUnclearedDoesNotByItselfCreateApprovalRequirement ()

localApprovalDoesNotCreateS43BExemption : LocalPlanningApprovalEqualsS43BExemption → ⊥
localApprovalDoesNotCreateS43BExemption ()

oldApprovalDoesNotProveContinuousUse : OldDevelopmentApprovalEqualsContinuousPre2000LandUse → ⊥
oldApprovalDoesNotProveContinuousUse ()

s43BCarveoutDoesNotDetermine8575Merits : S43BCarveoutEqualsEPBC8575Refusal → ⊥
s43BCarveoutDoesNotDetermine8575Merits ()

maturityDoesNotProveFifteenYearClearingHistory : MatureForestEqualsFifteenYearsUncleared → ⊥
maturityDoesNotProveFifteenYearClearingHistory ()

aerialImageDoesNotBecomeLegalHistory : HistoricalAerialEqualsLegalClearingHistory → ⊥
aerialImageDoesNotBecomeLegalHistory ()
