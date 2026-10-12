module DASHI.Cognition.EpsteinTechClaimVerificationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- TECH / MEDIA CLAIM VERIFICATION
--
-- Lead-bundle claims are decomposed into direct correspondence, attempted
-- meeting/visit, completed event, later corporate/infrastructure context and
-- disputed-source claims.  Later business overlap cannot be back-projected into
-- an Epstein-era relationship.
------------------------------------------------------------------------

data TechFigure : Set where
  elonMusk : TechFigure
  kimbalMusk : TechFigure
  peterThiel : TechFigure
  reidHoffman : TechFigure
  larryEllison : TechFigure
  alexKarp : TechFigure
  larrySummers : TechFigure

data TechEdgeKind : Set where
  directEmail : TechEdgeKind
  plannedVisit : TechEdgeKind
  completedVisit : TechEdgeKind
  engineeredIntroduction : TechEdgeKind
  investmentRelationship : TechEdgeKind
  laterCorporateOverlap : TechEdgeKind
  addressBookListing : TechEdgeKind
  disputedFundraisingAttribution : TechEdgeKind

record TechClaimStatus : Set where
  constructor tech-claim-status
  field
    subject : TechFigure
    edgeKind : TechEdgeKind
    sourceDescription : String
    edgePaid : Bool
    completionPaid : Bool
    wrongdoingEstablished : Bool
    note : String
open TechClaimStatus public

elonDirectEmail : TechClaimStatus
elonDirectEmail = tech-claim-status
  elonMusk directEmail
  "2026 DOJ-release reporting reproducing 2012-2013 Musk/Epstein emails"
  true false false
  "Direct email/contact is paid. Emails discuss possible island visits, but the 2012-13 visit appears not to have occurred; do not promote attempted planning to completed visit."

elonPlannedVisit : TechClaimStatus
elonPlannedVisit = tech-claim-status
  elonMusk plannedVisit
  "2012-2013 email chains"
  true false false
  "Planning/interest is paid; completion is not."

kimbalEngineeredIntroduction : TechClaimStatus
kimbalEngineeredIntroduction = tech-claim-status
  kimbalMusk engineeredIntroduction
  "2026 Guardian reporting from released email corpus"
  true false false
  "Reporting describes Epstein/Nikolic involvement in introducing and managing contact around a woman who dated Kimbal Musk; preserve her reported coercion/abuse account separately from Kimbal's conduct."

ellisonAddressBookCandidate : TechClaimStatus
ellisonAddressBookCandidate = tech-claim-status
  larryEllison addressBookListing
  "secondary public corpus/address-book index; primary page still required"
  false false false
  "Treat as locator only until underlying address-book receipt is acquired. Later Oracle/Paramount/TikTok/Palantir business overlaps do not create an Epstein relationship."

mandelsonPalantirContext : TechClaimStatus
mandelsonPalantirContext = tech-claim-status
  alexKarp laterCorporateOverlap
  "2026 Guardian reporting on Global Counsel/Palantir and Mandelson fallout"
  true false false
  "This pays a later lobbying/corporate-context edge, not an Epstein->Palantir funding or coordination edge."

summersOpenAIContext : TechClaimStatus
summersOpenAIContext = tech-claim-status
  larrySummers laterCorporateOverlap
  "2025 Reuters reporting on Summers resignation from OpenAI board after Epstein-email disclosure"
  true true false
  "Pays Summers->OpenAI board role and resignation after disclosure; does not create Sam Altman or OpenAI relationship with Epstein."

record MITFundraisingDisagreement : Set where
  constructor mit-fundraising-disagreement
  field
    newYorkerReportedEpsteinSecured75m : Bool
    mitInvestigationFoundEvidenceHeArrangedGatesBlackGifts : Bool
    mitInvestigationFoundGatesBlackMoneyWasEpsteinMoney : Bool
    sourceDisagreementMustRemainVisible : Bool
open MITFundraisingDisagreement public

mitFundraisingDisagreement : MITFundraisingDisagreement
mitFundraisingDisagreement = mit-fundraising-disagreement true false false true

------------------------------------------------------------------------
-- FIREWALLS
------------------------------------------------------------------------

data PlannedVisitImpliesCompletedVisit : Set where
data DirectEmailImpliesWrongdoing : Set where
data LaterBusinessOverlapImpliesHistoricalRelationship : Set where
data SecondaryIndexImpliesPrimaryReceipt : Set where
data MediaClaimOverridesInstitutionalInvestigation : Set where

plannedDoesNotCreateCompleted : PlannedVisitImpliesCompletedVisit → ⊥
plannedDoesNotCreateCompleted ()

directEmailDoesNotCreateWrongdoing : DirectEmailImpliesWrongdoing → ⊥
directEmailDoesNotCreateWrongdoing ()

laterOverlapDoesNotCreateHistoricalRelationship :
  LaterBusinessOverlapImpliesHistoricalRelationship → ⊥
laterOverlapDoesNotCreateHistoricalRelationship ()

secondaryIndexDoesNotCreatePrimaryReceipt : SecondaryIndexImpliesPrimaryReceipt → ⊥
secondaryIndexDoesNotCreatePrimaryReceipt ()

mediaClaimDoesNotOverrideInstitutionalInvestigation :
  MediaClaimOverridesInstitutionalInvestigation → ⊥
mediaClaimDoesNotOverrideInstitutionalInvestigation ()
