module DASHI.Planning.CollectiveTerritorialConsentExact where

open import DASHI.Core.Prelude
import DASHI.Biology.ConsentAgencyGovernanceCore as Consent
import DASHI.Planning.ParticipatoryPlanningGovernanceExact as Participation

------------------------------------------------------------------------
-- COLLECTIVE / TERRITORIAL CONSENT
--
-- Planning consultation, legal approval, participation and consent are kept
-- on separate carriers.  This lifts the existing refusal/withdrawal/review
-- discipline into a spatial and collective planning interface without
-- claiming that one generic record exhausts any community's law or protocol.
------------------------------------------------------------------------

data ConsentStage : Set where
  informed reached consulted consentRequested consentGiven : ConsentStage

data ConsentScope : Set where
  boundedUse irreversibleIntervention governanceChange : ConsentScope

data Contestability : Set where
  noContest reviewOnly canRefuse canWithdraw : Contestability

record CollectiveConsentEnvelope : Set where
  constructor collectiveConsentEnvelope
  field
    stage : ConsentStage
    scope : ConsentScope
    contestability : Contestability
    informationMateriallyCurrent : Bool
    alternativesRemainAvailable : Bool
    authoritySourceSpecified : Bool
    reopeningOnMaterialChange : Bool

consultationOnly : CollectiveConsentEnvelope
consultationOnly =
  collectiveConsentEnvelope consulted boundedUse reviewOnly true true true true

withdrawableConsent : CollectiveConsentEnvelope
withdrawableConsent =
  collectiveConsentEnvelope consentGiven irreversibleIntervention canWithdraw true true true true

consultedIsNotConsentGiven :
  CollectiveConsentEnvelope.stage consultationOnly ≡ consentGiven → ⊥
consultedIsNotConsentGiven ()

reviewOnlyIsNotWithdrawalPower :
  CollectiveConsentEnvelope.contestability consultationOnly ≡ canWithdraw → ⊥
reviewOnlyIsNotWithdrawalPower ()

record ConsentPromotionBoundary : Set where
  constructor consentPromotionBoundary
  field
    consultationImpliesConsent : Bool
    consultationImpliesConsentIsFalse : consultationImpliesConsent ≡ false
    legalApprovalImpliesCollectiveConsent : Bool
    legalApprovalImpliesCollectiveConsentIsFalse : legalApprovalImpliesCollectiveConsent ≡ false
    historicalConsentImpliesCurrentConsent : Bool
    historicalConsentImpliesCurrentConsentIsFalse : historicalConsentImpliesCurrentConsent ≡ false
    participationImpliesPowerToRefuse : Bool
    participationImpliesPowerToRefuseIsFalse : participationImpliesPowerToRefuse ≡ false
    consentWithoutWithdrawalIsFullyContestable : Bool
    consentWithoutWithdrawalIsFullyContestableIsFalse :
      consentWithoutWithdrawalIsFullyContestable ≡ false

canonicalConsentPromotionBoundary : ConsentPromotionBoundary
canonicalConsentPromotionBoundary =
  consentPromotionBoundary false refl false refl false refl false refl false refl

-- Reuse the existing consent/agency governance receipt rather than rebuilding
-- refusal, withdrawal and review semantics in planning.
existingConsentGovernance : Consent.ConsentAgencyGovernance
existingConsentGovernance = Consent.canonicalConsentAgencyGovernance

-- Participation remains a distinct seam: access/expression/co-decision are not
-- silently promoted to collective consent.
participatoryPlanningBoundary : Participation.ParticipatoryPlanningBoundary
participatoryPlanningBoundary = Participation.canonicalParticipatoryPlanningBoundary
