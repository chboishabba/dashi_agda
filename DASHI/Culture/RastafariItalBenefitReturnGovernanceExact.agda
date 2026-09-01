module DASHI.Culture.RastafariItalBenefitReturnGovernanceExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact as Indigenous
import DASHI.Culture.RastafariItalReturnFlowCircularityExact as Return
import DASHI.Planning.NonSubstitutionalReparationExact as Repair

------------------------------------------------------------------------
-- ITAL MATERIAL RETURN / BENEFIT / CONSENT / AUTHORITY GOVERNANCE
--
-- Cross-pollination owner.  The purpose is to prevent one positive axis from
-- silently substituting for another:
--
--   material return
--   != benefit sharing
--   != consent/access
--   != restored authority / decision rights
--   != equitable relational closure.
--
-- The Indigenous capstone remains authoritative for its Nagoya-style
-- consent/benefit-sharing specimen; the planning owner remains authoritative
-- for generic non-substitutional repair.  The finite fixtures below are DASHI
-- comparison states, not empirical descriptions of any Rastafari or Indigenous
-- community.
------------------------------------------------------------------------

data MaterialReturnStatus : Set where
  noMaterialReturn materialReturned : MaterialReturnStatus

data BenefitReturnStatus : Set where
  noBenefitReturn benefitReturned : BenefitReturnStatus

data ConsentRespectStatus : Set where
  consentUnresolved consentRespected : ConsentRespectStatus

data AuthorityRespectStatus : Set where
  authorityUnresolved authorityRespected : AuthorityRespectStatus

data RelationalClosureStatus : Set where
  relationStillOpen relationClosed : RelationalClosureStatus

record ReturnGovernanceState : Set where
  constructor returnGovernanceState
  field
    material : MaterialReturnStatus
    benefit : BenefitReturnStatus
    consent : ConsentRespectStatus
    authority : AuthorityRespectStatus
    relationalClosure : RelationalClosureStatus

open ReturnGovernanceState public

materialOnly : ReturnGovernanceState
materialOnly =
  returnGovernanceState
    materialReturned noBenefitReturn consentUnresolved authorityUnresolved relationStillOpen

materialWithBenefit : ReturnGovernanceState
materialWithBenefit =
  returnGovernanceState
    materialReturned benefitReturned consentUnresolved authorityUnresolved relationStillOpen

materialBenefitConsent : ReturnGovernanceState
materialBenefitConsent =
  returnGovernanceState
    materialReturned benefitReturned consentRespected authorityUnresolved relationStillOpen

fullFiniteFixture : ReturnGovernanceState
fullFiniteFixture =
  returnGovernanceState
    materialReturned benefitReturned consentRespected authorityRespected relationClosed

------------------------------------------------------------------------
-- Same material-return surface, different governed fibres.
------------------------------------------------------------------------

materialReturnCannotRecoverBenefit :
  NonFactor.FactorsThrough material benefit → ⊥
materialReturnCannotRecoverBenefit =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness materialOnly materialWithBenefit refl (λ ()))

materialReturnCannotRecoverConsent :
  NonFactor.FactorsThrough material consent → ⊥
materialReturnCannotRecoverConsent =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness materialOnly materialBenefitConsent refl (λ ()))

materialReturnCannotRecoverAuthority :
  NonFactor.FactorsThrough material authority → ⊥
materialReturnCannotRecoverAuthority =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness materialOnly fullFiniteFixture refl (λ ()))

materialReturnCannotRecoverRelationalClosure :
  NonFactor.FactorsThrough material relationalClosure → ⊥
materialReturnCannotRecoverRelationalClosure =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness materialOnly fullFiniteFixture refl (λ ()))

benefitReturnCannotRecoverAuthority :
  NonFactor.FactorsThrough benefit authority → ⊥
benefitReturnCannotRecoverAuthority =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness materialWithBenefit fullFiniteFixture refl (λ ()))

------------------------------------------------------------------------
-- Direct Indigenous-capstone reuse.
------------------------------------------------------------------------

scientificResultStillCannotRecoverConsent :
  NonFactor.FactorsThrough Indigenous.scientificResult Indigenous.accessStatus → ⊥
scientificResultStillCannotRecoverConsent =
  Indigenous.scientificResultCannotRecoverConsent

scientificResultStillCannotRecoverBenefitSharing :
  NonFactor.FactorsThrough Indigenous.scientificResult Indigenous.benefitSharingStatus → ⊥
scientificResultStillCannotRecoverBenefitSharing =
  Indigenous.scientificResultCannotRecoverBenefitSharing

nagoyaStyleGateRemainsTwoAxis :
  Indigenous.NagoyaStylePromotionGate Indigenous.sameResultWithConsentAndBenefitSharing
nagoyaStyleGateRemainsTwoAxis =
  Indigenous.nagoyaStylePromotionGate refl refl

------------------------------------------------------------------------
-- Direct generic non-substitutional-repair reuse.
------------------------------------------------------------------------

compensationStillDoesNotRestoreAuthority :
  Repair.ReparativeBundle.status Repair.compensationOnly Repair.authorityRestorationAxis
  ≡ Repair.repaired → ⊥
compensationStillDoesNotRestoreAuthority = Repair.compensationDoesNotRestoreAuthority

compensationStillDoesNotCreateDecisionRights :
  Repair.ReparativeBundle.status Repair.compensationOnly Repair.decisionRightsAxis
  ≡ Repair.repaired → ⊥
compensationStillDoesNotCreateDecisionRights = Repair.compensationDoesNotCreateDecisionRights

------------------------------------------------------------------------
-- Link to the existing Ital return-flow vocabulary without claiming that a
-- community redistribution event establishes any of the governance axes above.
------------------------------------------------------------------------

communityRedistributionKind : Return.ReturnKind
communityRedistributionKind = Return.communityRedistribution

data CommunityRedistributionProvesBenefitSharing : Set where

data MaterialReturnProvesConsent : Set where

data MaterialReturnRestoresAuthority : Set where

data BenefitSharingClosesRelation : Set where

data PhysicalCircularityMeansGovernanceCircularity : Set where

communityRedistributionDoesNotProveBenefitSharing :
  CommunityRedistributionProvesBenefitSharing → ⊥
communityRedistributionDoesNotProveBenefitSharing ()

materialReturnDoesNotProveConsent : MaterialReturnProvesConsent → ⊥
materialReturnDoesNotProveConsent ()

materialReturnDoesNotRestoreAuthority : MaterialReturnRestoresAuthority → ⊥
materialReturnDoesNotRestoreAuthority ()

benefitSharingDoesNotByItselfCloseRelation : BenefitSharingClosesRelation → ⊥
benefitSharingDoesNotByItselfCloseRelation ()

physicalCircularityDoesNotMeanGovernanceCircularity :
  PhysicalCircularityMeansGovernanceCircularity → ⊥
physicalCircularityDoesNotMeanGovernanceCircularity ()

record ItalBenefitReturnGovernanceBoundary : Set where
  constructor italBenefitReturnGovernanceBoundary
  field
    materialReturnEqualsBenefitReturn : Bool
    materialReturnEqualsBenefitReturnIsFalse : materialReturnEqualsBenefitReturn ≡ false

    benefitReturnEqualsConsent : Bool
    benefitReturnEqualsConsentIsFalse : benefitReturnEqualsConsent ≡ false

    benefitReturnEqualsAuthorityRestoration : Bool
    benefitReturnEqualsAuthorityRestorationIsFalse :
      benefitReturnEqualsAuthorityRestoration ≡ false

    materialCircularityEqualsRelationalClosure : Bool
    materialCircularityEqualsRelationalClosureIsFalse :
      materialCircularityEqualsRelationalClosure ≡ false

    governanceAxesRemainIndependentlyAuditable : Bool
    governanceAxesRemainIndependentlyAuditableIsTrue :
      governanceAxesRemainIndependentlyAuditable ≡ true

canonicalItalBenefitReturnGovernanceBoundary :
  ItalBenefitReturnGovernanceBoundary
canonicalItalBenefitReturnGovernanceBoundary =
  italBenefitReturnGovernanceBoundary
    false refl false refl false refl false refl true refl
