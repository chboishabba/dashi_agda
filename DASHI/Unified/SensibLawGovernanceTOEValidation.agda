{-# OPTIONS --safe #-}
module DASHI.Unified.SensibLawGovernanceTOEValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Data.Empty using (⊥)

import DASHI.Unified.SensibLawGovernanceTOEExact as GovTOE
import DASHI.EverythingTOESymmetryResolved369 as TOE
import DASHI.Unifier as Unifier

------------------------------------------------------------------------
-- Same-owner agreement.
------------------------------------------------------------------------

toeSemanticPromotionSurfaceMatchesOwner :
  TOE.toeSensibLawSemanticPromotionPolicySurface
  ≡ GovTOE.sensibLawSemanticPromotionPolicySurface
toeSemanticPromotionSurfaceMatchesOwner = refl

unifierSemanticPromotionSurfaceMatchesOwner :
  Unifier.unifierSensibLawSemanticPromotionPolicySurface
  ≡ GovTOE.sensibLawSemanticPromotionPolicySurface
unifierSemanticPromotionSurfaceMatchesOwner = refl

toeExpertBoundaryMatchesOwner :
  TOE.toeSensibLawExpertProductionBoundary
  ≡ GovTOE.sensibLawExpertProductionBoundary
toeExpertBoundaryMatchesOwner = refl

unifierExpertBoundaryMatchesOwner :
  Unifier.unifierSensibLawExpertProductionBoundary
  ≡ GovTOE.sensibLawExpertProductionBoundary
unifierExpertBoundaryMatchesOwner = refl

toeReviewBoundaryMatchesOwner :
  TOE.toeSensibLawRealMatterReviewBoundary
  ≡ GovTOE.sensibLawRealMatterReviewBoundary
toeReviewBoundaryMatchesOwner = refl

unifierReviewBoundaryMatchesOwner :
  Unifier.unifierSensibLawRealMatterReviewBoundary
  ≡ GovTOE.sensibLawRealMatterReviewBoundary
unifierReviewBoundaryMatchesOwner = refl

toeRequirementParetoMatchesOwner :
  TOE.toeSensibLawRequirementParetoContract
  ≡ GovTOE.sensibLawRequirementParetoContract
toeRequirementParetoMatchesOwner = refl

unifierRequirementParetoMatchesOwner :
  Unifier.unifierSensibLawRequirementParetoContract
  ≡ GovTOE.sensibLawRequirementParetoContract
unifierRequirementParetoMatchesOwner = refl

toeSnowballBoundaryMatchesOwner :
  TOE.toeSensibLawSnowballLineageBoundary
  ≡ GovTOE.sensibLawSnowballLineageBoundary
toeSnowballBoundaryMatchesOwner = refl

unifierSnowballBoundaryMatchesOwner :
  Unifier.unifierSensibLawSnowballLineageBoundary
  ≡ GovTOE.sensibLawSnowballLineageBoundary
unifierSnowballBoundaryMatchesOwner = refl

toeGovernanceZKPFrameMatchesOwner :
  TOE.toeSensibLawGovernanceZKPFrame
  ≡ GovTOE.canonicalSensibLawGovernanceZKPFrame
toeGovernanceZKPFrameMatchesOwner = refl

unifierGovernanceZKPFrameMatchesOwner :
  Unifier.unifierSensibLawGovernanceZKPFrame
  ≡ GovTOE.canonicalSensibLawGovernanceZKPFrame
unifierGovernanceZKPFrameMatchesOwner = refl

------------------------------------------------------------------------
-- Direct semantic and authority firewalls.
------------------------------------------------------------------------

toeSemanticPromotionLegalAuthorityClosed :
  GovTOE.sensibLawSemanticPromotionLegalAuthorityFlag ≡ false
toeSemanticPromotionLegalAuthorityClosed =
  TOE.toeSensibLawSemanticPromotionLegalAuthorityClosed

unifierSemanticPromotionLegalAuthorityClosed :
  GovTOE.sensibLawSemanticPromotionLegalAuthorityFlag ≡ false
unifierSemanticPromotionLegalAuthorityClosed =
  Unifier.unifierSensibLawSemanticPromotionLegalAuthorityClosed

toeExpertProductionAuthorityClosed :
  GovTOE.sensibLawExpertProductionPromotesAnyAuthority ≡ false
toeExpertProductionAuthorityClosed =
  TOE.toeSensibLawExpertProductionAuthorityClosed

unifierExpertProductionAuthorityClosed :
  GovTOE.sensibLawExpertProductionPromotesAnyAuthority ≡ false
unifierExpertProductionAuthorityClosed =
  Unifier.unifierSensibLawExpertProductionAuthorityClosed

toeReviewDoesNotCreateClaimTruth :
  GovTOE.LegalReviewDecisionCreatesClaimTruth → ⊥
toeReviewDoesNotCreateClaimTruth =
  TOE.toeSensibLawReviewDoesNotCreateClaimTruth

unifierReviewDoesNotCreateClaimTruth :
  GovTOE.LegalReviewDecisionCreatesClaimTruth → ⊥
unifierReviewDoesNotCreateClaimTruth =
  Unifier.unifierSensibLawReviewDoesNotCreateClaimTruth

toeParserCandidateCannotAuthorizeAdmission :
  GovTOE.ParserCandidateAloneAuthorizesAdmission → ⊥
toeParserCandidateCannotAuthorizeAdmission =
  TOE.toeSensibLawParserCandidateCannotAuthorizeAdmission

unifierParserCandidateCannotAuthorizeAdmission :
  GovTOE.ParserCandidateAloneAuthorizesAdmission → ⊥
unifierParserCandidateCannotAuthorizeAdmission =
  Unifier.unifierSensibLawParserCandidateCannotAuthorizeAdmission

toeQualificationDoesNotProveForensicCompliance :
  GovTOE.QualificationAutomaticallyForensicCompliance → ⊥
toeQualificationDoesNotProveForensicCompliance =
  TOE.toeSensibLawQualificationDoesNotProveForensicCompliance

unifierQualificationDoesNotProveForensicCompliance :
  GovTOE.QualificationAutomaticallyForensicCompliance → ⊥
unifierQualificationDoesNotProveForensicCompliance =
  Unifier.unifierSensibLawQualificationDoesNotProveForensicCompliance

toeOfficialLegalSurfaceCannotRecoverFineState :
  GovTOE.OfficialLegalSurfaceRecoversFineState → ⊥
toeOfficialLegalSurfaceCannotRecoverFineState =
  TOE.toeSensibLawOfficialLegalSurfaceCannotRecoverFineState

unifierOfficialLegalSurfaceCannotRecoverFineState :
  GovTOE.OfficialLegalSurfaceRecoversFineState → ⊥
unifierOfficialLegalSurfaceCannotRecoverFineState =
  Unifier.unifierSensibLawOfficialLegalSurfaceCannotRecoverFineState

toeLegalOnlyDoesNotCreateLegitimacy :
  GovTOE.LegalOnlyCreatesLegitimacy → ⊥
toeLegalOnlyDoesNotCreateLegitimacy =
  TOE.toeSensibLawLegalOnlyDoesNotCreateLegitimacy

unifierLegalOnlyDoesNotCreateLegitimacy :
  GovTOE.LegalOnlyCreatesLegitimacy → ⊥
unifierLegalOnlyDoesNotCreateLegitimacy =
  Unifier.unifierSensibLawLegalOnlyDoesNotCreateLegitimacy

------------------------------------------------------------------------
-- Fleet and scheduling boundary.
------------------------------------------------------------------------

toeLegalLaneDoesNotRetargetDischargedFleetFibres :
  GovTOE.legalGovernanceLaneRetargetsDischargedFleetFibres ≡ false
toeLegalLaneDoesNotRetargetDischargedFleetFibres =
  TOE.toeSensibLawLegalLaneDoesNotRetargetDischargedFleetFibres

unifierLegalLaneDoesNotRetargetDischargedFleetFibres :
  GovTOE.legalGovernanceLaneRetargetsDischargedFleetFibres ≡ false
unifierLegalLaneDoesNotRetargetDischargedFleetFibres =
  Unifier.unifierSensibLawLegalLaneDoesNotRetargetDischargedFleetFibres
