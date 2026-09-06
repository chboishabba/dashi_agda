module DASHI.Core.ResidualActionExecutionBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.MechanismModelDiscriminationExact as Model
import DASHI.Core.ResidualActionPolicyExact as Action
import DASHI.Core.ProofCarryingPhysicalExecutionBoundaryExact as Physical
import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as ProofSearch

record ResidualPhysicalPromotion : Set₁ where
  constructor residualPhysicalPromotion
  field
    residual : Model.ModelResidual
    requestedAction : Action.ResidualActionKind
    policyAdmissionReference : String
    physicalPromotion : Physical.PhysicalPromotionReceipt
    executable : Physical.ExecutableAction
    runtimeBindingReference : String

open ResidualPhysicalPromotion public

compilePromotedResidualAction :
  ResidualPhysicalPromotion → Physical.HardwareCommand
compilePromotedResidualAction promotion =
  Physical.compileExecutable (executable promotion)

record ResidualProofSearchPromotion : Set where
  constructor residualProofSearchPromotion
  field
    residualReference : String
    requestedActionReference : String
    routeAdmission : ProofSearch.RouteAdmission
    exactConsumerReference : String

open ResidualProofSearchPromotion public

admittedResidualProofSearch : ResidualProofSearchPromotion → ProofSearch.LiveProofSearch
admittedResidualProofSearch promotion =
  ProofSearch.elaborateRoute (routeAdmission promotion)

record ResidualActionExecutionBoundary : Set where
  constructor residualActionExecutionBoundary
  field
    residualImpliesPhysicalExecutability : Bool
    residualImpliesPhysicalExecutabilityIsFalse :
      residualImpliesPhysicalExecutability ≡ false
    perturbRecommendationImpliesHardwareCommand : Bool
    perturbRecommendationImpliesHardwareCommandIsFalse :
      perturbRecommendationImpliesHardwareCommand ≡ false
    proofSearchAdmissionImpliesPhysicalAuthority : Bool
    proofSearchAdmissionImpliesPhysicalAuthorityIsFalse :
      proofSearchAdmissionImpliesPhysicalAuthority ≡ false
    physicalPerturbationRequiresIndependentExecutionReceipt : Bool
    physicalPerturbationRequiresIndependentExecutionReceiptIsTrue :
      physicalPerturbationRequiresIndependentExecutionReceipt ≡ true
    postPerturbationObservationRemainsSeparateFromIntendedOutcome : Bool
    postPerturbationObservationRemainsSeparateFromIntendedOutcomeIsTrue :
      postPerturbationObservationRemainsSeparateFromIntendedOutcome ≡ true

canonicalResidualActionExecutionBoundary : ResidualActionExecutionBoundary
canonicalResidualActionExecutionBoundary =
  residualActionExecutionBoundary false refl false refl false refl true refl true refl

existingPhysicalBoundary : Physical.ProofCarryingPhysicalExecutionBoundary
existingPhysicalBoundary = Physical.canonicalProofCarryingPhysicalExecutionBoundary

existingProofSearchBoundary : ProofSearch.ProofSearchLeastPrivilegeBoundary
existingProofSearchBoundary = ProofSearch.canonicalProofSearchLeastPrivilegeBoundary
