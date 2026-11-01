module DASHI.Core.ResidualActionExecutionBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.MechanismModelDiscriminationExact as Model
import DASHI.Core.ResidualActionPolicyExact as Action
import DASHI.Core.ProofCarryingPhysicalExecutionBoundaryExact as Physical
import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as ProofSearch

------------------------------------------------------------------------
-- RESIDUAL ACTION <-> EXECUTION AUTHORITY BOUNDARY
--
-- Model discrimination can recommend a perturbation, but a recommendation is
-- not a physical command.  Wet-lab automation, engineering diagnostics,
-- robotics and other cyber-physical applications must separately satisfy the
-- repository's proof-carrying physical-execution boundary.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Proof-search cross-pollination.
--
-- A formal-search route and a physical execution route have analogous
-- least-privilege structure, but their authorities are deliberately distinct.
------------------------------------------------------------------------

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
