module DASHI.Cognition.VilyaProtectiveSpatialValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.ProtectiveSpatialIntelligenceExact as Core
import DASHI.Cognition.VilyaProtectionSourceAtlasExact as Vilya
import DASHI.Cognition.ProtectiveSpatialDualUseAntiPanopticonExact as DualUse
import DASHI.Cognition.KirkVilyaCounterfactualPreventionBoundaryExact as Kirk

gevObservationDoesNotCreateProtectiveAuthority :
  Core.observationCreatesProtectiveAuthority ≡ false
gevObservationDoesNotCreateProtectiveAuthority = refl

vilyaWorkflowKeepsFiveDistinctStages :
  Vilya.fiveStageWorkflowPaid ≡ true
vilyaWorkflowKeepsFiveDistinctStages = refl

vendorClaimsDoNotBecomeValidatedPerformance :
  Vilya.vendorDescriptionCreatesIndependentPerformanceValidation ≡ false
vendorClaimsDoNotBecomeValidatedPerformance = refl

sameSpatialPrimitiveDoesNotFixPurpose :
  DualUse.sameSpatialPrimitiveDeterminesProtectiveOrLethalPurpose ≡ false
sameSpatialPrimitiveDoesNotFixPurpose = refl

autonomousTargetSelectionDoesNotInheritProtectiveAuthority :
  DualUse.protectiveObservationCreatesAutonomousUseOfForceAuthority ≡ false
autonomousTargetSelectionDoesNotInheritProtectiveAuthority = refl

humanLifeDeathAuthorityRequired :
  DualUse.humanControlOverLifeDeathDecisionRequired ≡ true
humanLifeDeathAuthorityRequired = refl

kirkRelevantObservableOmissionPaid :
  Kirk.relevantProtectiveObservableOmissionPaid ≡ true
kirkRelevantObservableOmissionPaid = refl

vilyaWouldHavePreventedKirkNotPaid :
  Kirk.vilyaWouldHavePreventedKirkPaid ≡ false
vilyaWouldHavePreventedKirkNotPaid = refl

capabilityRelevanceDoesNotPayCausalPrevention :
  Kirk.capabilityAddressesOmittedObservableImpliesPrevention ≡ false
capabilityRelevanceDoesNotPayCausalPrevention = refl
