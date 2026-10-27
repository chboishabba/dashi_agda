module DASHI.Unified.ResidualWidthNonPromotionTOERegression where

------------------------------------------------------------------------
-- Regression for the TOE/Unifier normalization.
--
-- The regression does not re-prove complexity results.
-- It verifies that Unifier re-exports the exact theorem owner.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Unified.ResidualWidthNonPromotionTOEExact as TOE
import DASHI.Unifier as Unifier

unifierResidualWidthOwnerIsExact :
  Unifier.toeBlockEqualityResidualWidthWitness
  ≡ TOE.toeBlockEqualityResidualWidthWitness
unifierResidualWidthOwnerIsExact = refl

unifierWidthNonPromotionOwnerIsExact :
  Unifier.toeOrderedWidthDoesNotLowerBoundArbitraryDecisionCount
  ≡ TOE.toeOrderedWidthDoesNotLowerBoundArbitraryDecisionCount
unifierWidthNonPromotionOwnerIsExact = refl

unifierDirectDPObstructionOwnerIsExact :
  Unifier.toeBlockEqualityConditionalDirectDPObstruction
  ≡ TOE.toeBlockEqualityConditionalDirectDPObstruction
unifierDirectDPObstructionOwnerIsExact = refl

unifierSelfSpecializationNoGoOwnerIsExact :
  Unifier.toeGenericSelfSpecializationDoesNotForceSmallWidth
  ≡ TOE.toeGenericSelfSpecializationDoesNotForceSmallWidth
unifierSelfSpecializationNoGoOwnerIsExact = refl

unifierCandidateFirstStepBoundaryOwnerIsExact :
  Unifier.toeCandidateHighWidthRefutesRequiredFirstStep
  ≡ TOE.toeCandidateHighWidthRefutesRequiredFirstStep
unifierCandidateFirstStepBoundaryOwnerIsExact = refl

unifierExhaustiveFailureOwnerIsExact :
  Unifier.toeExhaustiveBuilderFailsAtSmallBudget
  ≡ TOE.toeExhaustiveBuilderFailsAtSmallBudget
unifierExhaustiveFailureOwnerIsExact = refl

unifierFutureTransportOwnerIsExact :
  Unifier.toeCandidateOutputDoesNotDetermineFuture
  ≡ TOE.toeCandidateOutputDoesNotDetermineFuture
unifierFutureTransportOwnerIsExact = refl

unifierStutteringPreservationOwnerIsExact :
  Unifier.toeStutteringPreservesDecision
  ≡ TOE.toeStutteringPreservesDecision
unifierStutteringPreservationOwnerIsExact = refl

unifierInterpreterBudgetOwnerIsExact :
  Unifier.toeInterpreterWorkLinearBound
  ≡ TOE.toeInterpreterWorkLinearBound
unifierInterpreterBudgetOwnerIsExact = refl

unifierCookLevinWeldOwnerIsExact :
  Unifier.toeSameMachineProgramCookLevin
  ≡ TOE.toeSameMachineProgramCookLevin
unifierCookLevinWeldOwnerIsExact = refl
