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
  Unifier.O-residualWidthWitness
  ≡ TOE.O-residualWidthWitness
unifierResidualWidthOwnerIsExact = refl

unifierWidthNonPromotionOwnerIsExact :
  Unifier.C-orderedWidthDoesNotLowerBoundArbitraryDecisionCount
  ≡ TOE.C-orderedWidthDoesNotLowerBoundArbitraryDecisionCount
unifierWidthNonPromotionOwnerIsExact = refl

unifierExhaustiveFailureOwnerIsExact :
  Unifier.S-exhaustiveBuilderFailsAtSmallBudget
  ≡ TOE.S-exhaustiveBuilderFailsAtSmallBudget
unifierExhaustiveFailureOwnerIsExact = refl

unifierFutureTransportOwnerIsExact :
  Unifier.L-candidateQuotedOutputCannotDetermineFuture
  ≡ TOE.L-candidateQuotedOutputCannotDetermineFuture
unifierFutureTransportOwnerIsExact = refl

unifierStutteringPreservationOwnerIsExact :
  Unifier.P-stutteringPreservesDecision
  ≡ TOE.P-stutteringPreservesDecision
unifierStutteringPreservationOwnerIsExact = refl

unifierInterpreterBudgetOwnerIsExact :
  Unifier.G-interpreterWorkLinearBound
  ≡ TOE.G-interpreterWorkLinearBound
unifierInterpreterBudgetOwnerIsExact = refl

unifierCookLevinWeldOwnerIsExact :
  Unifier.F-sameMachineProgramCookLevin
  ≡ TOE.F-sameMachineProgramCookLevin
unifierCookLevinWeldOwnerIsExact = refl
