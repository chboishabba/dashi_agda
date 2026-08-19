module DASHI.Papers.NavierStokes.TheoremInterfaceRound90Exact where

------------------------------------------------------------------------
-- PAPER-FACING ROUND90 INTERFACE
--
-- Round90 returns the programme to a top-down theorem architecture.
-- The branch no longer treats a fixed number of source-facing leaves as a
-- proof invariant.  Round89 demonstrated why: the proposed far-gap
-- strong-six-three viscous leaf was falsified at its actual linear consumer,
-- while moving p.q inside the gradient tensor exposed a different existing
-- HH->low H^{-1} route with no separate gap tax.
--
-- The terminal consumer is now solution indexed:
--
--   CriticalBarrierFor u
--       -> u in the Serrin continuation class
--       -> u extends past its maximal time.
--
-- Thus the old H2/H3 split is fused at the mathematically correct boundary.
-- All remaining pressure/HH/commutator/residual/occupation/Galerkin/limit work
-- is judged by whether it constructs `CriticalBarrierFor` for the SAME limiting
-- solution, not by whether a historical checklist has a fixed number of
-- leaves.
--
-- The Round89 gradient-tensor route remains fail-closed at its physical
-- realization seam.  Clay promotion remains false.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNClayTopDownConsumerRound90Exact as Top
import DASHI.Physics.Closure.NSTriadKNViscousWeightedHHLowTensorFactorizationRound89Exact as HHTensor
import DASHI.Physics.Closure.NSTriadKNStrongSixThreeLinearViscousNoGoRound89Exact as SixThreeNoGo

round90SameSolutionTopDownContinuationConsumer : Bool
round90SameSolutionTopDownContinuationConsumer =
  Top.round90TopDownClayConsumerConstructed

round90OldH2H3FuseAtBarrierInterface : Bool
round90OldH2H3FuseAtBarrierInterface =
  Top.round90OldH2H3FuseAtSameSolutionBarrierInterface

round90FixedLeafCountRetiredAsInvariant : Bool
round90FixedLeafCountRetiredAsInvariant = true

round90StrongSixThreeLinearViscousShortcutAvailable : Bool
round90StrongSixThreeLinearViscousShortcutAvailable =
  SixThreeNoGo.round89D1SquaredGramCanDirectlyServeAsLinearVariationBound

round90StrongSixThreeLinearViscousShortcutRejected : Bool
round90StrongSixThreeLinearViscousShortcutRejected = true

round90WeightedHHGradientTensorIdentityConstructed : Bool
round90WeightedHHGradientTensorIdentityConstructed =
  HHTensor.round89WeightedHHTensorDivergenceIdentityClosed

round90WeightedHHGradientTensorPhysicalCarrierWeld : Bool
round90WeightedHHGradientTensorPhysicalCarrierWeld =
  HHTensor.round89DerivativeWeightedTensorRealizedInClosedHHCarrier

round90PhysicalTopDownClayProducer : Bool
round90PhysicalTopDownClayProducer =
  Top.round90PhysicalTopDownClayProducerConstructed

round90ClayPromotion : Bool
round90ClayPromotion = false

round90SameSolutionTopDownContinuationConsumerIsTrue :
  round90SameSolutionTopDownContinuationConsumer ≡ true
round90SameSolutionTopDownContinuationConsumerIsTrue = refl

round90OldH2H3FuseAtBarrierInterfaceIsTrue :
  round90OldH2H3FuseAtBarrierInterface ≡ true
round90OldH2H3FuseAtBarrierInterfaceIsTrue = refl

round90FixedLeafCountRetiredAsInvariantIsTrue :
  round90FixedLeafCountRetiredAsInvariant ≡ true
round90FixedLeafCountRetiredAsInvariantIsTrue = refl

round90StrongSixThreeLinearViscousShortcutAvailableIsFalse :
  round90StrongSixThreeLinearViscousShortcutAvailable ≡ false
round90StrongSixThreeLinearViscousShortcutAvailableIsFalse = refl

round90StrongSixThreeLinearViscousShortcutRejectedIsTrue :
  round90StrongSixThreeLinearViscousShortcutRejected ≡ true
round90StrongSixThreeLinearViscousShortcutRejectedIsTrue = refl

round90WeightedHHGradientTensorIdentityConstructedIsTrue :
  round90WeightedHHGradientTensorIdentityConstructed ≡ true
round90WeightedHHGradientTensorIdentityConstructedIsTrue = refl

round90WeightedHHGradientTensorPhysicalCarrierWeldIsFalse :
  round90WeightedHHGradientTensorPhysicalCarrierWeld ≡ false
round90WeightedHHGradientTensorPhysicalCarrierWeldIsFalse = refl

round90PhysicalTopDownClayProducerIsFalse :
  round90PhysicalTopDownClayProducer ≡ false
round90PhysicalTopDownClayProducerIsFalse = refl

round90ClayPromotionIsFalse : round90ClayPromotion ≡ false
round90ClayPromotionIsFalse = refl
