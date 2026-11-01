module DASHI.Papers.NavierStokes.TheoremInterfaceRound79Exact where

------------------------------------------------------------------------
-- PAPER-FACING ROUND79 INTERFACE
--
-- Round79 corrects the Round78 pressure-resolved producer by separating two
-- same-event observables:
--
--   pressure contraction -> stretching-amplitude balance;
--   pressure off-diagonal/gap -> strain-eigenframe rotation balance.
--
-- Full pressure and deviatoric pressure share their eigenspaces exactly, but
-- neither the strain eigenframe nor a positive strain-gap/vorticity lower bound
-- is inferred.  The latter is explicitly falsified by a periodic pure-rotation
-- counterexample.  The corrected rotation theorem is division-free.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound79Exact as R79

round79FullAndDeviatoricPressureEigenframeSame : Bool
round79FullAndDeviatoricPressureEigenframeSame =
  R79.round79FullAndDeviatoricPressureShareEigenframe

round79PointwiseStrainGapVorticityShortcutValid : Bool
round79PointwiseStrainGapVorticityShortcutValid =
  R79.round79StrainGapComparableToVorticityFromOrderingAlone

round79PressureScalarSufficientForEigenframeRotation : Bool
round79PressureScalarSufficientForEigenframeRotation =
  R79.round79PressureContractionDeterminesFrameInjection

round79CorrectPressureProducerHasTwoAxes : Bool
round79CorrectPressureProducerHasTwoAxes =
  R79.round79CorrectC3NeedsStretchingAndRotation

-- Seven remaining physical/analytic packages.
round79SelectedGlobalLiteralGalerkinTrajectory : Bool
round79SelectedGlobalLiteralGalerkinTrajectory = false

round79SelectedFineStructuredDynamicBalance : Bool
round79SelectedFineStructuredDynamicBalance = false

round79PhysicalPressureStretchingRotationSurplusOrDepletionClosure : Bool
round79PhysicalPressureStretchingRotationSurplusOrDepletionClosure = false

round79PhysicalNormalizedSixThreeGramEstimate : Bool
round79PhysicalNormalizedSixThreeGramEstimate = false

round79PhysicalHHBadCapacityChargeBound : Bool
round79PhysicalHHBadCapacityChargeBound = false

round79PhysicalSoftDataAndBoundaryClosure : Bool
round79PhysicalSoftDataAndBoundaryClosure = false

round79PhysicalAnnularMultiplierKernelBound : Bool
round79PhysicalAnnularMultiplierKernelBound = false

round79CriticalRatioBarrier : Bool
round79CriticalRatioBarrier = false

round79GenericAubinLionsLimitInterfacesAlreadyPresent : Bool
round79GenericAubinLionsLimitInterfacesAlreadyPresent =
  R79.round79GenericAubinLionsLimitInterfacesAlreadyPresent

round79CriticalToSerrinReducerAlreadyPresent : Bool
round79CriticalToSerrinReducerAlreadyPresent =
  R79.round79CriticalToSerrinReducerAlreadyPresent

round79ClayPromotion : Bool
round79ClayPromotion = false

round79PointwiseStrainGapVorticityShortcutValidIsFalse :
  round79PointwiseStrainGapVorticityShortcutValid ≡ false
round79PointwiseStrainGapVorticityShortcutValidIsFalse = refl

round79PressureScalarSufficientForEigenframeRotationIsFalse :
  round79PressureScalarSufficientForEigenframeRotation ≡ false
round79PressureScalarSufficientForEigenframeRotationIsFalse = refl

round79ClayPromotionIsFalse : round79ClayPromotion ≡ false
round79ClayPromotionIsFalse = refl
