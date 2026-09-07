module DASHI.Physics.Closure.NSTriadKNR299NormalizedCompanionSameObjectRound494Exact where

------------------------------------------------------------------------
-- ROUND494 / EXACT NORMALIZATION OF THE LITERAL QUADRATIC COMPANION
--
-- R439's literal companion fold is built from the DOUBLED projected forcing.
-- R440 identifies the corresponding physical Hermitian cross with that literal
-- companion cross.  R441 separately proves that the same R440 physical cross
-- is exactly twice the R299-normalized common cross C_k.
--
-- Therefore the correct same-object theorem is
--
--   2 * C_k = literal R439 quadratic-companion cross,
--
-- not C_k = literal companion cross.  This file closes that finite
-- normalization exactly and prevents a factor-of-two receipt-laundering bug.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _*_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNWeightedCompanionHermitianCrossRound439Exact as R439
import DASHI.Physics.Closure.NSTriadKNPhysicalHeatDoubleSumFactorizationRound440Exact as R440
import DASHI.Physics.Closure.NSTriadKNPhysicalR299FactorizedCompanionRound441Exact as R441

F : C3.RealField _
F = Rational.rationalRealField

twoR299CommonIsLiteralCompanion :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (H : R142.HelicalHalfCalibration S)
    (W : R294.SwapInvariantCellWeight F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode))
    (output : Z3.FourierMode) →
  R441.two * R441.fixedOutputR299CommonCross W S system output
  ≡ R439.fixedOutputWeightedCompanionCross E I S W system output
      (R440.weightedAmplitudeAggregate W S system
        (DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber.physicalOutputFiber
          (Audit.cutoff system) output))
twoR299CommonIsLiteralCompanion S L H W system velocityTransverse output =
  trans
    (sym (R441.r440CommonCrossIsTwoR299CommonCross W S system output))
    (R440.fixedOutputCommonCrossIsQuadraticCompanionCross
      S L H W system velocityTransverse output)

round494R299NormalizationToLiteralCompanionClosed : Bool
round494R299NormalizationToLiteralCompanionClosed = true

round494R299CommonEqualsLiteralCompanionWithoutFactorTwo : Bool
round494R299CommonEqualsLiteralCompanionWithoutFactorTwo = false

round494IntroducesAnalyticEstimate : Bool
round494IntroducesAnalyticEstimate = false

round494TrajectoryIntegrationWeldClosed : Bool
round494TrajectoryIntegrationWeldClosed = false

round494SignedSpacetimeEstimateClosed : Bool
round494SignedSpacetimeEstimateClosed = false

round494ClayPromotion : Bool
round494ClayPromotion = false

round494R299NormalizationToLiteralCompanionClosedIsTrue :
  round494R299NormalizationToLiteralCompanionClosed ≡ true
round494R299NormalizationToLiteralCompanionClosedIsTrue = refl

round494R299CommonEqualsLiteralCompanionWithoutFactorTwoIsFalse :
  round494R299CommonEqualsLiteralCompanionWithoutFactorTwo ≡ false
round494R299CommonEqualsLiteralCompanionWithoutFactorTwoIsFalse = refl

round494ClayPromotionIsFalse : round494ClayPromotion ≡ false
round494ClayPromotionIsFalse = refl
