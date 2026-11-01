module DASHI.Physics.Closure.NSWholeSpacePhysicalCompensatedFieldCompilerExact where

------------------------------------------------------------------------
-- WHOLE-SPACE A / BUILD THE COMPENSATED FIELD FROM LOW/HIGH PHYSICAL PIECES
--
-- NSLebesgueSignedSecondMomentAggregationExact deliberately requires
-- compensatedMajorantIntegrable as a field.  The new low/high glue theorem
-- lets us derive that field rather than assume it wholesale.
--
-- Thus A's remaining majorant producer is split into two honest analytic jobs:
--
--   low  : compensation near xi = 0 gives an integrable physical majorant;
--   high : decay/dissipation gives an integrable high-frequency majorant.
--
-- Their pointwise sum is then compiled into the exact compensated field
-- consumed by the existing Lebesgue second-moment theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Real as BishopReal

import DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact as Euclidean
import DASHI.Physics.Closure.NSTriadKNEuclideanLebesgueSignedAggregationExact as Lebesgue
import DASHI.Physics.Closure.NSWholeSpaceLowFrequencyCompensationExact as Low
import DASHI.Physics.Closure.NSLebesgueSignedSecondMomentAggregationExact as Second
import DASHI.Physics.Closure.NSWholeSpaceCompensatedMajorantLowHighGlueExact as Glue
import DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact as Reciprocal

record PhysicalCompensatedFieldData
    {dataSet : Euclidean.EuclideanSignedFluxData}
    (base : Lebesgue.EuclideanLebesgueIntegralAuthority dataSet)
    (additive : Glue.AdditiveIntegrabilityAuthority base) : Set₁ where
  field
    heatRate :
      Euclidean.EuclideanInteraction → BishopReal.ℝ
    stateFactor :
      Euclidean.EuclideanInteraction → BishopReal.ℝ
    majorant :
      Euclidean.EuclideanInteraction → BishopReal.ℝ
    coefficient :
      Euclidean.EuclideanInteraction → BishopReal.ℝ

    coefficientNonnegative :
      (I : Euclidean.EuclideanInteraction) →
      BishopReal.NonNegative (coefficient I)

    pointwiseCompensation :
      (I : Euclidean.EuclideanInteraction) →
      Low.BishopLowFrequencyStateCompensation
        (heatRate I) (stateFactor I) (majorant I)

    compensatedIntegrandNonnegative :
      (I : Euclidean.EuclideanInteraction) →
      BishopReal.NonNegative
        (BishopReal._*_
          (coefficient I)
          (BishopReal._*_
            (Low.inverseCube
              (heatRate I)
              (Reciprocal.xNonzero
                (Low.heatRatePositive (pointwiseCompensation I))))
            (stateFactor I)))

    lowHighMajorant :
      Glue.PhysicalLowHighMajorant base

    lowHighMajorantIsPhysicalProduct :
      (I : Euclidean.EuclideanInteraction) →
      Glue.globalMajorant lowHighMajorant I
      ≡ BishopReal._*_ (coefficient I) (majorant I)

open PhysicalCompensatedFieldData public

physicalMajorantProductIntegrable :
  ∀ {dataSet base additive} →
  (D : PhysicalCompensatedFieldData {dataSet} base additive) →
  Lebesgue.Integrable base
    (λ I → BishopReal._*_ (coefficient D I) (majorant D I))
physicalMajorantProductIntegrable {additive = additive} D =
  Glue.integrableRespectsPointwise additive
    (lowHighMajorantIsPhysicalProduct D)
    (Glue.globalPhysicalMajorantIntegrable
      additive (lowHighMajorant D))

compilePhysicalCompensatedField :
  ∀ {dataSet base additive} →
  (D : PhysicalCompensatedFieldData {dataSet} base additive) →
  Second.LowFrequencySecondMomentField base
compilePhysicalCompensatedField D =
  record
    { Second.heatRate = heatRate D
    ; Second.stateFactor = stateFactor D
    ; Second.majorant = majorant D
    ; Second.coefficient = coefficient D
    ; Second.coefficientNonnegative = coefficientNonnegative D
    ; Second.pointwiseCompensation = pointwiseCompensation D
    ; Second.compensatedIntegrandNonnegative =
        compensatedIntegrandNonnegative D
    ; Second.compensatedMajorantIntegrable =
        physicalMajorantProductIntegrable D
    }

lowHighPiecesCompileExactCompensatedField : Bool
lowHighPiecesCompileExactCompensatedField = true

wholeSpaceMajorantIntegrabilityStillMonolithicInput : Bool
wholeSpaceMajorantIntegrabilityStillMonolithicInput = false

lowPhysicalMajorantAnalyticProducerClosedHere : Bool
lowPhysicalMajorantAnalyticProducerClosedHere = false

highPhysicalMajorantAnalyticProducerClosedHere : Bool
highPhysicalMajorantAnalyticProducerClosedHere = false

clayPromotion : Bool
clayPromotion = false

lowHighPiecesCompileExactCompensatedFieldIsTrue :
  lowHighPiecesCompileExactCompensatedField ≡ true
lowHighPiecesCompileExactCompensatedFieldIsTrue = refl

wholeSpaceMajorantIntegrabilityStillMonolithicInputIsFalse :
  wholeSpaceMajorantIntegrabilityStillMonolithicInput ≡ false
wholeSpaceMajorantIntegrabilityStillMonolithicInputIsFalse = refl
