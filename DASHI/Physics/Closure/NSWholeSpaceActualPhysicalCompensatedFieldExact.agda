module DASHI.Physics.Closure.NSWholeSpaceActualPhysicalCompensatedFieldExact where

------------------------------------------------------------------------
-- WHOLE-SPACE A4 / ACTUAL PHYSICAL LOW-HIGH DATA -> COMPENSATED FIELD
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Real as BishopReal

import DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact as Euclidean
import DASHI.Physics.Closure.NSTriadKNEuclideanLebesgueSignedAggregationExact as Lebesgue
import DASHI.Physics.Closure.NSWholeSpaceLowFrequencyCompensationExact as Low
import DASHI.Physics.Closure.NSWholeSpaceCompensatedMajorantLowHighGlueExact as Glue
import DASHI.Physics.Closure.NSWholeSpacePhysicalMajorantDominationExact as Dom
import DASHI.Physics.Closure.NSWholeSpacePhysicalCompensatedFieldCompilerExact as Field
import DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact as Reciprocal

record ActualPhysicalCompensatedFieldInputs
    {dataSet : Euclidean.EuclideanSignedFluxData}
    (base : Lebesgue.EuclideanLebesgueIntegralAuthority dataSet)
    (additive : Glue.AdditiveIntegrabilityAuthority base) : Set₁ where
  field
    domination : Dom.PhysicalMajorantDomination base

    heatRate stateFactor majorant coefficient :
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

    globalMajorant :
      Euclidean.EuclideanInteraction → BishopReal.ℝ

    globalSplitsLowHigh :
      (I : Euclidean.EuclideanInteraction) →
      globalMajorant I
      ≡ BishopReal._+_
          (Dom.lowPhysicalMajorant domination I)
          (Dom.highPhysicalMajorant domination I)

    globalMajorantIsPhysicalProduct :
      (I : Euclidean.EuclideanInteraction) →
      globalMajorant I ≡ BishopReal._*_ (coefficient I) (majorant I)

open ActualPhysicalCompensatedFieldInputs public

actualLowHighMajorant :
  ∀ {dataSet base additive} →
  (I : ActualPhysicalCompensatedFieldInputs {dataSet} base additive) →
  Glue.PhysicalLowHighMajorant base
actualLowHighMajorant I = record
  { Glue.globalMajorant = globalMajorant I
  ; Glue.lowMajorant = Dom.lowPhysicalMajorant (domination I)
  ; Glue.highMajorant = Dom.highPhysicalMajorant (domination I)
  ; Glue.lowIntegrable =
      Dom.lowPhysicalIntegrableFromConvolution (domination I)
  ; Glue.highIntegrable =
      Dom.highPhysicalIntegrableFromWeightedConvolution (domination I)
  ; Glue.globalSplitsLowHigh = globalSplitsLowHigh I
  }

actualPhysicalCompensatedField :
  ∀ {dataSet base additive} →
  (I : ActualPhysicalCompensatedFieldInputs {dataSet} base additive) →
  Field.PhysicalCompensatedFieldData base additive
actualPhysicalCompensatedField I = record
  { Field.heatRate = heatRate I
  ; Field.stateFactor = stateFactor I
  ; Field.majorant = majorant I
  ; Field.coefficient = coefficient I
  ; Field.coefficientNonnegative = coefficientNonnegative I
  ; Field.pointwiseCompensation = pointwiseCompensation I
  ; Field.compensatedIntegrandNonnegative =
      compensatedIntegrandNonnegative I
  ; Field.lowHighMajorant = actualLowHighMajorant I
  ; Field.lowHighMajorantIsPhysicalProduct =
      globalMajorantIsPhysicalProduct I
  }

actualPhysicalCompensatedFieldCompilerClosed : Bool
actualPhysicalCompensatedFieldCompilerClosed = true

actualPhysicalCompensatedFieldIntroducesPostulate : Bool
actualPhysicalCompensatedFieldIntroducesPostulate = false

clayPromotion : Bool
clayPromotion = false

actualPhysicalCompensatedFieldCompilerClosedIsTrue :
  actualPhysicalCompensatedFieldCompilerClosed ≡ true
actualPhysicalCompensatedFieldCompilerClosedIsTrue = refl
