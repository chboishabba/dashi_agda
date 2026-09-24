module DASHI.Physics.Closure.NSWholeSpaceActualSignedLebesgueEndgameExact where

------------------------------------------------------------------------
-- WHOLE-SPACE A5 / ACTUAL COMPENSATED FIELD -> SIGNED LEBESGUE ENDGAME
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact as Euclidean
import DASHI.Physics.Closure.NSTriadKNEuclideanLebesgueSignedAggregationExact as Lebesgue
import DASHI.Physics.Closure.NSLebesgueSignedSecondMomentAggregationExact as Second
import DASHI.Physics.Closure.NSWholeSpaceCompensatedMajorantLowHighGlueExact as Glue
import DASHI.Physics.Closure.NSWholeSpacePhysicalCompensatedFieldCompilerExact as Field
import DASHI.Physics.Closure.NSWholeSpaceActualPhysicalCompensatedFieldExact as Actual
import DASHI.Physics.Closure.NSWholeSpaceSignedLebesgueEndgameExact as End

record ActualSignedLebesgueEndgameInputs
    (dataSet : Euclidean.EuclideanSignedFluxData)
    (base : Lebesgue.EuclideanLebesgueIntegralAuthority dataSet)
    (additive : Glue.AdditiveIntegrabilityAuthority base) : Set₁ where
  field
    convolutionMeasure :
      Lebesgue.EuclideanConvolutionMeasureAuthority

    orderedIntegral :
      Second.OrderedEuclideanLebesgueAuthority base

    physicalField :
      Actual.ActualPhysicalCompensatedFieldInputs base additive

open ActualSignedLebesgueEndgameInputs public

wholeSpaceSignedLebesgueEndgame :
  ∀ {dataSet base additive} →
  ActualSignedLebesgueEndgameInputs dataSet base additive →
  End.WholeSpaceSignedLebesgueEndgame dataSet base
wholeSpaceSignedLebesgueEndgame I = record
  { End.convolutionMeasure = convolutionMeasure I
  ; End.orderedIntegral = orderedIntegral I
  ; End.compensatedField =
      Field.compilePhysicalCompensatedField
        (Actual.actualPhysicalCompensatedField (physicalField I))
  }

actualSignedLebesgueEndgameCompilerClosed : Bool
actualSignedLebesgueEndgameCompilerClosed = true

actualSignedLebesgueEndgameIntroducesPostulate : Bool
actualSignedLebesgueEndgameIntroducesPostulate = false

lowYoungCauchyAnalyticProducerInhabitedHere : Bool
lowYoungCauchyAnalyticProducerInhabitedHere = false

highInverseSixthAnalyticProducerInhabitedHere : Bool
highInverseSixthAnalyticProducerInhabitedHere = false

clayPromotion : Bool
clayPromotion = false

actualSignedLebesgueEndgameCompilerClosedIsTrue :
  actualSignedLebesgueEndgameCompilerClosed ≡ true
actualSignedLebesgueEndgameCompilerClosedIsTrue = refl
