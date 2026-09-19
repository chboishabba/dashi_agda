module DASHI.Biology.Agriculture.QueenslandLegumeResidueFirstOrderKineticsRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.QueenslandLegumeResidueFirstOrderKineticsExact as K

doiPinned : K.thomsonEtAl2007DOI ≡ "10.1071/EA05290"
doiPinned = refl

experimentDurationPinned :
  K.experimentDurationWeeks K.thomson2007Kinetics ≡ 17
experimentDurationPinned = refl

lowerRatePinned :
  K.rateLowerMilliPerWeek K.thomson2007Kinetics ≡ 45
lowerRatePinned = refl

upperRatePinned :
  K.rateUpperMilliPerWeek K.thomson2007Kinetics ≡ 325
upperRatePinned = refl

lowerHalfTimePinned :
  K.halfTimeLowerTenthsWeeks K.thomson2007Kinetics ≡ 21
lowerHalfTimePinned = refl

upperHalfTimePinned :
  K.halfTimeUpperTenthsWeeks K.thomson2007Kinetics ≡ 154
upperHalfTimePinned = refl

firstOrderShapeOwned :
  K.firstOrderResidueReleaseShapeObserved
    K.canonicalFirstOrderKineticsBoundary ≡ true
firstOrderShapeOwned = refl

notUniversalK :
  K.reportedRateRangeImpliesOneUniversalRate
    K.canonicalFirstOrderKineticsBoundary ≡ false
notUniversalK = refl

notAcaciaSameObject :
  K.northernAustralianResidueKineticsCreatesAcaciaSameObjectKernel
    K.canonicalFirstOrderKineticsBoundary ≡ false
notAcaciaSameObject = refl

notLivingRoot :
  K.residueMineralisationKineticsEqualsLivingBelowGroundTransfer
    K.canonicalFirstOrderKineticsBoundary ≡ false
notLivingRoot = refl

continuousFitNotDiscreteBishopRatio :
  K.continuousFirstOrderFitDirectlySuppliesDiscreteBishopRatio
    K.canonicalFirstOrderKineticsBoundary ≡ false
continuousFitNotDiscreteBishopRatio = refl


upperHalfTimeInsideObservedWindow :
  K.reportedUpperHalfTimeInsideExperimentWindow
    K.canonicalFirstOrderKineticsBoundary ≡ true
upperHalfTimeInsideObservedWindow = refl

finiteFitNotInfiniteTailAuthority :
  K.finiteFirstOrderFitAuthorizesInfiniteHorizonExtrapolation
    K.canonicalFirstOrderKineticsBoundary ≡ false
finiteFitNotInfiniteTailAuthority = refl
