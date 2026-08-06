module DASHI.Visualisation.EventSeparationQuantisationRegression where

open import DASHI.Core.Prelude

import DASHI.Visualisation.EventSeparationQuantisationExact as Event

separationMedianRegression :
  Event.medianThree
    Event.distanceNear
    Event.distanceMiddle
    Event.distanceFar
  ≡
  Event.distanceMiddle
separationMedianRegression = Event.medianIgnoresOneFarOutlier

emptyNeighbourhoodRegression :
  Event.localSeparation Event.emptyNeighbourhood
  ≡
  Event.distanceMiddle
emptyNeighbourhoodRegression =
  Event.emptyNeighbourhoodUsesDeclaredFallback

externalTimeProductRegression :
  Event.externalTimeContribution Event.canonicalSemanticTimeKernel
  ≡
  Event.blockDiagonalJointContribution Event.canonicalSemanticTimeKernel
externalTimeProductRegression = Event.externalAndJointProductAgree

parameterQuantisationRegression :
  Event.parameterError Event.exactParameters Event.quantisedParameters
  ≡
  Event.parameterErrorTuple 1 1 0 1
parameterQuantisationRegression = Event.canonicalParameterError

fieldErrorRegression :
  Event.fieldErrorCode
    Event.canonicalSensitivity
    (Event.parameterError Event.exactParameters Event.quantisedParameters)
  ≡
  9
fieldErrorRegression = Event.canonicalFieldErrorCodeIsNine

nonlinearInteriorRegression :
  Event.nonlinearCellResponse Event.interiorParameterPeak
  ≡
  Event.nonlinearCellResponse Event.upperParameterCorner
  →
  ⊥
nonlinearInteriorRegression = Event.interiorPeakExceedsUpperCorner
