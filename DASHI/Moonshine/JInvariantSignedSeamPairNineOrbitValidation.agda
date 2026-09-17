module DASHI.Moonshine.JInvariantSignedSeamPairNineOrbitValidation where

open import DASHI.Core.Prelude

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as SSP
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Moonshine.JInvariantOrderThreeOrbitBalancedTernaryBidiExact as Orbit
import DASHI.Moonshine.JInvariantSignedSeamPairNineOrbitExact as P

bothIdentityRegression :
  P.seamPairOrbit SSP.zeroMultiplicity SSP.zeroMultiplicity
  ≡ Triadic.zeroOrbit
bothIdentityRegression = refl

sameDirectionRegression :
  P.seamPairOrbit (SSP.negativeMultiplicity 0) (SSP.negativeMultiplicity 1)
  ≡ Triadic.equalSignOrbit
sameDirectionRegression = refl

oppositeDirectionRegression :
  P.seamPairOrbit (SSP.negativeMultiplicity 0) (SSP.positiveMultiplicity 1)
  ≡ Triadic.oppositeSignOrbit
oppositeDirectionRegression = refl

firstSeamMeaningRegression :
  P.firstSeamDynamics (SSP.negativeMultiplicity 0) (SSP.positiveMultiplicity 1)
  ≡ Orbit.convergingSeam
firstSeamMeaningRegression = refl

secondSeamMeaningRegression :
  P.secondSeamDynamics (SSP.negativeMultiplicity 0) (SSP.positiveMultiplicity 1)
  ≡ Orbit.divergingSeam
secondSeamMeaningRegression = refl
