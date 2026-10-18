module DASHI.Moonshine.Monster369SignedPairNineOrbitValidation where

open import DASHI.Core.Prelude

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as SSP
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Moonshine.Monster369SignedPairNineOrbitExact as P

zeroPairRegression :
  P.signedPairOrbit SSP.zeroMultiplicity SSP.zeroMultiplicity
  ≡ Triadic.zeroOrbit
zeroPairRegression = refl

firstAxisRegression :
  P.signedPairOrbit (SSP.positiveMultiplicity 0) SSP.zeroMultiplicity
  ≡ Triadic.firstAxisOrbit
firstAxisRegression = refl

secondAxisRegression :
  P.signedPairOrbit SSP.zeroMultiplicity (SSP.negativeMultiplicity 0)
  ≡ Triadic.secondAxisOrbit
secondAxisRegression = refl

equalSignRegression :
  P.signedPairOrbit (SSP.positiveMultiplicity 0) (SSP.positiveMultiplicity 1)
  ≡ Triadic.equalSignOrbit
equalSignRegression = refl

oppositeSignRegression :
  P.signedPairOrbit (SSP.positiveMultiplicity 0) (SSP.negativeMultiplicity 1)
  ≡ Triadic.oppositeSignOrbit
oppositeSignRegression = refl

simultaneousNegationRegression :
  (a b : SSP.SignedMultiplicity) ->
  P.signedPairOrbit (SSP.negateMultiplicity a) (SSP.negateMultiplicity b)
  ≡ P.signedPairOrbit a b
simultaneousNegationRegression = P.signedPairOrbitNegationInvariant

quarterTurnDescendsRegression :
  (a b : SSP.SignedMultiplicity) ->
  P.signedPairOrbitOfQuarterTurn a b
  ≡ P.rotateOrbit (P.signedPairOrbit a b)
quarterTurnDescendsRegression = P.signedPairQuarterTurnDescends

axisReflectionDescendsRegression :
  (a b : SSP.SignedMultiplicity) ->
  P.signedPairOrbitOfAxisReflection a b
  ≡ P.reflectAxisOrbit (P.signedPairOrbit a b)
axisReflectionDescendsRegression = P.signedPairAxisReflectionDescends
