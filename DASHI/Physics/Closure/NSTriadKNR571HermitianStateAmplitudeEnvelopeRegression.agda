module DASHI.Physics.Closure.NSTriadKNR571HermitianStateAmplitudeEnvelopeRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNR571HermitianStateAmplitudeEnvelopeExact as G1

localHermitianG1EnvelopeClosed :
  G1.r571LocalHermitianG1EnvelopeClosed ≡ true
localHermitianG1EnvelopeClosed =
  G1.r571LocalHermitianG1EnvelopeClosedIsTrue

g1UsesNoSquareRoot :
  G1.r571LocalHermitianG1UsesSquareRoot ≡ false
g1UsesNoSquareRoot =
  G1.r571LocalHermitianG1UsesSquareRootIsFalse

g2StillSeparate :
  G1.r571LocalHermitianG2ClosedHere ≡ false
g2StillSeparate =
  G1.r571LocalHermitianG2ClosedHereIsFalse

fullStateEnvelopeStillOpen :
  G1.r571FullStateDerivativeEnvelopeClosed ≡ false
fullStateEnvelopeStillOpen =
  G1.r571FullStateDerivativeEnvelopeClosedIsFalse
