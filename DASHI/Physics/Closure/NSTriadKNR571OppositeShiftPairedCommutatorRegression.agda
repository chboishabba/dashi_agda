module DASHI.Physics.Closure.NSTriadKNR571OppositeShiftPairedCommutatorRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNR571OppositeShiftPairedCommutatorExact as P

oppositeShiftGeometryClosed :
  P.r571OppositeShiftGeometryClosed ≡ true
oppositeShiftGeometryClosed = refl

pairedRawScalarIdentityClosed :
  P.r571OppositeShiftPairedRawScalarIdentityClosed ≡ true
pairedRawScalarIdentityClosed = refl

noEnvelopeEstimateIntroduced :
  P.r571OppositeShiftIntroducesEnvelopeEstimate ≡ false
noEnvelopeEstimateIntroduced = refl

noR568Promoted :
  P.r571OppositeShiftClosesR568 ≡ false
noR568Promoted = refl
