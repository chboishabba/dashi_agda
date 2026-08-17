module DASHI.Moonshine.P11MarkedJointSpectrumHighestAlphaRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (_*_; _/_; -_)

import DASHI.Moonshine.P11FiveStatePositiveHeckeLiftExact as Fine
import DASHI.Moonshine.P11MarkedX2JointHeckeFrobeniusSpectrumExact as Joint

constantT3AtA0 :
  Joint.markedT3 Joint.constantMode Fine.a0
  ≡ (+ 4 / 1) * Joint.constantMode Fine.a0
constantT3AtA0 = Joint.constantT3Eigen Fine.a0

frobeniusOddLineAtA0 :
  Joint.frobeniusPullback Joint.aAntiMode Fine.a0
  ≡ - Joint.aAntiMode Fine.a0
frobeniusOddLineAtA0 = Joint.aAntiFrobeniusOdd Fine.a0

mixedEvenT3AtB0 :
  Joint.markedT3 Joint.mixedEvenMode Fine.b0
  ≡ - Joint.mixedEvenMode Fine.b0
mixedEvenT3AtB0 = Joint.mixedT3Eigen Fine.b0

mixedEvenT5AtB0 :
  Joint.markedT5 Joint.mixedEvenMode Fine.b0
  ≡ Joint.mixedEvenMode Fine.b0
mixedEvenT5AtB0 = Joint.mixedT5Eigen Fine.b0

arbitraryObservableReconstructsAtB2 :
  (observable : Joint.Observable5) →
  Joint.reconstruct observable Fine.b2 ≡ observable Fine.b2
arbitraryObservableReconstructsAtB2 observable =
  Joint.jointBasisSpans observable Fine.b2

threeJointSignatures :
  Joint.numberOfDistinctJointSignatures Joint.canonicalJointSpectrumBoundary ≡ 3
threeJointSignatures = refl

nonconstantEvenMultiplicityThree :
  Joint.nonconstantEvenJointMultiplicity Joint.canonicalJointSpectrumBoundary ≡ 3
nonconstantEvenMultiplicityThree = refl
