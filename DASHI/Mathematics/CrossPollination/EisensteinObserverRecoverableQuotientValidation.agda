module DASHI.Mathematics.CrossPollination.EisensteinObserverRecoverableQuotientValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Rational.Base using (0ℚ)

import DASHI.Biology.EisensteinThreeSixSymmetryExact as ThreeSix
import DASHI.Mathematics.CrossPollination.EisensteinObserverRecoverableQuotientExact as E

phaseZero : E.phaseOfNat 0 ≡ ThreeSix.phaseOne
phaseZero = refl

phaseThree : E.phaseOfNat 3 ≡ ThreeSix.phaseOne
phaseThree = refl

quotientEight : E.quotient3 8 ≡ 2
quotientEight = refl

reopenEight : E.reopen3 (E.phaseOfNat 8) (E.quotient3 8) ≡ 8
reopenEight = E.reopenPhaseQuotient 8

phaseRoundTrip :
  E.phaseOfNat (E.reopen3 ThreeSix.phaseOmegaSquared 7)
  ≡ ThreeSix.phaseOmegaSquared
phaseRoundTrip = E.phaseOfReopen ThreeSix.phaseOmegaSquared 7

quotientRoundTrip :
  E.quotient3 (E.reopen3 ThreeSix.phaseOmega 9) ≡ 9
quotientRoundTrip = E.quotientOfReopen ThreeSix.phaseOmega 9

chiAtZero : E.chiMinus3PhaseWeight ThreeSix.phaseOne ≡ 0ℚ
chiAtZero = refl

antisymmetricOmegaFactorization :
  E.antisymmetricNumerator ThreeSix.phaseOmega
  ≡ E.scaleEisenstein
      (E.chiMinus3PhaseWeight ThreeSix.phaseOmega)
      E.antisymmetricDenominator
antisymmetricOmegaFactorization = E.antisymmetricCharacterFactorization ThreeSix.phaseOmega

coarseCollision : E.phaseOfNat 0 ≡ E.phaseOfNat 3
coarseCollision = refl

reopeningStillExactAtThree :
  E.reopen3 (E.phaseOfNat 3) (E.quotient3 3) ≡ 3
reopeningStillExactAtThree = E.reopenPhaseQuotient 3
