module DASHI.Physics.Closure.NSTriadKNRationalResolventFromPositiveGramPairRound384Exact where

------------------------------------------------------------------------
-- ROUND384 / CROSS-POLLINATION: YM RATIONAL RECIPROCAL -> NS R290 RESOLVENT
--
-- R291 already owns the exact damped Gram tangent.  R290 asks only for a
-- scalar weight w with w * pairRate = 1.  The Yang--Mills lane already proves
-- the constructive rational reciprocal law for every positive rational.
--
-- Therefore a positive R291 pair rate compiles directly into the exact R290
-- DampedGramPair.  No heat exponential and no analytic estimate is involved.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; Positive)

import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNWeightedGramFluxCompilerRound290Exact as R290
import DASHI.Physics.YangMills.BalabanClayGate4RationalPositiveMassReciprocalExact as Reciprocal

positivePairBuildsR290 :
  (pair : R291.DampedCellPair) →
  Positive (R291.pairRate pair) →
  R290.DampedGramPair
positivePairBuildsR290 pair pairRatePositive = record
  { R290.gram = R291.gram pair
  ; R290.pairRate = R291.pairRate pair
  ; R290.nonlinearRemainder = R291.nonlinearGramRemainder pair
  ; R290.gramTangent = R291.gramTangent pair
  ; R290.resolventWeight =
      Reciprocal.safeRationalReciprocal (R291.pairRate pair)
  ; R290.tangentLaw = R291.gramPairDampedTangent pair
  ; R290.resolventLaw =
      Reciprocal.safeRationalReciprocalTimesPositive
        (R291.pairRate pair) pairRatePositive
  }

round384R291ToR290CompilerClosed : Bool
round384R291ToR290CompilerClosed = true

round384ExactReciprocalArithmeticReusedFromYM : Bool
round384ExactReciprocalArithmeticReusedFromYM = true

round384OnlyRemainingRatePremiseIsPositivity : Bool
round384OnlyRemainingRatePremiseIsPositivity = true

round384R291ToR290CompilerClosedIsTrue :
  round384R291ToR290CompilerClosed ≡ true
round384R291ToR290CompilerClosedIsTrue = refl
