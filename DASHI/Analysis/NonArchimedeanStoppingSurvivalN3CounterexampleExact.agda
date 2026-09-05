module DASHI.Analysis.NonArchimedeanStoppingSurvivalN3CounterexampleExact where

------------------------------------------------------------------------
-- EXACT n=3 COUNTEREXAMPLE TO THE ADVERTISED UNIVERSAL SURVIVAL BOUND
--
-- Source claim (mixing/stopping document): for every non-empty stopping set A,
--
--   P(T > t) <= sqrt(|A^c|) * 2^(-t/2).
--
-- Take Z/8Z, A={4}, initial state x0=1, and the literal Collatz relation
-- branches y=3x and y=3x-1 mod 8.  Every one of the eight three-step branch
-- words avoids state 4, hence P(T>3)=1.  The advertised right-hand side has
-- square 7/8, so it is strictly below 1.  Thus the universal bound is false as
-- stated, independently of the earlier L2-norm counterexample.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Integer.Base as Int using (+_)
open import Data.Rational as R using (_/_)
open import Data.Rational.Base using (ℚ; 1ℚ; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable.Core using (toWitness)

------------------------------------------------------------------------
-- Literal Z/8Z carrier and the two source branches.
------------------------------------------------------------------------

data State8 : Set where
  s0 s1 s2 s3 s4 s5 s6 s7 : State8

data Branch : Set where
  branch3x branch3xMinus1 : Branch

step : State8 → Branch → State8
step s0 branch3x = s0
step s0 branch3xMinus1 = s7
step s1 branch3x = s3
step s1 branch3xMinus1 = s2
step s2 branch3x = s6
step s2 branch3xMinus1 = s5
step s3 branch3x = s1
step s3 branch3xMinus1 = s0
step s4 branch3x = s4
step s4 branch3xMinus1 = s3
step s5 branch3x = s7
step s5 branch3xMinus1 = s6
step s6 branch3x = s2
step s6 branch3xMinus1 = s1
step s7 branch3x = s5
step s7 branch3xMinus1 = s4

endpoint3 : Branch → Branch → Branch → State8
endpoint3 b1 b2 b3 = step (step (step s1 b1) b2) b3

endpoint3Avoids4 :
  (b1 b2 b3 : Branch) → endpoint3 b1 b2 b3 ≢ s4
endpoint3Avoids4 branch3x branch3x branch3x ()
endpoint3Avoids4 branch3x branch3x branch3xMinus1 ()
endpoint3Avoids4 branch3x branch3xMinus1 branch3x ()
endpoint3Avoids4 branch3x branch3xMinus1 branch3xMinus1 ()
endpoint3Avoids4 branch3xMinus1 branch3x branch3x ()
endpoint3Avoids4 branch3xMinus1 branch3x branch3xMinus1 ()
endpoint3Avoids4 branch3xMinus1 branch3xMinus1 branch3x ()
endpoint3Avoids4 branch3xMinus1 branch3xMinus1 branch3xMinus1 ()

------------------------------------------------------------------------
-- Exact probability/envelope coordinates.
--
-- All 2^3 equally weighted branch words survive, so the finite three-step
-- survival probability is 8/8 = 1.
------------------------------------------------------------------------

threeStepSurvivalProbability : ℚ
threeStepSurvivalProbability = 1ℚ

threeStepSurvivalIsOne : threeStepSurvivalProbability ≡ 1ℚ
threeStepSurvivalIsOne = refl

sevenEighths : ℚ
sevenEighths = Int.+ 7 R./ 8

-- Squaring the advertised RHS sqrt(7) * 2^(-3/2) gives exactly 7/8.
advertisedSquaredEnvelopeAtThree : ℚ
advertisedSquaredEnvelopeAtThree = sevenEighths

sevenEighthsLessThanOne : sevenEighths < 1ℚ
sevenEighthsLessThanOne =
  toWitness {a? = sevenEighths ℚP.<? 1ℚ} _

sourceSquaredSurvivalBoundFails :
  ¬ (threeStepSurvivalProbability ≤ advertisedSquaredEnvelopeAtThree)
sourceSquaredSurvivalBoundFails bound =
  ℚP.<⇒≱ sevenEighthsLessThanOne bound

record ExactStoppingCounterexample : Set where
  constructor exactStoppingCounterexample
  field
    allThreeStepBranchWordsAvoidTarget :
      (b1 b2 b3 : Branch) → endpoint3 b1 b2 b3 ≢ s4
    survivalAtThreeIsOne : threeStepSurvivalProbability ≡ 1ℚ
    advertisedSquaredBoundWouldRequireImpossibleOrder :
      ¬ (threeStepSurvivalProbability ≤ advertisedSquaredEnvelopeAtThree)

canonicalStoppingCounterexample : ExactStoppingCounterexample
canonicalStoppingCounterexample =
  exactStoppingCounterexample
    endpoint3Avoids4
    threeStepSurvivalIsOne
    sourceSquaredSurvivalBoundFails
