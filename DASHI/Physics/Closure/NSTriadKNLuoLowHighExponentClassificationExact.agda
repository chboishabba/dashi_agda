module DASHI.Physics.Closure.NSTriadKNLuoLowHighExponentClassificationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions of
-- Euler's Equation".
-- DOI: 10.1007/BF02099744.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Complete the exponent table for the centered second-moment low--high
-- commutator.  Write x=1/a, y=1/b with x+y=1/2.  The two Taylor branches have
-- frequency degrees
--
--   lambda_r^(7/2-3x) lambda_q^(1/2-3y),
--   lambda_r^(5/2-3x) lambda_q^(3/2-3y).
--
-- Both have total degree 5/2.  After extracting the critical low-shell factor
-- lambda_r^(3/2) and one output derivative lambda_q, the remaining powers are
-- pure gap factors
--
--   (lambda_r/lambda_q)^(2-3x),
--   (lambda_r/lambda_q)^(1-3x).
--
-- The table proves that (a,b)=(infinity,2) gives gap powers 2 and 1, while
-- (6,3) gives 3/2 and 1/2.  The pair (2,infinity) fails in the second branch.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality as Eq using (cong)
open Eq.≡-Reasoning

zero half minusHalf one threeHalves two four fiveHalves : ℚ
zero = Int.+ 0 / 1
half = Int.+ 1 / 2
minusHalf = Int.-[1+ 0 ] / 2
one = Int.+ 1 / 1
threeHalves = Int.+ 3 / 2
two = Int.+ 2 / 1
four = Int.+ 4 / 1
fiveHalves = Int.+ 5 / 2

oneThird oneSixth : ℚ
oneThird = Int.+ 1 / 3
oneSixth = Int.+ 1 / 6

record HolderReciprocalPair : Set where
  constructor holder-reciprocal-pair
  field
    lowReciprocal highReciprocal : ℚ
    holderBalance :
      lowReciprocal + highReciprocal ≡ half

open HolderReciprocalPair public

firstLowDegree : HolderReciprocalPair → ℚ
firstLowDegree pair =
  Int.+ 7 / 2 - (Int.+ 3 / 1 * lowReciprocal pair)

firstHighDegree : HolderReciprocalPair → ℚ
firstHighDegree pair =
  half - (Int.+ 3 / 1 * highReciprocal pair)

secondLowDegree : HolderReciprocalPair → ℚ
secondLowDegree pair =
  fiveHalves - (Int.+ 3 / 1 * lowReciprocal pair)

secondHighDegree : HolderReciprocalPair → ℚ
secondHighDegree pair =
  threeHalves - (Int.+ 3 / 1 * highReciprocal pair)

firstTotalDegree :
  (pair : HolderReciprocalPair) →
  firstLowDegree pair + firstHighDegree pair ≡ fiveHalves
firstTotalDegree pair =
  begin
    firstLowDegree pair + firstHighDegree pair
  ≡⟨ solve (lowReciprocal pair ∷ highReciprocal pair ∷ []) ⟩
    four - Int.+ 3 / 1
      * (lowReciprocal pair + highReciprocal pair)
  ≡⟨ cong (λ sum → four - Int.+ 3 / 1 * sum)
       (holderBalance pair) ⟩
    four - Int.+ 3 / 1 * half
  ≡⟨ solve [] ⟩
    fiveHalves
  ∎

secondTotalDegree :
  (pair : HolderReciprocalPair) →
  secondLowDegree pair + secondHighDegree pair ≡ fiveHalves
secondTotalDegree pair =
  begin
    secondLowDegree pair + secondHighDegree pair
  ≡⟨ solve (lowReciprocal pair ∷ highReciprocal pair ∷ []) ⟩
    four - Int.+ 3 / 1
      * (lowReciprocal pair + highReciprocal pair)
  ≡⟨ cong (λ sum → four - Int.+ 3 / 1 * sum)
       (holderBalance pair) ⟩
    four - Int.+ 3 / 1 * half
  ≡⟨ solve [] ⟩
    fiveHalves
  ∎

firstGapDegree : HolderReciprocalPair → ℚ
firstGapDegree pair = firstLowDegree pair - threeHalves

secondGapDegree : HolderReciprocalPair → ℚ
secondGapDegree pair = secondLowDegree pair - threeHalves

firstGapFormula :
  (pair : HolderReciprocalPair) →
  firstGapDegree pair
  ≡ two - (Int.+ 3 / 1 * lowReciprocal pair)
firstGapFormula pair = solve (lowReciprocal pair ∷ [])

secondGapFormula :
  (pair : HolderReciprocalPair) →
  secondGapDegree pair
  ≡ one - (Int.+ 3 / 1 * lowReciprocal pair)
secondGapFormula pair = solve (lowReciprocal pair ∷ [])

pairThreeSix : HolderReciprocalPair
pairThreeSix = holder-reciprocal-pair oneThird oneSixth (solve [])

pairSixThree : HolderReciprocalPair
pairSixThree = holder-reciprocal-pair oneSixth oneThird (solve [])

pairInfinityTwo : HolderReciprocalPair
pairInfinityTwo = holder-reciprocal-pair zero half (solve [])

pairTwoInfinity : HolderReciprocalPair
pairTwoInfinity = holder-reciprocal-pair half zero (solve [])

threeSixFirstGap : firstGapDegree pairThreeSix ≡ one
threeSixFirstGap = solve []

threeSixSecondGap : secondGapDegree pairThreeSix ≡ zero
threeSixSecondGap = solve []

sixThreeFirstGap : firstGapDegree pairSixThree ≡ threeHalves
sixThreeFirstGap = solve []

sixThreeSecondGap : secondGapDegree pairSixThree ≡ half
sixThreeSecondGap = solve []

infinityTwoFirstGap : firstGapDegree pairInfinityTwo ≡ two
infinityTwoFirstGap = solve []

infinityTwoSecondGap : secondGapDegree pairInfinityTwo ≡ one
infinityTwoSecondGap = solve []

twoInfinityFirstGap : firstGapDegree pairTwoInfinity ≡ half
twoInfinityFirstGap = solve []

twoInfinitySecondGap :
  secondGapDegree pairTwoInfinity ≡ minusHalf
twoInfinitySecondGap = solve []
