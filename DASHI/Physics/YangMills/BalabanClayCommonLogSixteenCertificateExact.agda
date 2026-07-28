module DASHI.Physics.YangMills.BalabanClayCommonLogSixteenCertificateExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Unit using (tt)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 1ℚ; _+_; _*_; _≤_; _≤ᵇ_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literature normalization.
--
-- Marc Daumas, David Lester and César Muñoz,
-- "Verified Real Number Calculations: A Library for Interval Arithmetic",
-- IEEE Transactions on Computers 58 (2009), 226--237.
-- DOI: 10.1109/TC.2008.213; arXiv:0708.3721
-- Relationship: formally verified rational interval evaluation of elementary
-- functions.  The finite exponential partial sum below is DASHI-owned.
------------------------------------------------------------------------

threeℚ sixteenℚ : ℚ
threeℚ = + 3 / 1
sixteenℚ = + 16 / 1

-- 1 + 3 + 3^2/2! + 3^3/3! + 3^4/4! = 131/8 > 16.
expThreeFourthPartialSum : ℚ
expThreeFourthPartialSum =
  1ℚ
  + threeℚ
  + (threeℚ * threeℚ) * (+ 1 / 2)
  + (threeℚ * threeℚ * threeℚ) * (+ 1 / 6)
  + (threeℚ * threeℚ * threeℚ * threeℚ) * (+ 1 / 24)

expThreeFourthPartialSumExact :
  expThreeFourthPartialSum ≡ + 131 / 8
expThreeFourthPartialSumExact = ℚRing.solve

sixteenBelowExpThreePartialSum :
  sixteenℚ ≤ expThreeFourthPartialSum
sixteenBelowExpThreePartialSum = ℚP.≤ᵇ⇒≤ tt

------------------------------------------------------------------------
-- Minimal real exponential/logarithm authority.  Positivity of the omitted
-- exponential series terms proves exp(3) is above the finite partial sum;
-- logarithm monotonicity then gives log(16) <= 3.
------------------------------------------------------------------------

record LogSixteenAnalyticAuthority (Scalar : Set) : Set₁ where
  field
    rational : ℚ → Scalar
    exponential logarithm : Scalar → Scalar
    LessEqual : Scalar → Scalar → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    rationalOrderEmbedding : ∀ {left right} →
      left ≤ right → LessEqual (rational left) (rational right)

    exponentialThreeAboveFourthPartialSum :
      LessEqual (rational expThreeFourthPartialSum)
        (exponential (rational threeℚ))

    logarithmMonotone : ∀ {left right} →
      LessEqual left right →
      LessEqual (logarithm left) (logarithm right)

    logarithmExponentialThree :
      logarithm (exponential (rational threeℚ)) ≡ rational threeℚ

open LogSixteenAnalyticAuthority public

logSixteenBelowThree :
  ∀ {Scalar} (dataSet : LogSixteenAnalyticAuthority Scalar) →
  LessEqual dataSet
    (logarithm dataSet (rational dataSet sixteenℚ))
    (rational dataSet threeℚ)
logSixteenBelowThree dataSet =
  subst
    (λ upper →
      LessEqual dataSet
        (logarithm dataSet (rational dataSet sixteenℚ)) upper)
    (logarithmExponentialThree dataSet)
    (logarithmMonotone dataSet
      (transitive dataSet
        (rationalOrderEmbedding dataSet sixteenBelowExpThreePartialSum)
        (exponentialThreeAboveFourthPartialSum dataSet)))

logSixteenFinitePartialSumArithmeticLevel : ProofLevel
logSixteenFinitePartialSumArithmeticLevel = machineChecked

logSixteenMonotoneReductionLevel : ProofLevel
logSixteenMonotoneReductionLevel = machineChecked

exponentialPositiveTailInputsLevel : ProofLevel
exponentialPositiveTailInputsLevel = conditional
