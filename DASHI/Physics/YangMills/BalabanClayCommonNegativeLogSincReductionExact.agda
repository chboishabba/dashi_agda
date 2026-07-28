module DASHI.Physics.YangMills.BalabanClayCommonNegativeLogSincReductionExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literature normalization.
--
-- Marc Daumas, David Lester and César Muñoz,
-- "Verified Real Number Calculations: A Library for Interval Arithmetic",
-- IEEE Transactions on Computers 58 (2009), 226--237.
-- DOI: 10.1109/TC.2008.213; arXiv:0708.3721
-- Relationship: interval decomposition of elementary-function bounds.
--
-- The only transcendental inequality used here is
--   -log(1-u) <= u/(1-u),  0 <= u < 1.
-- Everything else is order transport and rational arithmetic.
------------------------------------------------------------------------

oneFifth oneSixth oneTwentyFourth sixFifths : ℚ
oneFifth = + 1 / 5
oneSixth = + 1 / 6
oneTwentyFourth = + 1 / 24
sixFifths = + 6 / 5

sixFifthsTimesOneSixth :
  sixFifths * oneSixth ≡ oneFifth
sixFifthsTimesOneSixth = ℚRing.solve

record NegativeLogSincReductionData (Point Scalar : Set) : Set₁ where
  field
    zero one : Scalar
    add multiply subtract divide : Scalar → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    rational : ℚ → Scalar
    square sinc negativeLogSinc : Point → Scalar
    InConfiguredRadius : Point → Set

    u : Point → Scalar
    uDefinition : ∀ point →
      u point ≡ multiply (rational oneSixth) (square point)

    sincLowerByOneMinusU : ∀ point → InConfiguredRadius point →
      LessEqual (subtract one (u point)) (sinc point)

    negativeLogOrderReverse : ∀ {left right} →
      LessEqual left right →
      LessEqual (negativeLog right) (negativeLog left)
    negativeLog : Scalar → Scalar

    negativeLogSincDefinition : ∀ point →
      negativeLogSinc point ≡ negativeLog (sinc point)

    negativeLogOneMinusBound : ∀ point → InConfiguredRadius point →
      LessEqual
        (negativeLog (subtract one (u point)))
        (divide (u point) (subtract one (u point)))

    configuredRatioBound : ∀ point → InConfiguredRadius point →
      LessEqual
        (divide (u point) (subtract one (u point)))
        (multiply (rational sixFifths) (u point))

    scalarCoefficientNormalization : ∀ point →
      multiply (rational sixFifths)
        (multiply (rational oneSixth) (square point))
      ≡ multiply (rational oneFifth) (square point)

open NegativeLogSincReductionData public

negativeLogSincBelowOneFifthSquare :
  ∀ {Point Scalar}
    (dataSet : NegativeLogSincReductionData Point Scalar)
    point → InConfiguredRadius dataSet point →
  LessEqual dataSet
    (negativeLogSinc dataSet point)
    (multiply dataSet
      (rational dataSet oneFifth)
      (square dataSet point))
negativeLogSincBelowOneFifthSquare dataSet point inRadius =
  subst
    (λ upper →
      LessEqual dataSet (negativeLogSinc dataSet point) upper)
    (scalarCoefficientNormalization dataSet point)
    (subst
      (λ upper →
        LessEqual dataSet (negativeLogSinc dataSet point)
          (multiply dataSet (rational dataSet sixFifths) upper))
      (uDefinition dataSet point)
      (transitive dataSet
        (subst
          (λ lower →
            LessEqual dataSet lower
              (negativeLog dataSet
                (subtract dataSet (one dataSet) (u dataSet point))))
          (negativeLogSincDefinition dataSet point)
          (negativeLogOrderReverse dataSet
            (sincLowerByOneMinusU dataSet point inRadius)))
        (transitive dataSet
          (negativeLogOneMinusBound dataSet point inRadius)
          (configuredRatioBound dataSet point inRadius))))

negativeLogSincReductionLevel : ProofLevel
negativeLogSincReductionLevel = machineChecked

elementaryNegativeLogOneMinusInputsLevel : ProofLevel
elementaryNegativeLogOneMinusInputsLevel = conditional
