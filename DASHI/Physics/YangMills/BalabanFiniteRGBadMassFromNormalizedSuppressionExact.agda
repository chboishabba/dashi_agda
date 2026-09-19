{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanFiniteRGBadMassFromNormalizedSuppressionExact where

------------------------------------------------------------------------
-- NORMALIZED POINTWISE SUPPRESSION -> BAD MASS SUPPRESSION
--
-- On a finite rational carrier, suppose a nonnegative bad-region density b
-- is pointwise dominated by a fixed suppression factor s times a nonnegative
-- normalized reference density r:
--
--   0 <= b(x) <= s r(x),    sum_x r(x) = 1.
--
-- Then
--
--   sum_x b(x) <= s.
--
-- This is the exact integration step needed between the Gate4 pointwise
-- Wilson/Boltzmann suppression machinery and the finite-RG exceptional
-- covariance theorem.  It introduces no probability or source authority.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteRGExceptionalCovarianceMassExact as Exceptional

sumRationalMono :
  ∀ {State : Set}
    (states : List State)
    (left right : State → ℚ) →
  (∀ state → left state ≤ right state) →
  Sums.sumRational states left ≤ Sums.sumRational states right
sumRationalMono [] left right pointwise = ℚP.≤-refl
sumRationalMono (state ∷ states) left right pointwise =
  ℚP.+-mono-≤
    (pointwise state)
    (sumRationalMono states left right pointwise)

record NormalizedSuppressedBadMassData (State : Set) : Set₁ where
  field
    states : List State
    badWeight referenceWeight : State → ℚ
    suppression : ℚ

    badWeightNonnegative : ∀ state → 0ℚ ≤ badWeight state
    referenceWeightNonnegative : ∀ state → 0ℚ ≤ referenceWeight state
    suppressionNonnegative : 0ℚ ≤ suppression

    pointwiseSuppression : ∀ state →
      badWeight state ≤ suppression * referenceWeight state

    referenceNormalized :
      Sums.sumRational states referenceWeight ≡ 1ℚ

open NormalizedSuppressedBadMassData public

badMass :
  ∀ {State} → NormalizedSuppressedBadMassData State → ℚ
badMass dataSet =
  Sums.sumRational (states dataSet) (badWeight dataSet)

badMassBelowSuppression :
  ∀ {State} (dataSet : NormalizedSuppressedBadMassData State) →
  badMass dataSet ≤ suppression dataSet
badMassBelowSuppression dataSet =
  let
    pointwise :
      badMass dataSet
      ≤ Sums.sumRational (states dataSet)
          (λ state → suppression dataSet * referenceWeight dataSet state)
    pointwise =
      sumRationalMono
        (states dataSet)
        (badWeight dataSet)
        (λ state → suppression dataSet * referenceWeight dataSet state)
        (pointwiseSuppression dataSet)

    factor :
      Sums.sumRational (states dataSet)
        (λ state → suppression dataSet * referenceWeight dataSet state)
      ≡ suppression dataSet
    factor =
      trans
        (Sums.sumRationalScale
          (suppression dataSet)
          (states dataSet)
          (referenceWeight dataSet))
        (trans
          (cong (suppression dataSet *_) (referenceNormalized dataSet))
          (ℚP.*-identityʳ (suppression dataSet)))
  in
  subst
    (λ upper → badMass dataSet ≤ upper)
    factor
    pointwise

------------------------------------------------------------------------
-- Direct exceptional-covariance consequence.
------------------------------------------------------------------------

record ExceptionalBadMassAttachment
    {Fine Coarse : Set}
    {step : DASHI.Physics.YangMills.BalabanFiniteRGObservableReopeningExact.FiniteRGReopeningStep Fine Coarse}
    (bad : Exceptional.ExceptionalCovarianceMask step) : Set₁ where
  field
    badMassData : NormalizedSuppressedBadMassData Coarse

    sameBadMass :
      Exceptional.exceptionalMass bad
      ≡ badMass badMassData

open ExceptionalBadMassAttachment public

exceptionalMassBelowSuppression :
  ∀ {Fine Coarse step bad}
    (attachment : ExceptionalBadMassAttachment {Fine} {Coarse} {step} bad) →
  Exceptional.exceptionalMass bad
  ≤ suppression (badMassData attachment)
exceptionalMassBelowSuppression attachment =
  subst
    (λ lower →
      lower ≤ suppression (badMassData attachment))
    (sym (sameBadMass attachment))
    (badMassBelowSuppression (badMassData attachment))

twoTimesMono :
  ∀ {left right : ℚ} →
  left ≤ right →
  Exceptional.twoℚ * left ≤ Exceptional.twoℚ * right
twoTimesMono bound =
  let
    instance
      twoNonnegative : NonNegative Exceptional.twoℚ
      twoNonnegative = nonNegative Exceptional.twoNonnegative
  in
  ℚP.*-monoˡ-≤-nonNeg Exceptional.twoℚ bound

exceptionalCovarianceBelowTwiceSuppression :
  ∀ {Fine Coarse}
    {step : DASHI.Physics.YangMills.BalabanFiniteRGObservableReopeningExact.FiniteRGReopeningStep Fine Coarse}
    (positive : Exceptional.PositiveFiniteRGReopening step)
    (bad : Exceptional.ExceptionalCovarianceMask step)
    (attachment : ExceptionalBadMassAttachment bad)
    (left right : DASHI.Physics.YangMills.BalabanFiniteRGObservableReopeningExact.Observable Fine) →
  Exceptional.PointwiseUnitBounded left →
  Exceptional.PointwiseUnitBounded right →
  ∣ Exceptional.exceptionalCovarianceContribution bad left right ∣
  ≤ Exceptional.twoℚ * suppression (badMassData attachment)
exceptionalCovarianceBelowTwiceSuppression
    positive bad attachment left right leftBounded rightBounded =
  ℚP.≤-trans
    (Exceptional.exceptionalCovarianceBelowTwiceMass
      positive bad left right leftBounded rightBounded)
    (twoTimesMono (exceptionalMassBelowSuppression attachment))

finiteNormalizedBadMassSuppressionLevel : ProofLevel
finiteNormalizedBadMassSuppressionLevel = machineChecked

exceptionalCovarianceSuppressionCompilerLevel : ProofLevel
exceptionalCovarianceSuppressionCompilerLevel = machineChecked
