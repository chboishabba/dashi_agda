{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanFiniteRGExceptionalCovarianceMassExact where

------------------------------------------------------------------------
-- EXCEPTIONAL FIBRE COVARIANCE <= 2 * BAD MASS
--
-- Add only the positivity that a finite probability/reopening kernel actually
-- needs.  For pointwise-unit-bounded fine observables F,G:
--
--   |T F(c)|  <= 1
--   |T G(c)|  <= 1
--   |T(FG)(c)| <= 1
--
-- because kappa(c,.) is nonnegative and normalized.  Hence
--
--   |Cov(F,G | c)| <= 2.
--
-- Restricting the coarse expectation to any nonnegative bad-region mask chi
-- then gives
--
--   | E_coarse[ chi * Cov(F,G|C) ] |
--      <= 2 * E_coarse[chi].
--
-- Thus the exceptional covariance channel is reduced exactly to a bad-mass
-- estimate.  No fresh covariance theorem remains on that channel.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; ∣_∣; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteRGObservableReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanFiniteRGTotalCovarianceExact as Total
import DASHI.Physics.YangMills.BalabanFiniteRestrictedExpectationBoundExact as Restricted
import DASHI.Physics.YangMills.BalabanLiteralRationalSU2WilsonBoundedAlgebraExact as Bound

twoℚ : ℚ
twoℚ = 1ℚ + 1ℚ

record PositiveFiniteRGReopening
    {Fine Coarse : Set}
    (step : Reopen.FiniteRGReopeningStep Fine Coarse) : Set₁ where
  field
    coarseWeightNonnegative :
      ∀ coarse → 0ℚ ≤ Reopen.coarseWeight step coarse
    reopeningKernelNonnegative :
      ∀ coarse fine → 0ℚ ≤ Reopen.reopeningKernel step coarse fine

open PositiveFiniteRGReopening public

PointwiseUnitBounded :
  ∀ {State} → Reopen.Observable State → Set
PointwiseUnitBounded observable =
  ∀ state → ∣ observable state ∣ ≤ 1ℚ

oneNonnegative : 0ℚ ≤ 1ℚ
oneNonnegative = ℚP.0≤∣p∣ 1ℚ

twoNonnegative : 0ℚ ≤ twoℚ
twoNonnegative =
  ℚP.+-mono-≤ oneNonnegative oneNonnegative

transportObservableUnitBound :
  ∀ {Fine Coarse}
    {step : Reopen.FiniteRGReopeningStep Fine Coarse}
    (positive : PositiveFiniteRGReopening step)
    (observable : Reopen.Observable Fine) →
  PointwiseUnitBounded observable →
  ∀ coarse →
  ∣ Reopen.transportObservable step observable coarse ∣ ≤ 1ℚ
transportObservableUnitBound {step = step} positive observable bounded coarse =
  let
    raw :
      ∣ Reopen.transportObservable step observable coarse ∣
      ≤ 1ℚ
        * Restricted.restrictedMass
            (record
              { Restricted.FiniteRestrictedExpectationData.states =
                  Reopen.fineStates step
              ; Restricted.FiniteRestrictedExpectationData.weight =
                  Reopen.reopeningKernel step coarse
              ; Restricted.FiniteRestrictedExpectationData.mask =
                  λ _ → 1ℚ
              ; Restricted.FiniteRestrictedExpectationData.observable =
                  observable
              ; Restricted.FiniteRestrictedExpectationData.majorant = 1ℚ
              ; Restricted.FiniteRestrictedExpectationData.weightNonnegative =
                  reopeningKernelNonnegative positive coarse
              ; Restricted.FiniteRestrictedExpectationData.maskNonnegative =
                  λ _ → oneNonnegative
              ; Restricted.FiniteRestrictedExpectationData.observableBounded =
                  bounded
              ; Restricted.FiniteRestrictedExpectationData.majorantNonnegative =
                  oneNonnegative
              })
    raw =
      Restricted.restrictedExpectationBelowMass
        (record
          { Restricted.FiniteRestrictedExpectationData.states =
              Reopen.fineStates step
          ; Restricted.FiniteRestrictedExpectationData.weight =
              Reopen.reopeningKernel step coarse
          ; Restricted.FiniteRestrictedExpectationData.mask =
              λ _ → 1ℚ
          ; Restricted.FiniteRestrictedExpectationData.observable =
              observable
          ; Restricted.FiniteRestrictedExpectationData.majorant = 1ℚ
          ; Restricted.FiniteRestrictedExpectationData.weightNonnegative =
              reopeningKernelNonnegative positive coarse
          ; Restricted.FiniteRestrictedExpectationData.maskNonnegative =
              λ _ → oneNonnegative
          ; Restricted.FiniteRestrictedExpectationData.observableBounded =
              bounded
          ; Restricted.FiniteRestrictedExpectationData.majorantNonnegative =
              oneNonnegative
          })

    massIsOne :
      Restricted.restrictedMass
        (record
          { Restricted.FiniteRestrictedExpectationData.states =
              Reopen.fineStates step
          ; Restricted.FiniteRestrictedExpectationData.weight =
              Reopen.reopeningKernel step coarse
          ; Restricted.FiniteRestrictedExpectationData.mask =
              λ _ → 1ℚ
          ; Restricted.FiniteRestrictedExpectationData.observable =
              observable
          ; Restricted.FiniteRestrictedExpectationData.majorant = 1ℚ
          ; Restricted.FiniteRestrictedExpectationData.weightNonnegative =
              reopeningKernelNonnegative positive coarse
          ; Restricted.FiniteRestrictedExpectationData.maskNonnegative =
              λ _ → oneNonnegative
          ; Restricted.FiniteRestrictedExpectationData.observableBounded =
              bounded
          ; Restricted.FiniteRestrictedExpectationData.majorantNonnegative =
              oneNonnegative
          })
      ≡ 1ℚ
    massIsOne =
      trans
        (Reopen.Sums.sumRationalCong
          (Reopen.fineStates step)
          (λ fine → Reopen.reopeningKernel step coarse fine * 1ℚ)
          (Reopen.reopeningKernel step coarse)
          (λ fine → ℚP.*-identityʳ (Reopen.reopeningKernel step coarse fine)))
        (Reopen.reopeningNormalized step coarse)
  in
  subst
    (λ upper →
      ∣ Reopen.transportObservable step observable coarse ∣ ≤ upper)
    (trans
      (cong (1ℚ *_) massIsOne)
      (ℚP.*-identityˡ 1ℚ))
    raw
  where
  cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
  cong f refl = refl

productPointwiseUnitBounded :
  ∀ {State} (left right : Reopen.Observable State) →
  PointwiseUnitBounded left →
  PointwiseUnitBounded right →
  PointwiseUnitBounded (λ state → left state * right state)
productPointwiseUnitBounded left right leftBounded rightBounded state =
  subst
    (_≤ 1ℚ)
    (ℚP.*-identityʳ 1ℚ)
    (Bound.absoluteProductBound
      (leftBounded state)
      (rightBounded state)
      oneNonnegative
      oneNonnegative)

conditionalCovarianceTwoBound :
  ∀ {Fine Coarse}
    {step : Reopen.FiniteRGReopeningStep Fine Coarse}
    (positive : PositiveFiniteRGReopening step)
    (left right : Reopen.Observable Fine) →
  PointwiseUnitBounded left →
  PointwiseUnitBounded right →
  ∀ coarse →
  ∣ Total.conditionalCovariance step left right coarse ∣ ≤ twoℚ
conditionalCovarianceTwoBound {step = step} positive left right
    leftBounded rightBounded coarse =
  let
    productBound =
      transportObservableUnitBound positive
        (λ fine → left fine * right fine)
        (productPointwiseUnitBounded left right leftBounded rightBounded)
        coarse

    leftBound =
      transportObservableUnitBound positive left leftBounded coarse
    rightBound =
      transportObservableUnitBound positive right rightBounded coarse

    meanProductBound :
      ∣ Reopen.transportObservable step left coarse
          * Reopen.transportObservable step right coarse ∣ ≤ 1ℚ
    meanProductBound =
      subst
        (_≤ 1ℚ)
        (ℚP.*-identityʳ 1ℚ)
        (Bound.absoluteProductBound
          leftBound rightBound oneNonnegative oneNonnegative)

    triangle =
      ℚP.∣p-q∣≤∣p∣+∣q∣
        (Reopen.transportComposite step left right coarse)
        (Reopen.transportObservable step left coarse
          * Reopen.transportObservable step right coarse)
  in
  ℚP.≤-trans triangle
    (ℚP.+-mono-≤ productBound meanProductBound)

record ExceptionalCovarianceMask
    {Fine Coarse : Set}
    (step : Reopen.FiniteRGReopeningStep Fine Coarse) : Set₁ where
  field
    mask : Coarse → ℚ
    maskNonnegative : ∀ coarse → 0ℚ ≤ mask coarse

open ExceptionalCovarianceMask public

exceptionalMass :
  ∀ {Fine Coarse}
    {step : Reopen.FiniteRGReopeningStep Fine Coarse} →
  ExceptionalCovarianceMask step → ℚ
exceptionalMass {step = step} bad =
  Reopen.Sums.sumRational (Reopen.coarseStates step)
    (λ coarse → Reopen.coarseWeight step coarse * mask bad coarse)

exceptionalCovarianceContribution :
  ∀ {Fine Coarse}
    {step : Reopen.FiniteRGReopeningStep Fine Coarse} →
  ExceptionalCovarianceMask step →
  Reopen.Observable Fine → Reopen.Observable Fine → ℚ
exceptionalCovarianceContribution {step = step} bad left right =
  Reopen.Sums.sumRational (Reopen.coarseStates step)
    (λ coarse →
      (Reopen.coarseWeight step coarse * mask bad coarse)
        * Total.conditionalCovariance step left right coarse)

exceptionalCovarianceBelowTwiceMass :
  ∀ {Fine Coarse}
    {step : Reopen.FiniteRGReopeningStep Fine Coarse}
    (positive : PositiveFiniteRGReopening step)
    (bad : ExceptionalCovarianceMask step)
    (left right : Reopen.Observable Fine) →
  PointwiseUnitBounded left →
  PointwiseUnitBounded right →
  ∣ exceptionalCovarianceContribution bad left right ∣
  ≤ twoℚ * exceptionalMass bad
exceptionalCovarianceBelowTwiceMass {step = step}
    positive bad left right leftBounded rightBounded =
  Restricted.restrictedExpectationBelowMass
    (record
      { Restricted.FiniteRestrictedExpectationData.states =
          Reopen.coarseStates step
      ; Restricted.FiniteRestrictedExpectationData.weight =
          Reopen.coarseWeight step
      ; Restricted.FiniteRestrictedExpectationData.mask =
          mask bad
      ; Restricted.FiniteRestrictedExpectationData.observable =
          Total.conditionalCovariance step left right
      ; Restricted.FiniteRestrictedExpectationData.majorant =
          twoℚ
      ; Restricted.FiniteRestrictedExpectationData.weightNonnegative =
          coarseWeightNonnegative positive
      ; Restricted.FiniteRestrictedExpectationData.maskNonnegative =
          maskNonnegative bad
      ; Restricted.FiniteRestrictedExpectationData.observableBounded =
          conditionalCovarianceTwoBound
            positive left right leftBounded rightBounded
      ; Restricted.FiniteRestrictedExpectationData.majorantNonnegative =
          twoNonnegative
      })

finiteRGConditionalCovarianceTwoBoundLevel : ProofLevel
finiteRGConditionalCovarianceTwoBoundLevel = machineChecked

exceptionalCovarianceToBadMassCompilerLevel : ProofLevel
exceptionalCovarianceToBadMassCompilerLevel = machineChecked
