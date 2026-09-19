{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanFiniteRestrictedExpectationBoundExact where

------------------------------------------------------------------------
-- FINITE BAD-REGION INTEGRATION LEMMA
--
-- This is the exact algebra needed after the large-field/Boltzmann machinery
-- has produced a suppressed nonnegative mass.  For a finite weighted measure,
-- a mask 0 <= chi <= 1 and an observable |F| <= M,
--
--   | sum_x w(x) chi(x) F(x) |
--      <= M sum_x w(x) chi(x).
--
-- No probability semantics are assumed: normalization is not needed.  The
-- theorem is therefore reusable directly inside a finite RG reopening fibre.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; ∣_∣; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums

multiplyNonnegative :
  ∀ {left right : ℚ} →
  0ℚ ≤ left → 0ℚ ≤ right → 0ℚ ≤ left * right
multiplyNonnegative {left} {right} leftNN rightNN =
  let
    instance
      leftNonnegative : NonNegative left
      leftNonnegative = nonNegative leftNN

      rightNonnegative : NonNegative right
      rightNonnegative = nonNegative rightNN

      productNonnegative : NonNegative (left * right)
      productNonnegative = ℚP.nonNeg*nonNeg⇒nonNeg left right
  in
  ℚP.nonNegative⁻¹ (left * right)

scaleBound :
  ∀ {coefficient value majorant : ℚ} →
  0ℚ ≤ coefficient →
  ∣ value ∣ ≤ majorant →
  coefficient * ∣ value ∣ ≤ coefficient * majorant
scaleBound {coefficient} coefficientNN bound =
  let
    instance
      coefficientNonnegative : NonNegative coefficient
      coefficientNonnegative = nonNegative coefficientNN
  in
  ℚP.*-monoˡ-≤-nonNeg coefficient bound

record FiniteRestrictedExpectationData (State : Set) : Set₁ where
  field
    states : List State
    weight mask observable : State → ℚ
    majorant : ℚ

    weightNonnegative : ∀ state → 0ℚ ≤ weight state
    maskNonnegative : ∀ state → 0ℚ ≤ mask state
    observableBounded : ∀ state → ∣ observable state ∣ ≤ majorant
    majorantNonnegative : 0ℚ ≤ majorant

open FiniteRestrictedExpectationData public

restrictedMass :
  ∀ {State} → FiniteRestrictedExpectationData State → ℚ
restrictedMass dataSet =
  Sums.sumRational (states dataSet)
    (λ state → weight dataSet state * mask dataSet state)

restrictedExpectation :
  ∀ {State} → FiniteRestrictedExpectationData State → ℚ
restrictedExpectation dataSet =
  Sums.sumRational (states dataSet)
    (λ state →
      (weight dataSet state * mask dataSet state)
        * observable dataSet state)

sumAbsoluteBelowMajorant :
  ∀ {State}
    (values : List State)
    (coefficient observable : State → ℚ)
    (majorant : ℚ) →
  (∀ state → 0ℚ ≤ coefficient state) →
  (∀ state → ∣ observable state ∣ ≤ majorant) →
  ∣ Sums.sumRational values
      (λ state → coefficient state * observable state) ∣
  ≤ majorant * Sums.sumRational values coefficient
sumAbsoluteBelowMajorant [] coefficient observable majorant coefficientNN bounded =
  subst
    (λ right → 0ℚ ≤ right)
    (sym (ℚP.*-zeroʳ majorant))
    ℚP.≤-refl
sumAbsoluteBelowMajorant
    (state ∷ values) coefficient observable majorant coefficientNN bounded =
  let
    headAbs :
      ∣ coefficient state * observable state ∣
      ≤ majorant * coefficient state
    headAbs =
      subst
        (λ upper →
          ∣ coefficient state * observable state ∣ ≤ upper)
        (ℚP.*-comm majorant (coefficient state))
        (subst
          (λ lower →
            lower ≤ coefficient state * majorant)
          (ℚP.∣p*q∣≡∣p∣*∣q∣
            (coefficient state) (observable state))
          (scaleBound
            (coefficientNN state)
            (bounded state)))

    tailAbs :
      ∣ Sums.sumRational values
          (λ selected → coefficient selected * observable selected) ∣
      ≤ majorant * Sums.sumRational values coefficient
    tailAbs =
      sumAbsoluteBelowMajorant
        values coefficient observable majorant coefficientNN bounded

    triangle =
      ℚP.∣p+q∣≤∣p∣+∣q∣
        (coefficient state * observable state)
        (Sums.sumRational values
          (λ selected → coefficient selected * observable selected))

    summed =
      ℚP.+-mono-≤ headAbs tailAbs

    factor :
      majorant * coefficient state
        + majorant * Sums.sumRational values coefficient
      ≡ majorant
        * (coefficient state + Sums.sumRational values coefficient)
    factor = ℚRing.solve-∀
      majorant (coefficient state) (Sums.sumRational values coefficient)
  in
  ℚP.≤-trans triangle
    (subst
      (λ upper →
        ∣ coefficient state * observable state ∣
        + ∣ Sums.sumRational values
            (λ selected → coefficient selected * observable selected) ∣
        ≤ upper)
      factor
      summed)

restrictedExpectationBelowMass :
  ∀ {State} (dataSet : FiniteRestrictedExpectationData State) →
  ∣ restrictedExpectation dataSet ∣
  ≤ majorant dataSet * restrictedMass dataSet
restrictedExpectationBelowMass dataSet =
  sumAbsoluteBelowMajorant
    (states dataSet)
    (λ state → weight dataSet state * mask dataSet state)
    (observable dataSet)
    (majorant dataSet)
    (λ state →
      multiplyNonnegative
        (weightNonnegative dataSet state)
        (maskNonnegative dataSet state))
    (observableBounded dataSet)

unitBoundedRestrictedExpectationBelowMass :
  ∀ {State} (dataSet : FiniteRestrictedExpectationData State) →
  majorant dataSet ℚ.≡ ℚ.1ℚ →
  ∣ restrictedExpectation dataSet ∣ ≤ restrictedMass dataSet
unitBoundedRestrictedExpectationBelowMass dataSet refl =
  subst
    (λ right → ∣ restrictedExpectation dataSet ∣ ≤ right)
    (ℚP.*-identityˡ (restrictedMass dataSet))
    (restrictedExpectationBelowMass dataSet)

finiteRestrictedExpectationBoundLevel : ProofLevel
finiteRestrictedExpectationBoundLevel = machineChecked
