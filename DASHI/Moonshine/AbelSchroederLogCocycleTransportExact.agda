{-# OPTIONS --safe #-}
module DASHI.Moonshine.AbelSchroederLogCocycleTransportExact where

-- Exact logarithmic cocycle compiler from a Schroeder chart.
-- No holomorphic linearization or logarithm branch is postulated as solved:
-- these are explicitly supplied by the caller.
-- The additive chart may be complex, p-adic, hypercomplex or another
-- typed fibre; no unspoken division by a complex multiplier occurs.

open import Agda.Primitive using (Set; Set₁)
open import Agda.Builtin.Equality using (_≡_; refl)

private
  variable A B : Set

cong : (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

record SelectedSchroederLogChart : Set₁ where
  field
    Point : Set
    Multiplied : Set
    LogValue : Set
    AbelValue : Set
    step : Point → Point
    linearizing : Point → Multiplied
    multiplyByMultiplier : Multiplied → Multiplied
    schroederEquation : (x : Point) →
      linearizing (step x) ≡
      multiplyByMultiplier (linearizing x)

    -- A selected, single-valued logarithm branch on the chosen orbit domain.
    logarithm : Multiplied → LogValue
    addMultiplierLog : LogValue → LogValue
    logarithmCocycle : (u : Multiplied) →
      logarithm (multiplyByMultiplier u) ≡
      addMultiplierLog (logarithm u)

    -- Scaling by the selected nonzero log-multiplier, with its exact
    -- normalization law; no division field structure is smuggled in.
    normalizeLog : LogValue → AbelValue
    successor : AbelValue → AbelValue
    normalizationCommutes : (v : LogValue) →
      normalizeLog (addMultiplierLog v) ≡
      successor (normalizeLog v)

open SelectedSchroederLogChart public

originalLogMultiplierBranchAndCocycle :
  (C : SelectedSchroederLogChart) →
  (x : Point C) →
  logarithm C (linearizing C (step C x)) ≡
  addMultiplierLog C (logarithm C (linearizing C x))
originalLogMultiplierBranchAndCocycle C x =
  trans
    (cong (logarithm C) (schroederEquation C x))
    (logarithmCocycle C (linearizing C x))

constructedAbel : (C : SelectedSchroederLogChart) →
  Point C → AbelValue C
constructedAbel C x = normalizeLog C (logarithm C (linearizing C x))

originalSelectedAbelSemiconjugacy :
  (C : SelectedSchroederLogChart) →
  (x : Point C) →
  constructedAbel C (step C x) ≡ successor C (constructedAbel C x)
originalSelectedAbelSemiconjugacy C x =
  trans
    (cong (normalizeLog C)
      (originalLogMultiplierBranchAndCocycle C x))
    (normalizationCommutes C (logarithm C (linearizing C x)))

-- Stronger, branch-aware version: a winding correction may be nonzero.
-- To get the ordinary Abel equation, its normalized image must vanish,
-- which is exactly the certificate the caller must supply.

record WindingSchroederChart : Set₁ where
  field
    Point : Set
    LogValue : Set
    AbelValue : Set
    step : Point → Point
    chosenLog : Point → LogValue
    shift : LogValue → LogValue
    windingCorrect : Point → LogValue
    branchEquation : (x : Point) →
      chosenLog (step x) ≡ windingCorrect x
    normalize : LogValue → AbelValue
    successor : AbelValue → AbelValue
    normalizedBranch : (x : Point) →
      normalize (windingCorrect x) ≡
      successor (normalize (chosenLog x))

open WindingSchroederChart public

windingCorrectedAbel :
  (C : WindingSchroederChart) →
  (x : Point C) →
  normalize C (chosenLog C (step C x)) ≡
  successor C (normalize C (chosenLog C x))
windingCorrectedAbel C x =
  trans (cong (normalize C) (branchEquation C x))
        (normalizedBranch C x)
