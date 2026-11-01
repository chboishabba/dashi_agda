module DASHI.Physics.Closure.NSTriadKNSelectedPairEnergySquareRound453Exact where

------------------------------------------------------------------------
-- ROUND453 / R109 SPECIALIZATION: SELECTED ENERGY PAIRS ARE PAID BY E^2
--
-- R109's generic selected kernel is
--
--   D_i E_j + E_i D_j.
--
-- Set D=E.  The kernel is exactly 2 E_i E_j and the full selected sum is
-- bounded by 2 (sum E)^2.  Over the rational carrier, cancellation of the
-- positive factor two gives
--
--   sum_selected E_i E_j <= (sum E)^2.
--
-- The selector is arbitrary.  Fixed-output resonance, cutoff and any further
-- physical admissibility may therefore be encoded without a mode-count factor.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; subst; trans)

import DASHI.Physics.Closure.NSTriadKNSelectedPairEnergyDissipationProductRound109Exact as R109

record ModalEnergy {a : Level} (Mode : Set a) : Set a where
  constructor modal-energy
  field
    energy : Mode → ℚ
    energyNonnegative : (mode : Mode) → 0ℚ ≤ energy mode

open ModalEnergy public

asEqualED :
  ∀ {a} {Mode : Set a} →
  ModalEnergy Mode → R109.ModalEnergyDissipation Mode
asEqualED E = R109.modal-energy-dissipation
  (energy E)
  (energy E)
  (energyNonnegative E)
  (energyNonnegative E)

selectedEnergyInner :
  ∀ {a} {Mode : Set a} →
  ModalEnergy Mode →
  (Mode → Mode → Bool) → Mode → List Mode → ℚ
selectedEnergyInner E select left [] = 0ℚ
selectedEnergyInner E select left (right ∷ rest) with select left right
... | true = energy E left * energy E right
    + selectedEnergyInner E select left rest
... | false = selectedEnergyInner E select left rest

selectedEnergyPairSum :
  ∀ {a} {Mode : Set a} →
  ModalEnergy Mode →
  (Mode → Mode → Bool) → List Mode → List Mode → ℚ
selectedEnergyPairSum E select [] rights = 0ℚ
selectedEnergyPairSum E select (left ∷ rest) rights =
  selectedEnergyInner E select left rights
  + selectedEnergyPairSum E select rest rights

sumEnergy :
  ∀ {a} {Mode : Set a} → ModalEnergy Mode → List Mode → ℚ
sumEnergy E = R109.sumBy (energy E)

two : ℚ
two = 1ℚ + 1ℚ

selectedInnerDoubles :
  ∀ {a} {Mode : Set a}
    (E : ModalEnergy Mode)
    (select : Mode → Mode → Bool)
    (left : Mode) (rights : List Mode) →
  R109.selectedInner (asEqualED E) select left rights
  ≡ two * selectedEnergyInner E select left rights
selectedInnerDoubles E select left [] = solve []
selectedInnerDoubles E select left (right ∷ rest) with select left right
... | true =
  trans
    (cong₂ _+_ refl (selectedInnerDoubles E select left rest))
    (solve
      ( energy E left ∷ energy E right
      ∷ selectedEnergyInner E select left rest ∷ []))
... | false = selectedInnerDoubles E select left rest

selectedPairSumDoubles :
  ∀ {a} {Mode : Set a}
    (E : ModalEnergy Mode)
    (select : Mode → Mode → Bool)
    (lefts rights : List Mode) →
  R109.selectedOrderedPairSum (asEqualED E) select lefts rights
  ≡ two * selectedEnergyPairSum E select lefts rights
selectedPairSumDoubles E select [] rights = solve []
selectedPairSumDoubles E select (left ∷ rest) rights =
  trans
    (cong₂ _+_
      (selectedInnerDoubles E select left rights)
      (selectedPairSumDoubles E select rest rights))
    (solve
      ( selectedEnergyInner E select left rights
      ∷ selectedEnergyPairSum E select rest rights ∷ []))

sumEnergyMeaning :
  ∀ {a} {Mode : Set a}
    (E : ModalEnergy Mode) (modes : List Mode) →
  R109.sumEnergy (asEqualED E) modes ≡ sumEnergy E modes
sumEnergyMeaning E modes = refl

sumDissipationMeaning :
  ∀ {a} {Mode : Set a}
    (E : ModalEnergy Mode) (modes : List Mode) →
  R109.sumDissipation (asEqualED E) modes ≡ sumEnergy E modes
sumDissipationMeaning E modes = refl

selectedEnergyPairSumBound :
  ∀ {a} {Mode : Set a}
    (E : ModalEnergy Mode)
    (select : Mode → Mode → Bool)
    (modes : List Mode) →
  selectedEnergyPairSum E select modes modes
  ≤ sumEnergy E modes * sumEnergy E modes
selectedEnergyPairSumBound E select modes =
  let
    source = R109.selectedPairEnergyDissipationProductBound
      (asEqualED E) select modes

    doubledSource :
      two * selectedEnergyPairSum E select modes modes
      ≤ two * (sumEnergy E modes * sumEnergy E modes)
    doubledSource =
      subst
        (λ lower → lower ≤ two * (sumEnergy E modes * sumEnergy E modes))
        (selectedPairSumDoubles E select modes modes)
        (subst
          (λ upper →
            R109.selectedOrderedPairSum (asEqualED E) select modes modes ≤ upper)
          (solve (sumEnergy E modes ∷ []))
          source)

    twoPositive : 0ℚ < two
    twoPositive =
      ℚP.+-mono-<-< (ℚP.positive⁻¹ 1ℚ) (ℚP.positive⁻¹ 1ℚ)
  in
  ℚP.*-cancelˡ-≤-pos two doubledSource

round453SelectedEnergyPairSquareBoundClosed : Bool
round453SelectedEnergyPairSquareBoundClosed = true

round453ReusesR109SelectorCompiler : Bool
round453ReusesR109SelectorCompiler = true

round453IntroducesCardinalityTax : Bool
round453IntroducesCardinalityTax = false

round453PackageAClosed : Bool
round453PackageAClosed = false

round453ClayPromotion : Bool
round453ClayPromotion = false

round453IntroducesCardinalityTaxIsFalse :
  round453IntroducesCardinalityTax ≡ false
round453IntroducesCardinalityTaxIsFalse = refl
