module DASHI.Physics.Closure.NSTriadKNSelectedPairEnergyDissipationProductRound109Exact where

------------------------------------------------------------------------
-- ROUND109 / SELECTED-PAIR ENERGY-DISSIPATION PRODUCT
--
-- Let a finite mode family carry nonnegative modal energy E_i and modal
-- dissipation D_i.  For ANY Boolean selector chi(i,j), the selected ordered
-- pair kernel
--
--   K(i,j) = D_i E_j + E_i D_j
--
-- satisfies exactly
--
--   sum_{chi(i,j)} K(i,j)
--     <= 2 (sum_i E_i) (sum_i D_i).
--
-- No cardinality factor appears.  This is the finite summation mechanism needed
-- by the Round109 self-phase route once a literal triad contribution is reduced
-- termwise to the modal energy-dissipation kernel.  Resonance, helicity and
-- shell selection may all be encoded in `chi`; throwing away pairs can only
-- decrease the nonnegative kernel sum.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

record ModalEnergyDissipation {a : Level} (Mode : Set a) : Set a where
  constructor modal-energy-dissipation
  field
    energy dissipation : Mode → ℚ
    energyNonnegative : (mode : Mode) → 0ℚ ≤ energy mode
    dissipationNonnegative : (mode : Mode) → 0ℚ ≤ dissipation mode

open ModalEnergyDissipation public

sumBy : ∀ {a} {Mode : Set a} → (Mode → ℚ) → List Mode → ℚ
sumBy f [] = 0ℚ
sumBy f (x ∷ xs) = f x + sumBy f xs

pairKernel :
  ∀ {a} {Mode : Set a} →
  ModalEnergyDissipation Mode → Mode → Mode → ℚ
pairKernel M left right =
  dissipation M left * energy M right
  + energy M left * dissipation M right

pairKernelNonnegative :
  ∀ {a} {Mode : Set a}
    (M : ModalEnergyDissipation Mode) left right →
  0ℚ ≤ pairKernel M left right
pairKernelNonnegative M left right =
  ℚP.+-mono-≤
    (let
      instance
        dNN = Data.Rational.Base.nonNegative (dissipationNonnegative M left)
        eNN = Data.Rational.Base.nonNegative (energyNonnegative M right)
      in ℚP.nonNegative⁻¹ (dissipation M left * energy M right))
    (let
      instance
        eNN = Data.Rational.Base.nonNegative (energyNonnegative M left)
        dNN = Data.Rational.Base.nonNegative (dissipationNonnegative M right)
      in ℚP.nonNegative⁻¹ (energy M left * dissipation M right))

selectedInner :
  ∀ {a} {Mode : Set a} →
  ModalEnergyDissipation Mode →
  (Mode → Mode → Bool) → Mode → List Mode → ℚ
selectedInner M select left [] = 0ℚ
selectedInner M select left (right ∷ rest) with select left right
... | true = pairKernel M left right + selectedInner M select left rest
... | false = selectedInner M select left rest

fullInner :
  ∀ {a} {Mode : Set a} →
  ModalEnergyDissipation Mode → Mode → List Mode → ℚ
fullInner M left [] = 0ℚ
fullInner M left (right ∷ rest) = pairKernel M left right + fullInner M left rest

selectedInnerBelowFull :
  ∀ {a} {Mode : Set a}
    (M : ModalEnergyDissipation Mode)
    (select : Mode → Mode → Bool)
    (left : Mode) (rights : List Mode) →
  selectedInner M select left rights ≤ fullInner M left rights
selectedInnerBelowFull M select left [] = ℚP.≤-refl
selectedInnerBelowFull M select left (right ∷ rest) with select left right
... | true =
  ℚP.+-mono-≤ ℚP.≤-refl
    (selectedInnerBelowFull M select left rest)
... | false =
  let
    kernelNN = pairKernelNonnegative M left right
    tail = selectedInnerBelowFull M select left rest
    addKernel :
      selectedInner M select left rest
      ≤ pairKernel M left right + fullInner M left rest
    addKernel =
      ℚP.≤-trans tail
        (subst
          (λ lower → lower ≤ pairKernel M left right + fullInner M left rest)
          (ℚP.+-identityˡ (fullInner M left rest))
          (ℚP.+-mono-≤ kernelNN ℚP.≤-refl))
  in addKernel

selectedPairSum :
  ∀ {a} {Mode : Set a} →
  ModalEnergyDissipation Mode →
  (Mode → Mode → Bool) → List Mode → ℚ
selectedPairSum M select [] = 0ℚ
selectedPairSum M select (left ∷ rest) =
  selectedInner M select left (left ∷ rest)
  + selectedPairSum M select rest

-- The useful physical fold needs all ordered pairs, not only the triangular
-- suffix used above.  Keep a fixed complete `all` list while folding lefts.
selectedOrderedPairSum :
  ∀ {a} {Mode : Set a} →
  ModalEnergyDissipation Mode →
  (Mode → Mode → Bool) → List Mode → List Mode → ℚ
selectedOrderedPairSum M select [] all = 0ℚ
selectedOrderedPairSum M select (left ∷ lefts) all =
  selectedInner M select left all
  + selectedOrderedPairSum M select lefts all

fullOrderedPairSum :
  ∀ {a} {Mode : Set a} →
  ModalEnergyDissipation Mode → List Mode → List Mode → ℚ
fullOrderedPairSum M [] all = 0ℚ
fullOrderedPairSum M (left ∷ lefts) all =
  fullInner M left all + fullOrderedPairSum M lefts all

selectedOrderedPairSumBelowFull :
  ∀ {a} {Mode : Set a}
    (M : ModalEnergyDissipation Mode)
    (select : Mode → Mode → Bool)
    (lefts rights : List Mode) →
  selectedOrderedPairSum M select lefts rights
  ≤ fullOrderedPairSum M lefts rights
selectedOrderedPairSumBelowFull M select [] rights = ℚP.≤-refl
selectedOrderedPairSumBelowFull M select (left ∷ lefts) rights =
  ℚP.+-mono-≤
    (selectedInnerBelowFull M select left rights)
    (selectedOrderedPairSumBelowFull M select lefts rights)

sumEnergy sumDissipation :
  ∀ {a} {Mode : Set a} →
  ModalEnergyDissipation Mode → List Mode → ℚ
sumEnergy M = sumBy (energy M)
sumDissipation M = sumBy (dissipation M)

fullInnerFactorization :
  ∀ {a} {Mode : Set a}
    (M : ModalEnergyDissipation Mode)
    (left : Mode) (rights : List Mode) →
  fullInner M left rights
  ≡ dissipation M left * sumEnergy M rights
      + energy M left * sumDissipation M rights
fullInnerFactorization M left []
  rewrite ℚP.*-zeroʳ (dissipation M left)
        | ℚP.*-zeroʳ (energy M left)
        | ℚP.+-identityʳ 0ℚ = refl
fullInnerFactorization M left (right ∷ rest) =
  trans
    (cong (pairKernel M left right +_)
      (fullInnerFactorization M left rest))
    (solve
      ( dissipation M left ∷ energy M left
      ∷ energy M right ∷ dissipation M right
      ∷ sumEnergy M rest ∷ sumDissipation M rest ∷ []))

fullOrderedPairFactorization :
  ∀ {a} {Mode : Set a}
    (M : ModalEnergyDissipation Mode)
    (lefts rights : List Mode) →
  fullOrderedPairSum M lefts rights
  ≡ sumDissipation M lefts * sumEnergy M rights
      + sumEnergy M lefts * sumDissipation M rights
fullOrderedPairFactorization M [] rights
  rewrite ℚP.*-zeroˡ (sumEnergy M rights)
        | ℚP.*-zeroˡ (sumDissipation M rights)
        | ℚP.+-identityʳ 0ℚ = refl
fullOrderedPairFactorization M (left ∷ lefts) rights =
  trans
    (cong (_+ fullOrderedPairSum M lefts rights)
      (fullInnerFactorization M left rights))
    (trans
      (cong
        (λ tail →
          (dissipation M left * sumEnergy M rights
            + energy M left * sumDissipation M rights) + tail)
        (fullOrderedPairFactorization M lefts rights))
      (solve
        ( dissipation M left ∷ energy M left
        ∷ sumDissipation M lefts ∷ sumEnergy M lefts
        ∷ sumEnergy M rights ∷ sumDissipation M rights ∷ [])))

selectedPairEnergyDissipationProductBound :
  ∀ {a} {Mode : Set a}
    (M : ModalEnergyDissipation Mode)
    (select : Mode → Mode → Bool)
    (modes : List Mode) →
  selectedOrderedPairSum M select modes modes
  ≤
  (sumEnergy M modes * sumDissipation M modes)
    + (sumEnergy M modes * sumDissipation M modes)
selectedPairEnergyDissipationProductBound M select modes =
  let
    selectedBelow = selectedOrderedPairSumBelowFull M select modes modes
    factor = fullOrderedPairFactorization M modes modes
    endpoint :
      sumDissipation M modes * sumEnergy M modes
        + sumEnergy M modes * sumDissipation M modes
      ≡
      sumEnergy M modes * sumDissipation M modes
        + sumEnergy M modes * sumDissipation M modes
    endpoint = solve
      (sumEnergy M modes ∷ sumDissipation M modes ∷ [])
  in
  subst
    (λ upper → selectedOrderedPairSum M select modes modes ≤ upper)
    (trans factor endpoint)
    selectedBelow

round109SelectedPairEnergyDissipationProductBoundClosed : Bool
round109SelectedPairEnergyDissipationProductBoundClosed = true

round109SelectedPairBoundHasNoCardinalityFactor : Bool
round109SelectedPairBoundHasNoCardinalityFactor = true

round109SelectedPairEnergyDissipationProductBoundClosedIsTrue :
  round109SelectedPairEnergyDissipationProductBoundClosed ≡ true
round109SelectedPairEnergyDissipationProductBoundClosedIsTrue = refl

round109SelectedPairBoundHasNoCardinalityFactorIsTrue :
  round109SelectedPairBoundHasNoCardinalityFactor ≡ true
round109SelectedPairBoundHasNoCardinalityFactorIsTrue = refl
