module DASHI.Physics.Closure.CanonicalPrimeSelector where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties as NatP using (_≤?_; ≤-refl; ≤-trans; ≤-total)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary.Decidable.Core using (yes; no)

open import DASHI.Execution.Contract as EC
open import DASHI.Geometry.ShiftLorentzEmergenceInstance as SLEI
open import DASHI.Physics.Closure.CanonicalPrimeSelectionBridge
  using (ShiftContractState; shiftStep; canonicalPrimeWitness)
open import DASHI.Physics.Closure.CanonicalPrimeConcentration
  using
    ( PrimeWeight
    ; PrimeDominates
    ; PrimeConcentrated
    ; primeWeight-coarse-step-transport
    )
open import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI
  using (shiftCoarse)
open import MonsterOntos using
  ( SSP
  ; p2 ; p3 ; p5 ; p7 ; p11 ; p13 ; p17 ; p19 ; p23 ; p29 ; p31 ; p41 ; p47 ; p59 ; p71
  )

private
  ShiftC : EC.Contract
  ShiftC = SLEI.shiftContract {suc zero} {suc (suc (suc zero))}

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl yz = yz

chooseBetterByWeights : Nat → Nat → SSP → SSP → SSP
chooseBetterByWeights wp wq p q with NatP._≤?_ wq wp
... | yes _ = p
... | no _ = q

chooseBetter : ShiftContractState → SSP → SSP → SSP
chooseBetter x p q = chooseBetterByWeights (PrimeWeight x p) (PrimeWeight x q) p q

WeightEq : ShiftContractState → ShiftContractState → Set
WeightEq x y = ∀ p → PrimeWeight x p ≡ PrimeWeight y p

-- NOTE: A direct rewrite here forces heavy normalization of PrimeWeight
-- (transport, tail-split, etc.) and blows the inversion depth. We keep
-- the statement but avoid the reduction pressure by postulating it.
postulate
  chooseBetter-cong :
    ∀ {x y} →
    WeightEq x y →
    ∀ p q →
    chooseBetter x p q ≡ chooseBetter y p q

liftCandidate-cong :
  ∀ {x y} →
  WeightEq x y →
  (f : ShiftContractState → SSP) →
  ∀ p →
  (∀ {u v} → WeightEq u v → f u ≡ f v) →
  chooseBetter x (f x) p ≡ chooseBetter y (f y) p
liftCandidate-cong {x} {y} w≡ f p f-cong =
  trans
    (chooseBetter-cong {x} {y} w≡ (f x) p)
    (cong (λ z → chooseBetter y z p) (f-cong w≡))

chooseBetter-left-upper :
  ∀ x p q →
  PrimeWeight x p ≤ PrimeWeight x (chooseBetter x p q)
chooseBetter-left-upper x p q with NatP._≤?_ (PrimeWeight x q) (PrimeWeight x p)
... | yes _ = NatP.≤-refl
... | no q≰p with NatP.≤-total (PrimeWeight x p) (PrimeWeight x q)
...   | inj₁ p≤q = p≤q
...   | inj₂ q≤p = ⊥-elim (q≰p q≤p)

chooseBetter-right-upper :
  ∀ x p q →
  PrimeWeight x q ≤ PrimeWeight x (chooseBetter x p q)
chooseBetter-right-upper x p q with NatP._≤?_ (PrimeWeight x q) (PrimeWeight x p)
... | yes q≤p = q≤p
... | no _ = NatP.≤-refl

candidate₁ : ShiftContractState → SSP
candidate₁ x = chooseBetter x p2 p3

candidate₁-cong :
  ∀ {x y} →
  WeightEq x y →
  candidate₁ x ≡ candidate₁ y
candidate₁-cong {x} {y} w≡ =
  chooseBetter-cong {x} {y} w≡ p2 p3

candidate₂ : ShiftContractState → SSP
candidate₂ x = chooseBetter x (candidate₁ x) p5

candidate₂-cong :
  ∀ {x y} →
  WeightEq x y →
  candidate₂ x ≡ candidate₂ y
candidate₂-cong {x} {y} w≡ =
  liftCandidate-cong w≡ candidate₁ p5 candidate₁-cong

candidate₃ : ShiftContractState → SSP
candidate₃ x = chooseBetter x (candidate₂ x) p7

candidate₃-cong :
  ∀ {x y} →
  WeightEq x y →
  candidate₃ x ≡ candidate₃ y
candidate₃-cong {x} {y} w≡ =
  liftCandidate-cong w≡ candidate₂ p7 candidate₂-cong

candidate₄ : ShiftContractState → SSP
candidate₄ x = chooseBetter x (candidate₃ x) p11

candidate₄-cong :
  ∀ {x y} →
  WeightEq x y →
  candidate₄ x ≡ candidate₄ y
candidate₄-cong {x} {y} w≡ =
  liftCandidate-cong w≡ candidate₃ p11 candidate₃-cong

candidate₅ : ShiftContractState → SSP
candidate₅ x = chooseBetter x (candidate₄ x) p13

candidate₅-cong :
  ∀ {x y} →
  WeightEq x y →
  candidate₅ x ≡ candidate₅ y
candidate₅-cong {x} {y} w≡ =
  liftCandidate-cong w≡ candidate₄ p13 candidate₄-cong

candidate₆ : ShiftContractState → SSP
candidate₆ x = chooseBetter x (candidate₅ x) p17

candidate₆-cong :
  ∀ {x y} →
  WeightEq x y →
  candidate₆ x ≡ candidate₆ y
candidate₆-cong {x} {y} w≡ =
  liftCandidate-cong w≡ candidate₅ p17 candidate₅-cong

candidate₇ : ShiftContractState → SSP
candidate₇ x = chooseBetter x (candidate₆ x) p19

candidate₇-cong :
  ∀ {x y} →
  WeightEq x y →
  candidate₇ x ≡ candidate₇ y
candidate₇-cong {x} {y} w≡ =
  liftCandidate-cong w≡ candidate₆ p19 candidate₆-cong

candidate₈ : ShiftContractState → SSP
candidate₈ x = chooseBetter x (candidate₇ x) p23

candidate₈-cong :
  ∀ {x y} →
  WeightEq x y →
  candidate₈ x ≡ candidate₈ y
candidate₈-cong {x} {y} w≡ =
  liftCandidate-cong w≡ candidate₇ p23 candidate₇-cong

candidate₉ : ShiftContractState → SSP
candidate₉ x = chooseBetter x (candidate₈ x) p29

candidate₉-cong :
  ∀ {x y} →
  WeightEq x y →
  candidate₉ x ≡ candidate₉ y
candidate₉-cong {x} {y} w≡ =
  liftCandidate-cong w≡ candidate₈ p29 candidate₈-cong

candidate₁₀ : ShiftContractState → SSP
candidate₁₀ x = chooseBetter x (candidate₉ x) p31

candidate₁₀-cong :
  ∀ {x y} →
  WeightEq x y →
  candidate₁₀ x ≡ candidate₁₀ y
candidate₁₀-cong {x} {y} w≡ =
  liftCandidate-cong w≡ candidate₉ p31 candidate₉-cong

candidate₁₁ : ShiftContractState → SSP
candidate₁₁ x = chooseBetter x (candidate₁₀ x) p41

candidate₁₁-cong :
  ∀ {x y} →
  WeightEq x y →
  candidate₁₁ x ≡ candidate₁₁ y
candidate₁₁-cong {x} {y} w≡ =
  liftCandidate-cong w≡ candidate₁₀ p41 candidate₁₀-cong

candidate₁₂ : ShiftContractState → SSP
candidate₁₂ x = chooseBetter x (candidate₁₁ x) p47

candidate₁₂-cong :
  ∀ {x y} →
  WeightEq x y →
  candidate₁₂ x ≡ candidate₁₂ y
candidate₁₂-cong {x} {y} w≡ =
  liftCandidate-cong w≡ candidate₁₁ p47 candidate₁₁-cong

candidate₁₃ : ShiftContractState → SSP
candidate₁₃ x = chooseBetter x (candidate₁₂ x) p59

candidate₁₃-cong :
  ∀ {x y} →
  WeightEq x y →
  candidate₁₃ x ≡ candidate₁₃ y
candidate₁₃-cong {x} {y} w≡ =
  liftCandidate-cong w≡ candidate₁₂ p59 candidate₁₂-cong

candidate₁₄ : ShiftContractState → SSP
candidate₁₄ x = chooseBetter x (candidate₁₃ x) p71

candidate₁₄-cong :
  ∀ {x y} →
  WeightEq x y →
  candidate₁₄ x ≡ candidate₁₄ y
candidate₁₄-cong {x} {y} w≡ =
  liftCandidate-cong w≡ candidate₁₃ p71 candidate₁₃-cong

selectPrime : ShiftContractState → SSP
selectPrime = candidate₁₄

selectPrime-cong :
  ∀ {x y} →
  WeightEq x y →
  selectPrime x ≡ selectPrime y
selectPrime-cong {x} {y} w≡ = candidate₁₄-cong {x} {y} w≡

selected-dominates-from₁ : ∀ x → PrimeWeight x (candidate₁ x) ≤ PrimeWeight x (selectPrime x)
selected-dominates-from₁ x =
  NatP.≤-trans
    (chooseBetter-left-upper x (candidate₁ x) p5)
    (NatP.≤-trans
      (chooseBetter-left-upper x (candidate₂ x) p7)
      (NatP.≤-trans
        (chooseBetter-left-upper x (candidate₃ x) p11)
        (NatP.≤-trans
          (chooseBetter-left-upper x (candidate₄ x) p13)
          (NatP.≤-trans
            (chooseBetter-left-upper x (candidate₅ x) p17)
            (NatP.≤-trans
              (chooseBetter-left-upper x (candidate₆ x) p19)
              (NatP.≤-trans
                (chooseBetter-left-upper x (candidate₇ x) p23)
                (NatP.≤-trans
                  (chooseBetter-left-upper x (candidate₈ x) p29)
                  (NatP.≤-trans
                    (chooseBetter-left-upper x (candidate₉ x) p31)
                    (NatP.≤-trans
                      (chooseBetter-left-upper x (candidate₁₀ x) p41)
                      (NatP.≤-trans
                        (chooseBetter-left-upper x (candidate₁₁ x) p47)
                        (NatP.≤-trans
                          (chooseBetter-left-upper x (candidate₁₂ x) p59)
                          (chooseBetter-left-upper x (candidate₁₃ x) p71))))))))))))

selected-dominates-from₁₃ : ∀ x → PrimeWeight x (candidate₁₃ x) ≤ PrimeWeight x (selectPrime x)
selected-dominates-from₁₃ x =
  chooseBetter-left-upper x (candidate₁₃ x) p71

selected-dominates-from₁₂ : ∀ x → PrimeWeight x (candidate₁₂ x) ≤ PrimeWeight x (selectPrime x)
selected-dominates-from₁₂ x =
  NatP.≤-trans
    (chooseBetter-left-upper x (candidate₁₂ x) p59)
    (selected-dominates-from₁₃ x)

selected-dominates-from₁₁ : ∀ x → PrimeWeight x (candidate₁₁ x) ≤ PrimeWeight x (selectPrime x)
selected-dominates-from₁₁ x =
  NatP.≤-trans
    (chooseBetter-left-upper x (candidate₁₁ x) p47)
    (selected-dominates-from₁₂ x)

selected-dominates-from₁₀ : ∀ x → PrimeWeight x (candidate₁₀ x) ≤ PrimeWeight x (selectPrime x)
selected-dominates-from₁₀ x =
  NatP.≤-trans
    (chooseBetter-left-upper x (candidate₁₀ x) p41)
    (selected-dominates-from₁₁ x)

selected-dominates-from₉ : ∀ x → PrimeWeight x (candidate₉ x) ≤ PrimeWeight x (selectPrime x)
selected-dominates-from₉ x =
  NatP.≤-trans
    (chooseBetter-left-upper x (candidate₉ x) p31)
    (selected-dominates-from₁₀ x)

selected-dominates-from₈ : ∀ x → PrimeWeight x (candidate₈ x) ≤ PrimeWeight x (selectPrime x)
selected-dominates-from₈ x =
  NatP.≤-trans
    (chooseBetter-left-upper x (candidate₈ x) p29)
    (selected-dominates-from₉ x)

selected-dominates-from₇ : ∀ x → PrimeWeight x (candidate₇ x) ≤ PrimeWeight x (selectPrime x)
selected-dominates-from₇ x =
  NatP.≤-trans
    (chooseBetter-left-upper x (candidate₇ x) p23)
    (selected-dominates-from₈ x)

selected-dominates-from₆ : ∀ x → PrimeWeight x (candidate₆ x) ≤ PrimeWeight x (selectPrime x)
selected-dominates-from₆ x =
  NatP.≤-trans
    (chooseBetter-left-upper x (candidate₆ x) p19)
    (selected-dominates-from₇ x)

selected-dominates-from₅ : ∀ x → PrimeWeight x (candidate₅ x) ≤ PrimeWeight x (selectPrime x)
selected-dominates-from₅ x =
  NatP.≤-trans
    (chooseBetter-left-upper x (candidate₅ x) p17)
    (selected-dominates-from₆ x)

selected-dominates-from₄ : ∀ x → PrimeWeight x (candidate₄ x) ≤ PrimeWeight x (selectPrime x)
selected-dominates-from₄ x =
  NatP.≤-trans
    (chooseBetter-left-upper x (candidate₄ x) p13)
    (selected-dominates-from₅ x)

selected-dominates-from₃ : ∀ x → PrimeWeight x (candidate₃ x) ≤ PrimeWeight x (selectPrime x)
selected-dominates-from₃ x =
  NatP.≤-trans
    (chooseBetter-left-upper x (candidate₃ x) p11)
    (selected-dominates-from₄ x)

selected-dominates-from₂ : ∀ x → PrimeWeight x (candidate₂ x) ≤ PrimeWeight x (selectPrime x)
selected-dominates-from₂ x =
  NatP.≤-trans
    (chooseBetter-left-upper x (candidate₂ x) p7)
    (selected-dominates-from₃ x)

selected-dominates :
  ∀ x →
  PrimeDominates x (selectPrime x)
selected-dominates x p2  =
  NatP.≤-trans
    (chooseBetter-left-upper x p2 p3)
    (selected-dominates-from₁ x)
selected-dominates x p3  =
  NatP.≤-trans
    (chooseBetter-right-upper x p2 p3)
    (selected-dominates-from₁ x)
selected-dominates x p5  =
  NatP.≤-trans
    (chooseBetter-right-upper x (candidate₁ x) p5)
    (selected-dominates-from₂ x)
selected-dominates x p7  =
  NatP.≤-trans
    (chooseBetter-right-upper x (candidate₂ x) p7)
    (selected-dominates-from₃ x)
selected-dominates x p11 =
  NatP.≤-trans
    (chooseBetter-right-upper x (candidate₃ x) p11)
    (selected-dominates-from₄ x)
selected-dominates x p13 =
  NatP.≤-trans
    (chooseBetter-right-upper x (candidate₄ x) p13)
    (selected-dominates-from₅ x)
selected-dominates x p17 =
  NatP.≤-trans
    (chooseBetter-right-upper x (candidate₅ x) p17)
    (selected-dominates-from₆ x)
selected-dominates x p19 =
  NatP.≤-trans
    (chooseBetter-right-upper x (candidate₆ x) p19)
    (selected-dominates-from₇ x)
selected-dominates x p23 =
  NatP.≤-trans
    (chooseBetter-right-upper x (candidate₇ x) p23)
    (selected-dominates-from₈ x)
selected-dominates x p29 =
  NatP.≤-trans
    (chooseBetter-right-upper x (candidate₈ x) p29)
    (selected-dominates-from₉ x)
selected-dominates x p31 =
  NatP.≤-trans
    (chooseBetter-right-upper x (candidate₉ x) p31)
    (selected-dominates-from₁₀ x)
selected-dominates x p41 =
  NatP.≤-trans
    (chooseBetter-right-upper x (candidate₁₀ x) p41)
    (selected-dominates-from₁₁ x)
selected-dominates x p47 =
  NatP.≤-trans
    (chooseBetter-right-upper x (candidate₁₁ x) p47)
    (selected-dominates-from₁₂ x)
selected-dominates x p59 =
  NatP.≤-trans
    (chooseBetter-right-upper x (candidate₁₂ x) p59)
    (selected-dominates-from₁₃ x)
selected-dominates x p71 =
  chooseBetter-right-upper x (candidate₁₃ x) p71

selector-sound :
  ∀ x →
  PrimeConcentrated x (selectPrime x)
selector-sound x =
  canonicalPrimeWitness x (selectPrime x)
  ,
  selected-dominates x

stepCoarse-weightEq :
  ∀ x →
  WeightEq (shiftCoarse (shiftStep x)) (shiftStep (shiftCoarse x))
stepCoarse-weightEq x p = primeWeight-coarse-step-transport x p

selector-no-loss-target :
  EC.Contract.ExecutionAdmissible ShiftC
    →
  ∀ x →
  PrimeConcentrated (shiftStep x) (selectPrime (shiftStep x))
    →
  PrimeConcentrated x (selectPrime x)
selector-no-loss-target _ x _ = selector-sound x

selector-step-coarse-target :
  ∀ x →
  selectPrime (shiftCoarse (shiftStep x))
    ≡
  selectPrime (shiftStep (shiftCoarse x))
selector-step-coarse-target x =
  selectPrime-cong (stepCoarse-weightEq x)

selectedWeight : ShiftContractState → Nat
selectedWeight x = PrimeWeight x (selectPrime x)

record CanonicalPrimeSelector : Set₁ where
  field
    selectedPrime : ShiftContractState → SSP
    selectedWeightAt : ShiftContractState → Nat
    selectorSound : Set
    selectorNoLoss : Set
    selectorStepCoarse : Set

canonicalPrimeSelector : CanonicalPrimeSelector
canonicalPrimeSelector = record
  { selectedPrime = selectPrime
  ; selectedWeightAt = selectedWeight
  ; selectorSound = ∀ x → PrimeConcentrated x (selectPrime x)
  ; selectorNoLoss =
      EC.Contract.ExecutionAdmissible ShiftC
        →
      ∀ x →
      PrimeConcentrated (shiftStep x) (selectPrime (shiftStep x))
        →
      PrimeConcentrated x (selectPrime x)
  ; selectorStepCoarse =
      ∀ x →
      selectPrime (shiftCoarse (shiftStep x))
        ≡
      selectPrime (shiftStep (shiftCoarse x))
  }
