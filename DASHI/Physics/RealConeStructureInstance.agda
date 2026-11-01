module DASHI.Physics.RealConeStructureInstance where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; cong)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Integer using (ℤ; +_) renaming (_≤_ to _≤ᵢ_)
open import Data.Integer.Properties as IntP
open import Data.Nat.Base as NatB using (s≤s)
open import Data.Vec using (Vec; []; _∷_)

open import DASHI.Algebra.Trit using (Trit; zer)
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.IndefiniteMaskQuadratic as IMQ
open import DASHI.Physics.SignatureFromMask as SFM
open import DASHI.Physics.MaskedConeStructure as MCS

------------------------------------------------------------------------
-- Qσ evaluated on the zero vector

Qσ-zeroVec :
  ∀ {m : Nat} (σ : Vec IMQ.Sign m) →
  IMQ.Qσ σ (RTC.zeroVec {n = m}) ≡ (+ 0)
Qσ-zeroVec [] = refl
Qσ-zeroVec (s ∷ σ)
  rewrite Qσ-zeroVec σ
        | IntP.*-zeroʳ (IMQ.signℤ s)
  = refl

------------------------------------------------------------------------
-- A trivial causal structure (local order + zero delta)

trivialCausal : ∀ {m : Nat} → MCS.CausalStructure m
trivialCausal {m} =
  record
    { _≼_  = λ _ _ → ⊤
    ; delta = λ _ _ → RTC.zeroVec {n = m}
    }

------------------------------------------------------------------------
-- Cone monotonicity for the trivial causal structure

coneMonotone-trivial :
  ∀ {m : Nat} (σ : Vec IMQ.Sign m) (x y : Vec Trit m) →
  MCS.CausalStructure._≼_ (trivialCausal {m}) x y →
  (+ 0) ≤ᵢ IMQ.Qσ σ (MCS.CausalStructure.delta (trivialCausal {m}) x y)
coneMonotone-trivial σ x y _ =
  IntP.≤-reflexive (sym (Qσ-zeroVec σ))

------------------------------------------------------------------------
-- One-minus mask implies “not two time-like”

countMinus-oneMinus :
  ∀ {m : Nat} → SFM.countMinus (SFM.oneMinusRestPlus {m}) ≡ suc 0
countMinus-oneMinus {m} =
  cong suc (SFM.countMinus-replicatePlus {m})

noTwoTimeLike-oneMinus :
  ∀ {m : Nat} → ¬ MCS.TwoTimeLike (SFM.oneMinusRestPlus {m})
noTwoTimeLike-oneMinus {m} h
  rewrite countMinus-oneMinus {m}
  with h
... | s≤s ()

twoTimeLike→noUniqueFP-oneMinus :
  ∀ {m : Nat} (T : Vec Trit (suc m) → Vec Trit (suc m)) →
  MCS.TwoTimeLike (SFM.oneMinusRestPlus {m}) →
  ¬ MCS.UniqueFixedPoint T
twoTimeLike→noUniqueFP-oneMinus {m} T h =
  λ _ → noTwoTimeLike-oneMinus {m} h
