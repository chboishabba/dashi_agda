module DASHI.Physics.MaskedConeStructureAssumptions where

open import Agda.Builtin.Nat using (Nat)
open import Data.Integer using (+_) renaming (_≤_ to _≤ᵢ_)
open import Data.Vec using (Vec)

open import DASHI.Algebra.Trit using (Trit)
open import DASHI.Physics.IndefiniteMaskQuadratic as IMQ
open import DASHI.Physics.MaskedConeStructure as MCS

-- Cone monotonicity seam (assumption module).
record MaskedConeAxioms : Set₁ where
  field
    coneMonotone :
      ∀ {m : Nat} (σ : Vec IMQ.Sign m) (C : MCS.CausalStructure m) (x y : Vec Trit m) →
      MCS.CausalStructure._≼_ C x y →
      (+ 0) ≤ᵢ IMQ.Qσ σ (MCS.CausalStructure.delta C x y)

    -- Unique time direction seam (assumption module).
    twoTimeLike→noUniqueFP :
      ∀ {m : Nat} (σ : Vec IMQ.Sign m) (T : Vec Trit m → Vec Trit m) →
      MCS.TwoTimeLike σ → MCS.¬ MCS.UniqueFixedPoint T

coneMonotone :
  (A : MaskedConeAxioms) →
  ∀ {m : Nat} (σ : Vec IMQ.Sign m) (C : MCS.CausalStructure m) (x y : Vec Trit m) →
  MCS.CausalStructure._≼_ C x y →
  (+ 0) ≤ᵢ IMQ.Qσ σ (MCS.CausalStructure.delta C x y)
coneMonotone A = MaskedConeAxioms.coneMonotone A

twoTimeLike→noUniqueFP :
  (A : MaskedConeAxioms) →
  ∀ {m : Nat} (σ : Vec IMQ.Sign m) (T : Vec Trit m → Vec Trit m) →
  MCS.TwoTimeLike σ → MCS.¬ MCS.UniqueFixedPoint T
twoTimeLike→noUniqueFP A = MaskedConeAxioms.twoTimeLike→noUniqueFP A
