module DASHI.Physics.RealCausalStructureInstance where

open import Agda.Builtin.Nat using (Nat)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (sym)
open import Data.Integer using (ℤ; +_) renaming (_≤_ to _≤ᵢ_)
open import Data.Integer.Properties as IntP
open import Data.Vec using (Vec)

open import DASHI.Algebra.Trit using (Trit)
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.IndefiniteMaskQuadratic as IMQ
open import DASHI.Physics.MaskedConeStructure as MCS
open import DASHI.Geometry.RealFiniteSpeed.Instance.Core as RFSI
open import DASHI.Physics.RealConeStructureInstance as RCSI

------------------------------------------------------------------------
-- Causal structure based on locality predicate (finite speed)

localCausal : ∀ {m : Nat} → MCS.CausalStructure m
localCausal {m} =
  record
    { _≼_  = λ x y → RFSI.local {n = m} x y
    ; delta = λ _ _ → RTC.zeroVec {n = m}
    }

------------------------------------------------------------------------
-- Cone monotonicity for the locality-based causal structure

coneMonotone-local :
  ∀ {m : Nat} (σ : Vec IMQ.Sign m) (x y : Vec Trit m) →
  MCS.CausalStructure._≼_ (localCausal {m}) x y →
  (+ 0) ≤ᵢ IMQ.Qσ σ (MCS.CausalStructure.delta (localCausal {m}) x y)
coneMonotone-local σ x y h =
  IntP.≤-reflexive (sym (RCSI.Qσ-zeroVec σ))
