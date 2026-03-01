module DASHI.Physics.Closure.MDLConcreteInstance where

open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties as NatP using (≤-refl)

open import DASHI.MDL.MDLLyapunov as MDL
open import DASHI.Physics.DefaultClosure as DC

-- Concrete MDL functional on the Bool carrier (trivial but real).
-- This gives us a fully provable Lyapunov descent instance.

MDLFunctionalInstance : MDL.MDLFunctional DC.Carrier
MDLFunctionalInstance =
  record
    { model = λ _ → zero
    ; residual = λ _ → zero
    ; mdl = λ _ → zero
    ; mdl≡ = λ _ → refl
    }

LyapunovInstance : MDL.MDLLyapunov DC.T MDLFunctionalInstance
LyapunovInstance =
  record
    { decreases = λ _ → NatP.≤-refl
    ; strictUnlessFixed = ⊤
    }
  where
    open import Data.Unit using (⊤; tt)
