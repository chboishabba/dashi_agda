module DASHI.Physics.Cone.ArrowSeparatedDeltaConeShift where

open import Agda.Builtin.Nat using (Nat; _+_; zero)
open import Data.Nat using (_≤_; _∸_; z≤n)
open import Data.Integer using (ℤ; +_) renaming (_≤_ to _≤ᵢ_)
open import Data.Vec using (Vec)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

open import DASHI.Algebra.Trit using (Trit)
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.TailCollapseProof as TCP
open import DASHI.Physics.Closure.MDLTradeoffShiftInstance as MSI
open import DASHI.Physics.IndefiniteMaskQuadratic as IMQ
import DASHI.Physics.Cone.ArrowSeparatedDeltaCone as ASD

private
  S : ∀ {m k : Nat} → Set
  S {m} {k} = RTC.Carrier (m + k)

  arrow : ∀ {m k : Nat} → S {m} {k} → Nat
  arrow {m} {k} x = MSI.countNZ (TCP.tailOf m k x)

  splitS : ∀ {m k : Nat} → ASD.ArrowSplit {ℓs = _} {ℓa = _} {ℓx = _}
  splitS {m} {k} = record
    { State = S {m} {k}
    ; Shape = S {m} {k}
    ; Arrow = Nat
    ; split = λ x → x , arrow {m} {k} x
    }

  δ : ∀ {m k : Nat} → ASD.ArrowDelta (ASD.Shape (splitS {m} {k})) (ASD.Arrow (splitS {m} {k}))
  δ {m} {k} = record
    { ΔShape = λ x' _ → x'
    ; ΔArrow = λ a' a → a ∸ a'
    }

  forward : ∀ {m k : Nat} → ASD.ForwardPred (ASD.Arrow (splitS {m} {k}))
  forward {m} {k} = record
    { Forward = λ d → zero ≤ d
    }

  cone : ∀ {m k : Nat} (σ : Vec IMQ.Sign (m + k)) → ASD.ConeScreen (ASD.Shape (splitS {m} {k}))
  cone {m} {k} σ = record
    { Cone = λ s → (+ 0) ≤ᵢ IMQ.Qσ σ s
    }

record ShiftArrowSeparatedDeltaCone {m k : Nat} (σ : Vec IMQ.Sign (m + k)) : Set₁ where
  field
    step⇒forward : ∀ {x} → ASD.ForwardStep (splitS {m} {k}) (δ {m} {k}) (forward {m} {k}) x (TCP.Tᵣ {m} {k} x)
    forward⇒cone : ∀ {x} →
      ASD.ForwardStep (splitS {m} {k}) (δ {m} {k}) (forward {m} {k}) x (TCP.Tᵣ {m} {k} x) →
      ASD.ConeStep (splitS {m} {k}) (δ {m} {k}) (cone {m} {k} σ) x (TCP.Tᵣ {m} {k} x)

  kit : ASD.ArrowSeparatedDeltaCone (splitS {m} {k}) (δ {m} {k}) (forward {m} {k}) (cone {m} {k} σ) (λ x y → y ≡ TCP.Tᵣ {m} {k} x)
  kit = record
    { step⇒forward = stepForward
    ; forward⇒cone = coneForward
    }
    where
      stepForward :
        ∀ {x y} → y ≡ TCP.Tᵣ {m} {k} x →
        ASD.ForwardStep (splitS {m} {k}) (δ {m} {k}) (forward {m} {k}) x y
      stepForward {x} {y} eq rewrite eq = step⇒forward {x}

      coneForward :
        ∀ {x y} → y ≡ TCP.Tᵣ {m} {k} x →
        ASD.ForwardStep (splitS {m} {k}) (δ {m} {k}) (forward {m} {k}) x y →
        ASD.ConeStep (splitS {m} {k}) (δ {m} {k}) (cone {m} {k} σ) x y
      coneForward {x} {y} eq fw rewrite eq = forward⇒cone {x} fw

open ShiftArrowSeparatedDeltaCone public
