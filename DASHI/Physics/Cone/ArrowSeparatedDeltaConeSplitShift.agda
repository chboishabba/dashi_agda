module DASHI.Physics.Cone.ArrowSeparatedDeltaConeSplitShift where

open import Level using (Level; suc; _⊔_) renaming (zero to lzero)
open import Agda.Builtin.Nat using (Nat; _+_; zero)
open import Data.Nat using (_≤_; _∸_)
open import Data.Product using (_,_)
open import Data.Vec using (Vec)
open import Data.Integer using (ℤ; +_) renaming (_≤_ to _≤ᵢ_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Cone.ArrowSeparatedDeltaCone as ASD
open import DASHI.Physics.Cone.ArrowSeparatedDeltaConeSplit as ADSplit
open import DASHI.Physics.MaskedOrthogonalSplit as MOS
open import DASHI.Physics.TailCollapseProof as TCP
open import DASHI.Physics.IndefiniteMaskQuadratic as IMQ
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.Closure.MDLTradeoffShiftInstance as MSI

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

-- Concrete wiring to the shift step; split/forward/cone are fixed by ADS.
record ShiftArrowSeparatedConeSplit
  {ℓr : Level}
  {m k : Nat}
  (σ : Vec IMQ.Sign (m + k))
  (R : Set ℓr)
  (A : MOS.Additive (S {m} {k}))
  (B : MOS.Bilinear (S {m} {k}) R)
  (QF : MOS.Quadratic (S {m} {k}) R)
  (AR : MOS.AdditiveR R)
  (Pr : MOS.Projection (S {m} {k}))
  (SC : ADSplit.SplitCone (S {m} {k}))
  : Set (suc ℓr ⊔ suc lzero) where
  field
    coneSplitKit : ADSplit.ArrowSeparatedConeSplit
      (splitS {m} {k})
      R
      (δ {m} {k})
      (forward {m} {k})
      (cone {m} {k} σ)
      (λ x y → y ≡ TCP.Tᵣ {m} {k} x)
      A B QF AR Pr SC

open ShiftArrowSeparatedConeSplit public
