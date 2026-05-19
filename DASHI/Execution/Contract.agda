module DASHI.Execution.Contract where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_)

-- Execution-facing contract:
-- Δ is per-step, the cone condition is checked only on projected deltas,
-- and MDL / basin / eigen obligations remain separate fields.
record Contract
  {ℓx ℓs ℓδ ℓπ ℓe : Level} : Set (lsuc (ℓx ⊔ ℓs ⊔ ℓδ ⊔ ℓπ ⊔ ℓe)) where
  field
    State : Set ℓx
    Source : Set ℓs
    ΔState : Set ℓδ
    ΔSource : Set ℓπ
    Eigen : Set ℓe

    step : State → State
    π : State → Source
    Δ : State → ΔState
    projectΔ : ΔState → ΔSource

    Arrow : State → Nat
    Q : ΔSource → Nat
    L : State → Nat

    InBasin : Source → Set (ℓx ⊔ ℓs ⊔ ℓδ ⊔ ℓπ ⊔ ℓe)
    eigenOf : Source → Eigen
    eigenOverlap : Eigen → Eigen → Nat
    overlapFloor : Nat

  record ExecutionAdmissible : Set (ℓx ⊔ ℓs ⊔ ℓδ ⊔ ℓπ ⊔ ℓe) where
    field
      arrow-monotone : ∀ x → Arrow x ≤ Arrow (step x)
      cone-delta : ∀ x → Q (projectΔ (Δ x)) ≤ 0
      mdl-descent : ∀ x → L (step x) ≤ L x
      basin-preserved : ∀ x → InBasin (π x) → InBasin (π (step x))
      eigen-overlap : ∀ x → overlapFloor ≤ eigenOverlap (eigenOf (π x)) (eigenOf (π (step x)))

  admissible-step-stable :
    ExecutionAdmissible →
    ∀ x → InBasin (π x) → InBasin (π (step x))
  admissible-step-stable A x b =
    ExecutionAdmissible.basin-preserved A x b

open Contract public
