module DASHI.Physics.Closure.ExecutionContract where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import DASHI.Physics.Closure.Basin as Basin using (Basin)
open import DASHI.Physics.Closure.Projection as Projection using (Projection)

-- Generic execution contract for a single step. The cone check is evaluated
-- on projected deltas rather than absolute states.
record ExecutionContract
  {ℓx ℓs ℓδ ℓπ ℓe : Level} : Set (lsuc (ℓx ⊔ ℓs ⊔ ℓδ ⊔ ℓπ ⊔ ℓe)) where
  field
    State : Set ℓx
    Source : Set ℓs
    ΔState : Set ℓδ
    ΔSource : Set ℓπ
    Eigen : Set ℓe

    projection : Projection State Source ΔState ΔSource
    sourceStep : Source → Source

    ArrowOK : State → State → Set (ℓx ⊔ ℓs ⊔ ℓδ ⊔ ℓπ ⊔ ℓe)
    ConeOK : ΔSource → Set (ℓx ⊔ ℓs ⊔ ℓδ ⊔ ℓπ ⊔ ℓe)
    mdl : State → Nat
    basin : Basin Source
    eigenOf : Source → Eigen
    eigenOverlap : Eigen → Eigen → Nat
    overlapFloor : Nat

  π : State → Source
  π = Projection.π projection

  Δ : State → State → ΔState
  Δ = Projection.Δ projection

  projectΔ : ΔState → ΔSource
  projectΔ = Projection.projectΔ projection

  BasinPred : Source → Set _
  BasinPred = Basin.InBasin basin

  StableShell : Source → Set _
  StableShell = Basin.StableShell basin

  basinStep :
    ∀ s →
    BasinPred s →
    BasinPred (Basin.step basin s)
  basinStep = Basin.basin-step basin

  ArrowAdmissible : State → State → Set _
  ArrowAdmissible x x' = ArrowOK x x'

  ConeAdmissible : State → State → Set _
  ConeAdmissible x x' = ConeOK (projectΔ (Δ x x'))

  MDLAdmissible : State → State → Set
  MDLAdmissible x x' = mdl x' ≤ mdl x

  BasinAdmissible : State → State → Set _
  BasinAdmissible x x' = BasinPred (π x) × BasinPred (π x')

  EigenAdmissible : State → State → Set
  EigenAdmissible x x' = overlapFloor ≤ eigenOverlap (eigenOf (π x)) (eigenOf (π x'))

  AdmissibleStep : State → State → Set _
  AdmissibleStep x x' =
    ArrowAdmissible x x'
    × ConeAdmissible x x'
    × MDLAdmissible x x'
    × BasinAdmissible x x'
    × EigenAdmissible x x'

  admissible→mdl :
    ∀ {x x'} →
    AdmissibleStep x x' →
    MDLAdmissible x x'
  admissible→mdl a = proj₁ (proj₂ (proj₂ a))

open ExecutionContract public
