module DASHI.Physics.Closure.CPTContract where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_)
open import Data.Empty using (⊥)
open import Data.Unit.Polymorphic using (⊤)

-- Discrete symmetries on the execution state.
-- CPT is not an axiom in this stack; it is an admissibility property of C, P, T.
record CPTOps {ℓ} (S : Set ℓ) : Set (lsuc ℓ) where
  field
    C : S → S
    P : S → S
    T : S → S

    C-involutive : ∀ s → C (C s) ≡ s
    P-involutive : ∀ s → P (P s) ≡ s
    T-involutive : ∀ s → T (T s) ≡ s

open CPTOps public

-- Combined CPT action.
CPT : ∀ {ℓ} {S : Set ℓ} → CPTOps S → S → S
CPT ops x = T ops (P ops (C ops x))

-- Step semantics in the same style used in LILA trace work.
record StepSystem {ℓ} (S : Set ℓ) : Set (lsuc ℓ) where
  field
    step : S → S
    Delta : S → S → S

open StepSystem public

-- Acceptance geometry and basin shells used by admissibility checks.
record ConeShell {ℓ} (S : Set ℓ) : Set (lsuc ℓ) where
  field
    InCone : S → Set

open ConeShell public

record BasinShell {ℓ} (S : Set ℓ) : Set (lsuc ℓ) where
  field
    InBasin : S → Set

open BasinShell public

-- MDL/Lyapunov scalar (descent-oriented).
record MDLShell {ℓ} (S : Set ℓ) : Set (lsuc ℓ) where
  field
    L : S → Nat

open MDLShell public

-- A concrete admissible step contract (the existing operational surface).
record StepAdmissible {ℓ}
  (S : Set ℓ)
  (sys : StepSystem S)
  (cone : ConeShell S)
  (basin : BasinShell S)
  (mdl : MDLShell S)
  : Set (lsuc ℓ) where
  field
    arrow-mdl-nondecreasing : ∀ s → L mdl (step sys s) ≤ L mdl s
    cone-ok : ∀ s → InCone cone (Delta sys s (step sys s))
    basin-ok : ∀ s → InBasin basin s → InBasin basin (step sys s)

open StepAdmissible public

-- Strong symmetry contract: CPT commutes with the step and preserves all
-- shell predicates with exact MDL invariance.
record CPTInvariant {ℓ}
  (S : Set ℓ)
  (ops : CPTOps S)
  (sys : StepSystem S)
  (cone : ConeShell S)
  (basin : BasinShell S)
  (mdl : MDLShell S)
  : Set (lsuc ℓ) where
  field
    step-commutes : ∀ s → step sys (CPT ops s) ≡ CPT ops (step sys s)

    cone-preserved :
      ∀ s₀ s₁ →
      InCone cone (Delta sys s₀ s₁) →
      InCone cone (Delta sys (CPT ops s₀) (CPT ops s₁))

    basin-preserved :
      ∀ s → InBasin basin s → InBasin basin (CPT ops s)

    mdl-preserved :
      ∀ s → L mdl (CPT ops s) ≡ L mdl s

open CPTInvariant public

-- Realistic contract for contraction-based systems:
-- symmetry may hold on a reversible sector only.
record ReversibleSector {ℓ} (S : Set ℓ) : Set (lsuc ℓ) where
  field
    InSector : S → Set

open ReversibleSector public

record LocalCPTInvariant {ℓ}
  (S : Set ℓ)
  (ops : CPTOps S)
  (sys : StepSystem S)
  (cone : ConeShell S)
  (basin : BasinShell S)
  (mdl : MDLShell S)
  (sector : ReversibleSector S)
  : Set (lsuc ℓ) where
  field
    sector-closed : ∀ s → InSector sector s → InSector sector (CPT ops s)

    step-commutes-local :
      ∀ s →
      InSector sector s → step sys (CPT ops s) ≡ CPT ops (step sys s)

    cone-preserved-local :
      ∀ s₀ s₁ →
      InSector sector s₀ →
      InSector sector s₁ →
      InCone cone (Delta sys s₀ s₁) →
      InCone cone (Delta sys (CPT ops s₀) (CPT ops s₁))

    basin-preserved-local :
      ∀ s → InSector sector s → InBasin basin s → InBasin basin (CPT ops s)

    mdl-preserved-local :
      ∀ s → InSector sector s → L mdl (CPT ops s) ≡ L mdl s

open LocalCPTInvariant public

-- Explicit obstruction package for the descent regime.
-- If L is strictly decreasing on every step, global T and hence CPT
-- cannot be expected from the dynamics alone.
record TimeArrowObstruction {ℓ}
  (S : Set ℓ)
  (sys : StepSystem S)
  (mdl : MDLShell S)
  : Set (lsuc ℓ) where
  field
    nonincreasing-mdl : ∀ s → L mdl (step sys s) ≤ L mdl s
    strict-mdl-drop : ∀ s → L mdl (step sys s) ≡ L mdl s → ⊥

open TimeArrowObstruction public

CPTObstructionByMDL :
  ∀ {ℓ} (S : Set ℓ) (sys : StepSystem S) (mdl : MDLShell S) →
  TimeArrowObstruction S sys mdl → Set (lsuc ℓ)
CPTObstructionByMDL _ _ _ _ = ⊤
