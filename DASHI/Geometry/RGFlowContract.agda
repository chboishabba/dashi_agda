module DASHI.Geometry.RGFlowContract where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat using (_≤_; _<_)
open import Ultrametric
open import Contraction

record RGFlowAxioms : Set₁ where
  field
    CouplingState : Set
    U : Ultrametric CouplingState
    step : CouplingState → CouplingState
    mdl : CouplingState → Nat

    -- Two closure options:
    -- A) Contraction (metric closure)
    stepContractive : Contractive U step

    -- B) Lyapunov descent (MDL closure)
    mdlMonotone : ∀ s → mdl (step s) ≤ mdl s
