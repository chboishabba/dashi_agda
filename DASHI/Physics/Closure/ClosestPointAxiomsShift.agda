module DASHI.Physics.Closure.ClosestPointAxiomsShift where

open import Agda.Builtin.Nat using (Nat; _+_)

open import DASHI.Energy.FejerToClosestPoint as FC
open import DASHI.Physics.Closure.EnergyShiftBase as ESB

-- Single seam: closest-point axiom for the Bool shift instance.
record ClosestPointAxiomsShift : Set₁ where
  field
    closestAxiomShift :
      ∀ {m k : Nat} →
      FC.FejerClosestAxioms (ESB.EnergyShift {m} {k}) (ESB.ProjShift {m} {k})

open ClosestPointAxiomsShift public
