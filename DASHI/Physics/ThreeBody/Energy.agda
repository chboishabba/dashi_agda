module DASHI.Physics.ThreeBody.Energy where

open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------------
-- Local energy / action package.
--
-- This is the right level for a Dashi-style three-body scaffold:
-- define the measurement surface without claiming global descent.

record ThreeBodyEnergyAction
  (State : Set)
  (Energy : Set)
  : Set₁ where
  field
    localEnergy : State → Energy
    actionFunctional : (Nat → State) → Energy

open ThreeBodyEnergyAction public
