module DASHI.Physics.ThreeBody.Wave where

open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------------
-- Admissible path space and wave-facing kernel.
--
-- This is a path/kernel scaffold only. No positivity or major/minor arc
-- theorem is claimed here.

record ThreeBodyAdmissiblePath
  (State : Set)
  : Set₁ where
  field
    path : Nat → State
    admissible : Nat → Set

open ThreeBodyAdmissiblePath public

record ThreeBodyWaveKernel
  (State : Set)
  (Energy : Set)
  (Phase : Set)
  : Set₁ where
  field
    admissibleWeight :
      ThreeBodyAdmissiblePath State → Energy
    phaseLift :
      ThreeBodyAdmissiblePath State → Phase
    kernel :
      ThreeBodyAdmissiblePath State → Phase

open ThreeBodyWaveKernel public
