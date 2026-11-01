module DASHI.Physics.Closure.PhysicsClosureEmpirical where

open import Agda.Builtin.Nat using (Nat; _+_)

open import DASHI.Physics.RealClosureKit
open import DASHI.Physics.Closure.ShiftSeamCertificates as SSC

-- Empirical closure package: contraction/Fejér/prox/MDL seams only.
-- Keeps quadratic/signature/constraints out of scope.
record PhysicsClosureEmpirical : Set₁ where
  field
    kit : RealClosureKit
    seams : ∀ {m k : Nat} → ShiftSeams {m} {k}

open PhysicsClosureEmpirical public
