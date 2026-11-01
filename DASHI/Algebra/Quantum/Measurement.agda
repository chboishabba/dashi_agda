module DASHI.Algebra.Quantum.Measurement where

open import DASHI.Core.Prelude
open import DASHI.Core.OperatorTypes
open import DASHI.Algebra.ProjectionVsInvertible using (projection+invertible→identity)

record Measurement {S : Set} (Π : S → S) : Set where
  field
    proj : Projection Π
    nontrivial : Nontrivial Π   -- measurement actually collapses something

measurement-not-invertible :
  ∀ {S : Set} {Π : S → S} →
  Measurement Π →
  ¬ Invertible Π
measurement-not-invertible {S} {Π} M invΠ =
  let open Measurement M in
  -- If Π invertible and projection ⇒ Π = id, contradict nontrivial.
  nontrivial (projection+invertible→identity proj invΠ)
