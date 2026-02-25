{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.PhysicsClosure where

open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.RealClosureKit
open import DASHI.Geometry.QuadraticFormFromProjection
open import DASHI.Geometry.OrthogonalityFromPolarization
open import DASHI.Geometry.SignatureUniqueness31
open import DASHI.Physics.Constraints.Generators
open import DASHI.Physics.Constraints.Bracket
open import DASHI.Physics.Constraints.Closure
open import DASHI.MDL.MDLLyapunov
open import DASHI.Physics.UniversalityTheorem

record PhysicsClosure : Set₁ where
  field
    kit : RealClosureKit
    metricEmergence : QuadraticFromProjection
    orthogonality : Set
    signature31 : Signature31Theorem
    CS : ConstraintSystem
    L  : LieLike CS
    constraintClosure : ClosureLaw CS L
    mdlLyap : ∀ {S : Set} (T : S → S) → Set
    universality : Universality
