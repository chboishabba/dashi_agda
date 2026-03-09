module DASHI.Physics.Closure.PhysicsClosure where

open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.RealClosureKit
open import DASHI.Geometry.QuadraticFormFromProjection
open import DASHI.Geometry.OrthogonalityFromPolarization
open import DASHI.Geometry.SignatureUniqueness31
open import DASHI.Physics.Constraints.Generators
open import DASHI.Physics.Constraints.Bracket
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Physics.Constraints.Closure
open import MDL.Core.Core as OldMDL
open import DASHI.Physics.Closure.OrthogonalityZLift
open import DASHI.Physics.UniversalityTheorem

record PhysicsClosure : Set₂ where
  field
    kit : RealClosureKit
    metricEmergence : QuadraticFromProjection
    -- Orthogonality seam specialized to the ℤ-lifted carrier.
    orthogonalityZ : ∀ {m : Nat} → OrthogonalityZLift {m}
    signature31 : Signature31Theorem
    CS : ConstraintSystem
    L  : LieLike CS
    constraintClosure : ClosureLaw CS L
    mdlLyap : ∀ {S : Set} (T : S → S) → OldMDL.Lyapunov T
    universality : Universality (RealClosureKit.C kit)
