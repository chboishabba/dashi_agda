module DASHI.Physics.FiniteToContinuumGeometry where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer using (ℤ)

open import DASHI.Physics.LorentzianCoreClosure as LCC

record ContinuumGeometry : Set₁ where
  field
    Point Scalar Vector Tensor2 Tensor4 : Set
    metric     : Vector → Vector → Scalar
    connection : Vector → Vector → Vector
    curvature  : Vector → Vector → Vector → Vector
    torsionFree      : Set
    metricCompatible : Set
    curvatureDerived : Set

record FiniteContinuumBridge (G : ContinuumGeometry) : Set₁ where
  open ContinuumGeometry G
  field
    core : LCC.LorentzianCoreClosure
    embedPoint  : LCC.Core4 → Point
    tangentLift : LCC.Core4 → Vector
    integerToScalar : ℤ → Scalar
    metricRestricts : ∀ x y →
      metric (tangentLift x) (tangentLift y)
        ≡ integerToScalar (LCC.Dot₄ x y)
    Refinement : Set
    converges  : Refinement → Set
    compatibleRefinement : ∀ r → converges r

record ContinuumLorentzClosure : Set₁ where
  field
    geometry : ContinuumGeometry
    bridge   : FiniteContinuumBridge geometry

open ContinuumLorentzClosure public
