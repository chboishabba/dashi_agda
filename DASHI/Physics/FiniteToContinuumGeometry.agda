module DASHI.Physics.FiniteToContinuumGeometry where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer using (ℤ)

open import DASHI.Physics.LorentzianCoreClosure as LCC

------------------------------------------------------------------------
-- Finite masked geometry to continuum differential geometry.
--
-- The bridge records the exact compatibility obligations: an embedding of the
-- finite core, a metric extending Q₄, a connection, and curvature derived from
-- that connection.  Analytic convergence is explicit data, not hidden in a
-- postulate named "continuum".

record ContinuumGeometry : Set₁ where
  field
    Point   : Set
    Scalar  : Set
    Vector  : Set
    Tensor2 : Set
    Tensor4 : Set

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

    -- The continuum metric restricts to the masked weighted dot product.
    metricRestricts : ∀ x y →
      metric (tangentLift x) (tangentLift y)
        ≡ integerToScalar (LCC.Dot₄ x y)

    -- Refinement/convergence structure.  These predicates may be instantiated
    -- with Cauchy convergence, projective limits, or a chosen completion.
    Refinement : Set
    converges  : Refinement → Set
    compatibleRefinement : ∀ r → converges r

record ContinuumLorentzClosure : Set₁ where
  field
    geometry : ContinuumGeometry
    bridge   : FiniteContinuumBridge geometry

open ContinuumLorentzClosure public
