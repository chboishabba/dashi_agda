module DASHI.Physics.Closure.NSTriadKNLuoFiniteStrainTransverseDecompositionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Evan Miller.
-- Title: "On the Interaction of Strain and Vorticity for Solutions of the
-- Navier--Stokes Equation".
-- arXiv:2407.02691.
-- DOI: none assigned in the cited preprint version.
--
-- PURPOSE
-- Instantiate the repository's exact rational orthogonal projection along a
-- unit vorticity direction.  For an arbitrary strain action v and unit
-- direction n, define
--
--   parallel(v)   = <n,v> n,
--   transverse(v) = v - parallel(v).
--
-- The module derives exact reconstruction, transverse orthogonality,
-- Pythagoras and squared contraction.  This is the algebraic content needed
-- by a normalized-vorticity direction equation; no continuum material
-- derivative or strain-tensor evolution is assumed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (0ℚ; 1ℚ; _+_; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V

record UnitDirectionAction : Set where
  constructor unit-direction-action
  field
    direction action : V.Vector3
    directionUnit : V.normSquared direction ≡ 1ℚ

open UnitDirectionAction public

projectionData : UnitDirectionAction → V.ProjectionMode
projectionData inputs = V.projection-mode
  (direction inputs)
  1ℚ
  (trans
    (solve (V.normSquared (direction inputs) ∷ []))
    (directionUnit inputs))

parallelAction : UnitDirectionAction → V.Vector3
parallelAction inputs = V.longitudinal (projectionData inputs) (action inputs)

transverseAction : UnitDirectionAction → V.Vector3
transverseAction inputs = V.project (projectionData inputs) (action inputs)

parallelActionMeaning :
  (inputs : UnitDirectionAction) →
  parallelAction inputs
  ≡ V.scale (V.dot (direction inputs) (action inputs)) (direction inputs)
parallelActionMeaning inputs
  with direction inputs | action inputs
... | V.v3 nx ny nz | V.v3 vx vy vz =
  V.vectorExt
    (solve (nx ∷ ny ∷ nz ∷ vx ∷ vy ∷ vz ∷ []))
    (solve (nx ∷ ny ∷ nz ∷ vx ∷ vy ∷ vz ∷ []))
    (solve (nx ∷ ny ∷ nz ∷ vx ∷ vy ∷ vz ∷ []))

strainActionReconstructs :
  (inputs : UnitDirectionAction) →
  V.add (transverseAction inputs) (parallelAction inputs)
  ≡ action inputs
strainActionReconstructs inputs =
  V.projectPlusLongitudinal (projectionData inputs) (action inputs)

transverseOrthogonalToDirection :
  (inputs : UnitDirectionAction) →
  V.dot (direction inputs) (transverseAction inputs) ≡ 0ℚ
transverseOrthogonalToDirection inputs =
  V.projectTransverse (projectionData inputs) (action inputs)

strainPythagorean :
  (inputs : UnitDirectionAction) →
  V.normSquared (action inputs)
  ≡ V.normSquared (transverseAction inputs)
    + V.normSquared (parallelAction inputs)
strainPythagorean inputs =
  V.projectPythagorean (projectionData inputs) (action inputs)

transverseContractionSquared :
  (inputs : UnitDirectionAction) →
  V.normSquared (transverseAction inputs)
  ≤ V.normSquared (action inputs)
transverseContractionSquared inputs =
  V.projectContractionSquared (projectionData inputs) (action inputs)
