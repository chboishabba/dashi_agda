module DASHI.Physics.Closure.PhysicsClosureFull where

open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Unit using (⊤; tt)

open import DASHI.Physics.RealClosureKit
open import DASHI.Geometry.ProjectionDefect
open import DASHI.Geometry.QuadraticForm
open import DASHI.Geometry.QuadraticFormFromProjection
open import DASHI.Geometry.QuadraticFormEmergence
open import DASHI.Geometry.OrthogonalityFromPolarization
open import DASHI.Geometry.ConeTimeIsotropy
open import DASHI.Geometry.Signature31FromConeArrowIsotropy
open import DASHI.Physics.Constraints.Generators
open import DASHI.Physics.Constraints.Bracket
open import DASHI.Physics.Constraints.Closure
open import DASHI.MDL.MDLLyapunov
open import DASHI.Physics.Closure.MDLFejerAxiomsShift as MDLFA
open import DASHI.Physics.UniversalityTheorem

record PhysicsClosureFull : Set₁ where
  field
    kit : RealClosureKit

    -- Quadratic emergence
    metricEmergence : QuadraticFromProjection
    quadraticForm   : Set
    polarization    : Set
    orthogonality   : Set

    -- Signature lock
    signature31 : Signature

    -- Constraint closure
    CS : ConstraintSystem
    L  : LieLike CS
    constraintClosure : ClosureLaw CS L

    -- MDL Lyapunov descent
    mdlLyap : ∀ {S : Set} (T : S → S) → Set
    mdlFejer : MDLFA.MDLFejerAxiomsShift

    -- Universality
    universality : Universality
