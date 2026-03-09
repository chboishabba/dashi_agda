module DASHI.Physics.Closure.PhysicsClosureFull where

open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat)
open import Data.Unit using (⊤; tt)

open import DASHI.Physics.RealClosureKit
open import DASHI.Geometry.ProjectionDefect
open import DASHI.Geometry.QuadraticForm
open import DASHI.Geometry.QuadraticFormEmergence
open import DASHI.Geometry.OrthogonalityFromPolarization
open import DASHI.Geometry.ConeTimeIsotropy
open import DASHI.Geometry.Signature31FromConeArrowIsotropy
open import DASHI.Physics.Constraints.Generators
open import DASHI.Physics.Constraints.Bracket
open import DASHI.Physics.Constraints.Closure
open import MDL.Core.Core as OldMDL
open import DASHI.Physics.Closure.MDLFejerAxiomsShift as MDLFA
open import DASHI.Physics.Closure.DynamicalClosure as DC
open import DASHI.Physics.Closure.OrthogonalityZLift
open import DASHI.Physics.UniversalityTheorem
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES
open import DASHI.Geometry.OrthogonalityFromPolarization as OP

record PhysicsClosureFull : Setω where
  field
    kit : RealClosureKit

    -- Quadratic emergence
    metricEmergence :
      ∀ {ℓv ℓs} (A : Additive ℓv) (F : ScalarField ℓs)
        (PD : ProjectionDefect A) (Ax : QuadraticEmergenceAxioms A F PD)
      → Σ (QuadraticForm A F) (λ _ → ⊤)
    quadraticFormZ  :
      ∀ {m : Nat} →
        QuadraticForm (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ
    polarizationZ   :
      ∀ {m : Nat} →
        OP.Polarization (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ
    -- Orthogonality seam specialized to the ℤ-lifted carrier.
    orthogonalityZ  : ∀ {m : Nat} → DASHI.Physics.Closure.OrthogonalityZLift.OrthogonalityZLift {m}

    -- Signature lock
    signature31 : Signature

    -- Constraint closure
    CS : ConstraintSystem
    L  : LieLike CS
    constraintClosure : ClosureLaw CS L

    -- MDL Lyapunov descent
    mdlLyap : ∀ {S : Set} (T : S → S) → OldMDL.Lyapunov T
    mdlFejer : MDLFA.MDLFejerAxiomsShift
    dynamics : DC.DynamicalClosure

    -- Universality
    universality : Universality (RealClosureKit.C kit)
