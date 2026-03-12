module DASHI.Physics.Closure.PhysicsClosureFull where

open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat)
open import Data.Unit using (⊤; tt)

open import DASHI.Physics.RealClosureKit
open import DASHI.Geometry.ProjectionDefect
open import DASHI.Geometry.QuadraticForm
open import DASHI.Geometry.ProjectionDefectToParallelogram as PDP
open import DASHI.Geometry.OrthogonalityFromPolarization
import DASHI.Geometry.ConeTimeIsotropy as CTI
open import DASHI.Geometry.Signature31FromConeArrowIsotropy
open import DASHI.Geometry.SignatureUniqueness31 as SU
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
open import DASHI.Physics.Closure.ContractionForcesQuadraticTheorem as CFQT
open import DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem as CQSB

record PhysicsClosureFull : Setω where
  field
    kit : RealClosureKit

    -- Quadratic emergence
    metricEmergence :
      ∀ {ℓv ℓs} (A : Additive ℓv) (F : ScalarField ℓs)
        (Pkg : PDP.ProjectionDefectParallelogramPackage A F)
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
    signature31Theorem : SU.Signature31Theorem
    signature31 : CTI.Signature

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

canonicalContractionQuadraticTheorem :
  CFQT.ContractionForcesQuadraticTheorem
canonicalContractionQuadraticTheorem =
  CFQT.canonicalRealStackContractionForcesQuadraticTheorem

canonicalContractionQuadraticToSignatureBridge :
  CQSB.ContractionQuadraticToSignatureBridgeTheorem
canonicalContractionQuadraticToSignatureBridge =
  CQSB.canonicalContractionQuadraticToSignatureBridgeTheorem
