module DASHI.Physics.Closure.PhysicsClosureFullShift where

open import Agda.Primitive using (Setω)
open import Data.Unit using (⊤)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Physics.Closure.OrthogonalityZLift

open import DASHI.Physics.RealClosureKitFiber
open import DASHI.Geometry.SignatureUniqueness31
open import MDL.Core.Core as OldMDL
open import DASHI.MDL.MDLDescentTradeoff as MDL using (MDLParts)
open import DASHI.Physics.Closure.MDLTradeoffShiftInstance as MSI
open import DASHI.Physics.Closure.MDLFejerAxiomsShift as MDLFA
open import DASHI.Physics.Closure.DynamicalClosure as DC
open import DASHI.Physics.UniversalityTheorem
open import DASHI.Physics.Constraints.Generators
open import DASHI.Physics.Constraints.Bracket
open import DASHI.Physics.Constraints.Closure
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES
open import DASHI.Geometry.OrthogonalityFromPolarization as OP
open import DASHI.Geometry.QuadraticForm

-- Shift-specific closure package: uses the fiber kit and real MDL Lyapunov.
record PhysicsClosureFullShift : Setω where
  field
    kit : RealClosureKitFiber
    signature31 : Signature
    mdlLyap : ∀ {m k : Nat} → OldMDL.Lyapunov (MDLParts.T (MSI.MDLPartsShift {m} {k}))
    mdlFejer : MDLFA.MDLFejerAxiomsShift
    dynamics : DC.DynamicalClosure
    quadraticFormZ :
      ∀ {m : Nat} →
        QuadraticForm (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ
    polarizationZ :
      ∀ {m : Nat} →
        OP.Polarization (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ
    orthogonalityZ : ∀ {m : Nat} → OrthogonalityZLift {m}
    CS : ConstraintSystem
    L  : LieLike CS
    constraintClosure : ClosureLaw CS L
    universality : Universality (RealClosureKitFiber.C kit)
