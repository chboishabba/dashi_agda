module DASHI.Physics.Closure.PhysicsClosureFull where

open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat) renaming (_+_ to _+N_)
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
import DASHI.Physics.Constraints.ConcreteInstance as CI
open import MDL.Core.Core as OldMDL
open import DASHI.MDL.MDLDescentTradeoff as MDL using (MDLParts)
open import DASHI.Physics.Closure.MDLTradeoffShiftInstance as MSI
open import DASHI.Physics.Closure.MDLFejerAxiomsShift as MDLFA
open import DASHI.Physics.Closure.DynamicalClosure as DC
open import DASHI.Physics.Closure.DynamicalClosureWitness as DCW
open import DASHI.Physics.Closure.OrthogonalityZLift
open import DASHI.Physics.UniversalityTheorem
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Geometry.OrthogonalityFromPolarization as OP
import DASHI.Physics.Signature31Canonical as S31C
open import DASHI.Physics.Closure.PhysicsClosureCoreWitness as PCCW
open import DASHI.Physics.Closure.ContractionForcesQuadraticTheorem as CFQT
open import DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem as CQSB
open import DASHI.Physics.Closure.CanonicalConstraintClosureWitness as CCCW

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
    signatureCoreProvider : S31C.IntrinsicCoreProvider
    signature31Theorem : SU.Signature31Theorem
    signature31 : CTI.Signature

    -- Constraint closure
    CS : ConstraintSystem
    L  : LieLike CS
    constraintClosure : ClosureLaw CS L

    -- MDL Lyapunov descent
    mdlLyap :
      ∀ {m k : Nat} →
      OldMDL.Lyapunov
        {S = RTC.Carrier (m +N k)}
        (MDLParts.T (MSI.MDLPartsShift {m} {k}))
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

record LegacyExternalInputs : Setω where
  field
    kit : RealClosureKit
    polarizationZ :
      ∀ {m : Nat} →
        OP.Polarization (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ
    orthogonalityZ :
      ∀ {m : Nat} →
        DASHI.Physics.Closure.OrthogonalityZLift.OrthogonalityZLift {m}
    signatureCoreProvider : S31C.IntrinsicCoreProvider
    mdlLyap :
      ∀ {m k : Nat} →
      OldMDL.Lyapunov
        {S = RTC.Carrier (m +N k)}
        (MDLParts.T (MSI.MDLPartsShift {m} {k}))
    mdlFejer : MDLFA.MDLFejerAxiomsShift
    dynamics : DC.DynamicalClosure
    universality : Universality (RealClosureKit.C kit)

physicsClosureFullFromLegacyExternal :
  LegacyExternalInputs →
  PhysicsClosureFull
physicsClosureFullFromLegacyExternal ext =
  record
    { kit = LegacyExternalInputs.kit ext
    ; metricEmergence = λ {ℓv} {ℓs} A F Pkg →
        PDP.quadraticFromProjectionDefect A F Pkg
    ; quadraticFormZ = λ {m} →
        CFQT.ContractionForcesQuadraticTheorem.derivedQuadratic
          (CFQT.canonicalContractionForcesQuadraticTheorem m)
    ; polarizationZ = LegacyExternalInputs.polarizationZ ext
    ; orthogonalityZ = LegacyExternalInputs.orthogonalityZ ext
    ; signatureCoreProvider =
        LegacyExternalInputs.signatureCoreProvider ext
    ; signature31Theorem =
        S31C.signature31-theoremFromProvider
          (LegacyExternalInputs.signatureCoreProvider ext)
    ; signature31 =
        S31C.signature31FromProvider
          (LegacyExternalInputs.signatureCoreProvider ext)
    ; CS = CI.CS
    ; L = CI.L
    ; constraintClosure =
        CCCW.CanonicalConstraintClosureWitness.closureWitness
          CCCW.canonicalConstraintClosureWitness
    ; mdlLyap = λ {m} {k} → LegacyExternalInputs.mdlLyap ext {m} {k}
    ; mdlFejer = LegacyExternalInputs.mdlFejer ext
    ; dynamics = LegacyExternalInputs.dynamics ext
    ; universality = LegacyExternalInputs.universality ext
    }

physicsClosureFullFromCoreWitness :
  PCCW.PhysicsClosureCoreWitness →
  PhysicsClosureFull
physicsClosureFullFromCoreWitness witness =
  record
    { kit = PCCW.PhysicsClosureCoreWitness.kit witness
    ; metricEmergence = λ {ℓv} {ℓs} A F Pkg →
        PDP.quadraticFromProjectionDefect A F Pkg
    ; quadraticFormZ = λ {m} →
        CFQT.ContractionForcesQuadraticTheorem.derivedQuadratic
          (CFQT.canonicalContractionForcesQuadraticTheorem m)
    ; polarizationZ =
        DCW.DynamicalClosureWitness.effectiveGeometryPolarization
          (PCCW.PhysicsClosureCoreWitness.dynamicsWitness witness)
    ; orthogonalityZ =
        DCW.DynamicalClosureWitness.effectiveGeometryOrthogonality
          (PCCW.PhysicsClosureCoreWitness.dynamicsWitness witness)
    ; signatureCoreProvider =
        PCCW.PhysicsClosureCoreWitness.signatureCoreProvider witness
    ; signature31Theorem =
        S31C.signature31-theoremFromProvider
          (PCCW.PhysicsClosureCoreWitness.signatureCoreProvider witness)
    ; signature31 =
        S31C.signature31FromProvider
          (PCCW.PhysicsClosureCoreWitness.signatureCoreProvider witness)
    ; CS = CI.CS
    ; L = CI.L
    ; constraintClosure =
        CCCW.CanonicalConstraintClosureWitness.closureWitness
          CCCW.canonicalConstraintClosureWitness
    ; mdlLyap = λ {m} {k} →
        DCW.DynamicalClosureWitness.monotoneLyapunov
          (PCCW.PhysicsClosureCoreWitness.dynamicsWitness witness)
          {m} {k}
    ; mdlFejer =
        DCW.DynamicalClosureWitness.monotoneFejer
          (PCCW.PhysicsClosureCoreWitness.dynamicsWitness witness)
    ; dynamics = PCCW.PhysicsClosureCoreWitness.dynamics witness
    ; universality = PCCW.PhysicsClosureCoreWitness.universality witness
    }
