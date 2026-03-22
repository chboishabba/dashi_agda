module DASHI.Physics.Closure.PhysicsClosureFullInstance where

-- Assumptions:
-- - concrete real-kit instance and shift-side dynamics/constraint witnesses
-- - projection-defect/parallelogram route for quadratic emergence
--
-- Output:
-- - concrete PhysicsClosureFull instance used by canonical minimal-credible
--   closure.
--
-- Classification:
-- - concrete

open import Data.Unit as DU using (⊤; tt)
open import DASHI.Physics.Closure.OrthogonalityZLift as OZ
open import Agda.Builtin.Nat using (Nat; zero; _+_)

open import DASHI.Physics.Closure.PhysicsClosureFull as PCF
open import DASHI.Physics.MyRealInstance as MRI
open import DASHI.Physics.Closure.PolarizationZLift as PZL
open import DASHI.Physics.Closure.DynamicalClosureShiftInstance as DCSI
open import DASHI.Physics.Closure.DynamicalClosureShiftWitnessInstance as DCWI
open import DASHI.Physics.Closure.ExecutionAdmissibilityCurrentTraceWitness as EACTW
open import DASHI.Physics.Closure.ExecutionAdmissibilityCurrentFamilyWitness as EACFW
open import DASHI.Physics.Closure.MDLTradeoffShiftInstance as MSI
open import DASHI.Physics.Closure.MDLLyapunovShiftInstance as MDLL
open import DASHI.Physics.Closure.MDLFejerAxiomsShift as MDLFA
open import DASHI.Physics.Closure.PhysicsClosureCoreWitness as PCCW
open import DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem as CQSB
open import DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem as QTCB
open import DASHI.Physics.Closure.CanonicalConstraintClosureWitness as CCCW
open import DASHI.Physics.Closure.ClosureObservableWitness as COW
open import DASHI.Physics.Closure.ShiftClosureObservableWitnessInstance as SCOWI
open import DASHI.Physics.Closure.SyntheticClosureObservableWitnessInstance as SYCOWI
open import DASHI.Physics.Closure.RootSystemB4ClosureObservableWitnessInstance as B4COWI
open import DASHI.Physics.Signature31Canonical as S31C
open import DASHI.Physics.RealClosureKit as RK
open import MDL.Core.Core as OldMDL
open import DASHI.MDL.MDLDescentTradeoff as MDL using (MDLParts)
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.UniversalityTheorem as UTH
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Concrete instance: wires the Bool closure stack into PhysicsClosureFull.
-- The `mdlLyap` field now carries the authoritative shift witness directly.

physicsClosureFullFromProvider :
  S31C.IntrinsicCoreProvider → PCF.PhysicsClosureFull
physicsClosureFullFromProvider provider =
  PCF.canonicalPhysicsClosureFullFromExternal
    record
      { kit = MRI.myKit
      ; polarizationZ = λ {m} → PZL.polarizationZLift {m}
      ; orthogonalityZ = λ {m} → OZ.orthogonalityZLift {m}
      ; signatureCoreProvider = provider
      ; mdlLyap = λ {m} {k} → MDLL.lyapunovShift {m} {k}
      ; mdlFejer = MDLFA.mdlFejerShift
      ; dynamics = DCSI.shiftDynamics
      ; universality = UTH.canonicalUniversality (RK.RealClosureKit.C MRI.myKit)
      }

coreWitnessWithShiftObservables :
  (observables : COW.ClosureObservableWitness) →
  S31C.signature31FromProvider S31C.shiftCoreProvider
    ≡ COW.ClosureObservableWitness.provedSignature observables →
  PCCW.PhysicsClosureCoreWitness
coreWitnessWithShiftObservables observables signatureAgreement =
  record
    { kit = MRI.myKit
    ; universality = UTH.canonicalUniversality (RK.RealClosureKit.C MRI.myKit)
    ; contractionQuadraticWitness =
        CQSB.ContractionQuadraticToSignatureBridgeTheorem.strengthenedContraction
          CQSB.canonicalContractionQuadraticToSignatureBridgeTheorem
    ; contractionSignatureWitness =
        CQSB.canonicalContractionQuadraticToSignatureBridgeTheorem
    ; quadraticCliffordWitness =
        QTCB.canonicalQuadraticToCliffordBridgeTheorem
    ; signatureCoreProvider = S31C.shiftCoreProvider
    ; constraintClosureWitness = CCCW.canonicalConstraintClosureWitness
    ; dynamics = DCSI.shiftDynamics
    ; dynamicsWitness = DCWI.shiftDynamicsWitness
    ; executionAdmissibilityWitness = EACTW.currentTraceExecutionAdmissibility
    ; familyClassificationWitness = EACFW.currentFamilyClassification
    ; observables = observables
    ; observableSignatureAgreement = signatureAgreement
    }

coreWitnessWithB4Observables :
  (observables : COW.ClosureObservableWitness) →
  S31C.signature31FromProvider S31C.b4CoreProvider
    ≡ COW.ClosureObservableWitness.provedSignature observables →
  PCCW.PhysicsClosureCoreWitness
coreWitnessWithB4Observables observables signatureAgreement =
  record
    { kit = MRI.myKit
    ; universality = UTH.canonicalUniversality (RK.RealClosureKit.C MRI.myKit)
    ; contractionQuadraticWitness =
        CQSB.ContractionQuadraticToSignatureBridgeTheorem.strengthenedContraction
          CQSB.canonicalContractionQuadraticToSignatureBridgeTheorem
    ; contractionSignatureWitness =
        CQSB.canonicalContractionQuadraticToSignatureBridgeTheorem
    ; quadraticCliffordWitness =
        QTCB.canonicalQuadraticToCliffordBridgeTheorem
    ; signatureCoreProvider = S31C.b4CoreProvider
    ; constraintClosureWitness = CCCW.canonicalConstraintClosureWitness
    ; dynamics = DCSI.shiftDynamics
    ; dynamicsWitness = DCWI.shiftDynamicsWitness
    ; executionAdmissibilityWitness = EACTW.currentTraceExecutionAdmissibility
    ; familyClassificationWitness = EACFW.currentFamilyClassification
    ; observables = observables
    ; observableSignatureAgreement = signatureAgreement
    }

physicsClosureCoreWitness : PCCW.PhysicsClosureCoreWitness
physicsClosureCoreWitness =
  coreWitnessWithShiftObservables SCOWI.shiftClosureObservableWitness refl

syntheticPhysicsClosureCoreWitness : PCCW.PhysicsClosureCoreWitness
syntheticPhysicsClosureCoreWitness =
  record
    { kit = MRI.myKit
    ; universality = UTH.canonicalUniversality (RK.RealClosureKit.C MRI.myKit)
    ; contractionQuadraticWitness =
        CQSB.ContractionQuadraticToSignatureBridgeTheorem.strengthenedContraction
          CQSB.canonicalContractionQuadraticToSignatureBridgeTheorem
    ; contractionSignatureWitness =
        CQSB.canonicalContractionQuadraticToSignatureBridgeTheorem
    ; quadraticCliffordWitness =
        QTCB.canonicalQuadraticToCliffordBridgeTheorem
    ; signatureCoreProvider = S31C.syntheticCoreProvider
    ; constraintClosureWitness = CCCW.canonicalConstraintClosureWitness
    ; dynamics = DCSI.shiftDynamics
    ; dynamicsWitness = DCWI.shiftDynamicsWitness
    ; executionAdmissibilityWitness = EACTW.currentTraceExecutionAdmissibility
    ; familyClassificationWitness = EACFW.currentFamilyClassification
    ; observables = SYCOWI.syntheticClosureObservableWitness
    ; observableSignatureAgreement = refl
    }

b4PhysicsClosureCoreWitness : PCCW.PhysicsClosureCoreWitness
b4PhysicsClosureCoreWitness =
  coreWitnessWithB4Observables B4COWI.b4ClosureObservableWitness refl

physicsClosureFull : PCF.PhysicsClosureFull
physicsClosureFull =
  PCF.physicsClosureFullFromCoreWitness physicsClosureCoreWitness

physicsClosureFullSynthetic : PCF.PhysicsClosureFull
physicsClosureFullSynthetic =
  PCF.physicsClosureFullFromCoreWitness syntheticPhysicsClosureCoreWitness

b4PhysicsClosureFull : PCF.PhysicsClosureFull
b4PhysicsClosureFull =
  PCF.physicsClosureFullFromCoreWitness b4PhysicsClosureCoreWitness

-- Concrete Lyapunov witness for the shift stack is available as:
-- MDLL.lyapunovShift {m} {k}

authoritativeLyapunovShift :
  ∀ {m k : Nat} →
  OldMDL.Lyapunov
    {S = RTC.Carrier (m + k)}
    (MDLParts.T (MSI.MDLPartsShift {m} {k}))
authoritativeLyapunovShift {m} {k} =
  MDLL.lyapunovShift {m} {k}
