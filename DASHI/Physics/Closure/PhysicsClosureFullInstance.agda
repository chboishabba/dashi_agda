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
open import DASHI.Physics.Closure.MDLTradeoffShiftInstance as MSI
open import DASHI.Physics.Closure.MDLLyapunovShiftInstance as MDLL
open import DASHI.Physics.Closure.MDLFejerAxiomsShift as MDLFA
open import DASHI.Physics.Closure.PhysicsClosureCoreWitness as PCCW
open import DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem as CQSB
open import DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem as QTCB
open import DASHI.Physics.Closure.CliffordToEvenWaveLiftBridgeTheorem as CEW
open import DASHI.Physics.Closure.CanonicalConstraintClosureWitness as CCCW
open import DASHI.Physics.Closure.ShiftObservablePredictionInstance as SOPI
open import DASHI.Physics.Closure.SyntheticObservablePredictionInstance as SYOPI
open import DASHI.Physics.Signature31Canonical as S31C
open import DASHI.Physics.RealClosureKit as RK
open import MDL.Core.Core as OldMDL
open import DASHI.MDL.MDLDescentTradeoff as MDL using (MDLParts)
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.UniversalityTheorem as UTH
open import Relation.Binary.PropositionalEquality using (refl)

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

physicsClosureFull : PCF.PhysicsClosureFull
physicsClosureFull =
  PCF.physicsClosureFullFromCoreWitness physicsClosureCoreWitness

physicsClosureFullSynthetic : PCF.PhysicsClosureFull
physicsClosureFullSynthetic =
  PCF.physicsClosureFullFromCoreWitness syntheticPhysicsClosureCoreWitness

-- Concrete Lyapunov witness for the shift stack is available as:
-- MDLL.lyapunovShift {m} {k}

authoritativeLyapunovShift :
  ∀ {m k : Nat} →
  OldMDL.Lyapunov
    {S = RTC.Carrier (m + k)}
    (MDLParts.T (MSI.MDLPartsShift {m} {k}))
authoritativeLyapunovShift {m} {k} =
  MDLL.lyapunovShift {m} {k}

physicsClosureCoreWitness : PCCW.PhysicsClosureCoreWitness
physicsClosureCoreWitness =
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
    ; evenWaveLiftWitness =
        CEW.canonicalCliffordToEvenWaveLiftBridgeTheorem
    ; signatureCoreProvider = S31C.shiftCoreProvider
    ; constraintClosureWitness = CCCW.canonicalConstraintClosureWitness
    ; dynamics = DCSI.shiftDynamics
    ; dynamicsWitness = DCWI.shiftDynamicsWitness
    ; observables = SOPI.shiftObservablePrediction
    ; observableSignatureAgreement = refl
    }

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
    ; evenWaveLiftWitness =
        CEW.canonicalCliffordToEvenWaveLiftBridgeTheorem
    ; signatureCoreProvider = S31C.syntheticCoreProvider
    ; constraintClosureWitness = CCCW.canonicalConstraintClosureWitness
    ; dynamics = DCSI.shiftDynamics
    ; dynamicsWitness = DCWI.shiftDynamicsWitness
    ; observables = SYOPI.syntheticObservablePrediction
    ; observableSignatureAgreement = refl
    }
