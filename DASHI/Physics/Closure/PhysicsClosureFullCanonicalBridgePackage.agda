module DASHI.Physics.Closure.PhysicsClosureFullCanonicalBridgePackage where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.PhysicsClosureFull as PCF
open import DASHI.Physics.Closure.PhysicsClosureFullInstance as PCFI
open import DASHI.Physics.Closure.PhysicsClosureCoreWitness as PCCW
open import DASHI.Physics.Closure.ContractionForcesQuadraticStrong as CFQS
open import DASHI.Physics.Closure.CanonicalContractionToCliffordBridgeTheorem as CCTCB
open import DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem as CQSB
open import DASHI.Physics.Closure.ContractionSignatureToSpinDiracBridgeTheorem as CSSDB
open import DASHI.Physics.Closure.CliffordToEvenWaveLiftBridgeTheorem as CTEW

-- Canonical package tying the full closure endpoint to the theorem-derived
-- Clifford/spin/Dirac bridge outputs.
record PhysicsClosureFullCanonicalBridgePackage : Setω where
  field
    fullClosure : PCF.PhysicsClosureFull
    contractionToCliffordBridge :
      CCTCB.CanonicalContractionToCliffordBridgeTheorem
    packageClosureQuadraticBoundary :
      CFQS.SignatureCliffordGaugeBoundary
        (CQSB.ContractionQuadraticToSignatureBridgeTheorem.strengthenedContraction
          (CCTCB.CanonicalContractionToCliffordBridgeTheorem.contractionQuadraticToSignatureBridge
            contractionToCliffordBridge))
    contractionSignatureToSpinDiracBridge :
      CSSDB.ContractionSignatureToSpinDiracBridgeTheorem
    cliffordToEvenWaveLiftBridge :
      CTEW.CliffordToEvenWaveLiftBridgeTheorem

canonicalPhysicsClosureFullCanonicalBridgePackage :
  PhysicsClosureFullCanonicalBridgePackage
canonicalPhysicsClosureFullCanonicalBridgePackage =
  record
    { fullClosure = PCF.physicsClosureFullFromCoreWitness PCFI.physicsClosureCoreWitness
    ; packageClosureQuadraticBoundary =
        PCCW.closureQuadraticBoundary PCFI.physicsClosureCoreWitness
    ; contractionToCliffordBridge =
        CCTCB.canonicalContractionToCliffordBridgeTheorem
    ; contractionSignatureToSpinDiracBridge =
        CSSDB.canonicalContractionSignatureToSpinDiracBridgeTheorem
    ; cliffordToEvenWaveLiftBridge =
        CTEW.canonicalCliffordToEvenWaveLiftBridgeTheorem
    }
