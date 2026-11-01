module DASHI.Physics.Closure.CanonicalProofSpine where

-- Canonical proof-spine forwarding module.
-- This is the authoritative import path for the current physics closure route.
--
-- Assumptions:
-- - uses the concrete real stack instance and canonical bridge modules.
--
-- Output:
-- - one ordered record exposing the canonical route from real stack through
--   strong contraction/quadratic/signature/Clifford to minimal-credible and
--   known-limits bridges.
--
-- Classification:
-- - canonical

open import Agda.Primitive using (Setω)

open import DASHI.Physics.ClosureBuilder as CB
open import DASHI.Physics.ConcreteClosureStack as CCS
open import DASHI.Physics.Closure.ContractionForcesQuadraticStrong as CFQS
open import DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem as CQSB
open import DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem as QTCB
open import DASHI.Physics.Closure.CliffordToEvenWaveLiftBridgeTheorem as CEW
open import DASHI.Physics.Closure.PhysicsClosureCoreWitness as PCCW
open import DASHI.Physics.Closure.PhysicsClosureConstructorTheorem as PCCT
open import DASHI.Physics.Closure.PhysicsClosureTheoremLadder as PCTL
open import DASHI.Physics.Closure.PhysicsClosureTheoremChecklist as PCTC
open import DASHI.Physics.Closure.PhysicsClosureFull as PCF
open import DASHI.Physics.Closure.PhysicsClosureFullInstance as PCFI

record CanonicalProofSpine : Setω where
  field
    concreteRealStack : CB.RealStack
    strongContractionQuadratic : CFQS.ContractionForcesQuadraticStrong
    canonicalContractionToSignature : CQSB.ContractionQuadraticToSignatureBridgeTheorem
    canonicalQuadraticToCliffordBridge : QTCB.QuadraticToCliffordBridgeTheorem
    canonicalCliffordToEvenWaveLiftBridge : CEW.CliffordToEvenWaveLiftBridgeTheorem
    canonicalCoreWitness : PCCW.PhysicsClosureCoreWitness
    canonicalConstructorTheorem : PCCT.PhysicsClosureConstructorTheorem
    canonicalTheoremLadder : PCTL.RealizationIndependentPhysicsClosureTheorem
    canonicalTheoremChecklist : PCTC.PhysicsClosureTheoremChecklist
    canonicalFullClosure : PCF.PhysicsClosureFull

canonicalProofSpine : CanonicalProofSpine
canonicalProofSpine =
  record
    { concreteRealStack = CCS.realStack
    ; strongContractionQuadratic = CFQS.canonicalNontrivialInvariantStrong
    ; canonicalContractionToSignature =
        CQSB.canonicalContractionQuadraticToSignatureBridgeTheorem
    ; canonicalQuadraticToCliffordBridge =
        QTCB.canonicalQuadraticToCliffordBridgeTheorem
    ; canonicalCliffordToEvenWaveLiftBridge =
        CEW.canonicalCliffordToEvenWaveLiftBridgeTheorem
    ; canonicalCoreWitness = PCFI.physicsClosureCoreWitness
    ; canonicalConstructorTheorem =
        PCCT.canonicalPhysicsClosureConstructorTheorem
    ; canonicalTheoremLadder =
        PCTL.realizationIndependentPhysicsClosureTheorem
    ; canonicalTheoremChecklist =
        PCTC.canonicalPhysicsClosureTheoremChecklist
    ; canonicalFullClosure = PCFI.physicsClosureFull
    }
