module DASHI.Physics.Closure.CanonicalContractionQuadraticSignatureBridgeTheorem where

-- Assumptions:
-- - concrete real-stack unification witnesses
-- - canonical contraction=>Clifford bundle surface
--
-- Output:
-- - compatibility wrapper combining contraction=>quadratic/signature fields
--   with the canonical contraction=>Clifford bridge.
--
-- Classification:
-- - canonical (compatibility wrapper; non-primary import path)

open import Agda.Primitive using (Setω)

open import DASHI.Physics.ClosureBuilder as CB
open import DASHI.Physics.ContractionQuadraticBridge as CQB
open import DASHI.Physics.SignatureClassificationBridge as SCB
open import DASHI.Physics.ConcreteClosureStack as CCS
open import DASHI.Physics.UnifiedClosure as UC
open import DASHI.Physics.Closure.CanonicalContractionToCliffordBridgeTheorem as CCTCB

record CanonicalContractionQuadraticSignatureBridgeTheorem : Setω where
  field
    contractionQuadraticBridge :
      CQB.Contraction⇒Quadratic (CB.U CCS.realStack) (CB.T CCS.realStack)
    signatureClassificationBridge : SCB.Quadratic⇒Signature
    classifiedSignature : SCB.SignatureClassification
    canonicalContractionToCliffordBridge :
      CCTCB.CanonicalContractionToCliffordBridgeTheorem

canonicalContractionQuadraticSignatureBridgeTheorem :
  CanonicalContractionQuadraticSignatureBridgeTheorem
canonicalContractionQuadraticSignatureBridgeTheorem =
  let
    u = CCS.physicsUnification
    cq = UC.PhysicsUnification.cq u
    qs = UC.PhysicsUnification.qs u
    sym = UC.PhysicsUnification.sym u
  in
  record
    { contractionQuadraticBridge = cq
    ; signatureClassificationBridge = qs
    ; classifiedSignature = SCB.classify qs (CQB.out cq) sym
    ; canonicalContractionToCliffordBridge =
        CCTCB.canonicalContractionToCliffordBridgeTheorem
    }
