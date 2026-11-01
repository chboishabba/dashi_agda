module DASHI.Physics.Closure.CanonicalContractionToCliffordBridgeTheorem where

-- Assumptions:
-- - concrete real stack unification witnesses
-- - canonical contraction=>signature and signature=>spin/Dirac bridges
-- - canonical quadratic=>Clifford bridge
--
-- Output:
-- - canonical contraction=>Clifford bridge bundle with concrete witnesses.
--
-- Classification:
-- - canonical

open import Agda.Primitive using (Setω)

open import DASHI.Physics.ClosureBuilder as CB
open import DASHI.Physics.ContractionQuadraticBridge as CQB
open import DASHI.Physics.SignatureClassificationBridge as SCB
open import DASHI.Physics.CliffordEvenLiftBridge as CE
open import DASHI.Physics.ConcreteClosureStack as CCS
open import DASHI.Physics.UnifiedClosure as UC
open import DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem as CQSB
open import DASHI.Physics.Closure.ContractionSignatureToSpinDiracBridgeTheorem as CSSDB
open import DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem as QTCB

record CanonicalContractionToCliffordBridgeTheorem : Setω where
  field
    contractionQuadraticToSignatureBridge :
      CQSB.ContractionQuadraticToSignatureBridgeTheorem
    contractionSignatureToSpinDiracBridge :
      CSSDB.ContractionSignatureToSpinDiracBridgeTheorem
    quadraticToCliffordBridge :
      QTCB.QuadraticToCliffordBridgeTheorem
    concreteContractionQuadraticBridge :
      CQB.Contraction⇒Quadratic
        (CB.U CCS.realStack) (CB.T CCS.realStack)
    concreteSignatureBridge : SCB.Quadratic⇒Signature
    concreteCliffordBridge : CE.Quadratic⇒Clifford
    concreteCliffordFromCanonicalQuadratic :
      CE.Clifford
        (CQB.V (CQB.out concreteContractionQuadraticBridge))
        (CQB.Scalar (CQB.out concreteContractionQuadraticBridge))
    concreteWaveLiftEvenBridge : CE.WaveLift⇒Even

canonicalContractionToCliffordBridgeTheorem :
  CanonicalContractionToCliffordBridgeTheorem
canonicalContractionToCliffordBridgeTheorem =
  let
    u = CCS.physicsUnification
    cq = UC.PhysicsUnification.cq u
    q2cl = UC.PhysicsUnification.q2cl u
  in
  record
    { contractionQuadraticToSignatureBridge =
        CQSB.canonicalContractionQuadraticToSignatureBridgeTheorem
    ; contractionSignatureToSpinDiracBridge =
        CSSDB.canonicalContractionSignatureToSpinDiracBridgeTheorem
    ; quadraticToCliffordBridge =
        QTCB.canonicalQuadraticToCliffordBridgeTheorem
    ; concreteContractionQuadraticBridge = cq
    ; concreteSignatureBridge = UC.PhysicsUnification.qs u
    ; concreteCliffordBridge = q2cl
    ; concreteCliffordFromCanonicalQuadratic =
        CE.Quadratic⇒Clifford.build q2cl (CQB.out cq)
    ; concreteWaveLiftEvenBridge = UC.PhysicsUnification.wl u
    }
