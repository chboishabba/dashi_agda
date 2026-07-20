module DASHI.Physics.Closure.UltrametricDefectQuadraticPhysicsSpine where

-- Canonical theorem-facing spine for the current DASHI physics programme.
--
-- This module does not introduce a new physical axiom or promote a GR/QFT
-- claim.  It composes the existing canonical bridge theorems into one narrow
-- dependency surface:
--
--   hierarchical contraction / defect geometry
--     -> normalized quadratic form
--     -> Lorentz-signature bridge
--     -> Clifford and even-wave-lift bridge
--     -> spin / Dirac consumer.
--
-- The remaining continuum, constructive-QFT, and Clay-facing analytic
-- obligations stay in their existing fail-closed frontier modules.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Geometry.ConeTimeIsotropy as CTI
open import DASHI.Geometry.QuadraticForm as QF
open import DASHI.Physics.QuadraticPolarization as QP
open import DASHI.Physics.Closure.ContractionForcesQuadraticStrong as CFQS
open import DASHI.Physics.Closure.ContractionForcesQuadraticTheorem as CFQT
open import DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem as CQSB
open import DASHI.Physics.Closure.CanonicalContractionToCliffordBridgeTheorem as CCTCB
open import DASHI.Physics.Closure.ContractionSignatureToSpinDiracBridgeTheorem as CSSDB

record CanonicalPhysicsClosureSpine : Setω where
  field
    strengthenedContraction : CFQS.ContractionForcesQuadraticStrong
    contractionForcesQuadratic : CFQT.ContractionForcesQuadraticTheorem
    contractionQuadraticToSignature :
      CQSB.ContractionQuadraticToSignatureBridgeTheorem
    contractionToClifford :
      CCTCB.CanonicalContractionToCliffordBridgeTheorem
    contractionSignatureToSpinDirac :
      CSSDB.ContractionSignatureToSpinDiracBridgeTheorem

    normalizedQuadratic :
      ∀ x →
        QF.QuadraticForm.Q
          (CFQS.ContractionForcesQuadraticStrong.derivedQuadratic
            strengthenedContraction)
          x
        ≡ QP.Q̂core x

    signatureForced31 :
      CQSB.ContractionQuadraticToSignatureBridgeTheorem.signature31Value
        contractionQuadraticToSignature
      ≡ CTI.sig31

canonicalPhysicsClosureSpine : CanonicalPhysicsClosureSpine
canonicalPhysicsClosureSpine =
  let
    signatureBridge =
      CQSB.canonicalContractionQuadraticToSignatureBridgeTheorem
    strong =
      CQSB.ContractionQuadraticToSignatureBridgeTheorem.strengthenedContraction
        signatureBridge
  in
  record
    { strengthenedContraction = strong
    ; contractionForcesQuadratic =
        CFQT.fromStrongContraction strong
    ; contractionQuadraticToSignature = signatureBridge
    ; contractionToClifford =
        CCTCB.canonicalContractionToCliffordBridgeTheorem
    ; contractionSignatureToSpinDirac =
        CSSDB.canonicalContractionSignatureToSpinDiracBridgeTheorem
    ; normalizedQuadratic =
        CQSB.ContractionQuadraticToSignatureBridgeTheorem.normalizedQuadratic
          signatureBridge
    ; signatureForced31 =
        CQSB.ContractionQuadraticToSignatureBridgeTheorem.signatureForced31
          signatureBridge
    }

canonicalQuadraticIsNormalized :
  ∀ x →
    QF.QuadraticForm.Q
      (CFQS.ContractionForcesQuadraticStrong.derivedQuadratic
        (CanonicalPhysicsClosureSpine.strengthenedContraction
          canonicalPhysicsClosureSpine))
      x
    ≡ QP.Q̂core x
canonicalQuadraticIsNormalized =
  CanonicalPhysicsClosureSpine.normalizedQuadratic
    canonicalPhysicsClosureSpine

canonicalSignatureIs31 :
  CQSB.ContractionQuadraticToSignatureBridgeTheorem.signature31Value
    (CanonicalPhysicsClosureSpine.contractionQuadraticToSignature
      canonicalPhysicsClosureSpine)
  ≡ CTI.sig31
canonicalSignatureIs31 =
  CanonicalPhysicsClosureSpine.signatureForced31
    canonicalPhysicsClosureSpine

canonicalCliffordFromForcedQuadratic :
  CCTCB.CanonicalContractionToCliffordBridgeTheorem
canonicalCliffordFromForcedQuadratic =
  CanonicalPhysicsClosureSpine.contractionToClifford
    canonicalPhysicsClosureSpine

canonicalSpinDiracFromForcedSignature :
  CSSDB.ContractionSignatureToSpinDiracBridgeTheorem
canonicalSpinDiracFromForcedSignature =
  CanonicalPhysicsClosureSpine.contractionSignatureToSpinDirac
    canonicalPhysicsClosureSpine
