module DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem where

-- Assumptions:
-- - strong contraction=>quadratic witness
-- - signature31 theorem surface
--
-- Output:
-- - canonical contraction=>quadratic=>signature bridge with normalized
--   quadratic witness.
--
-- Classification:
-- - canonical

-- Canonical quadratic -> signature bridge surface.
-- Stage-C pipeline modules should import this bridge rather than alternate
-- quadratic emergence routes.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Geometry.ConeTimeIsotropy as CTI
open import DASHI.Geometry.QuadraticForm as QF
open import DASHI.Geometry.Signature31FromIntrinsicShellForcing as S31ISF
open import DASHI.Geometry.SignatureUniqueness31 as SU
open import DASHI.Physics.Closure.ContractionForcesQuadraticTheorem as CFQT
open import DASHI.Physics.Closure.ContractionForcesQuadraticStrong as CFQS
open import DASHI.Physics.QuadraticPolarization as QP
open import DASHI.Physics.Signature31Canonical as S31C

record ContractionQuadraticToSignatureBridgeTheorem : Setω where
  field
    contractionForcesQuadraticTheorem : CFQT.ContractionForcesQuadraticTheorem
    strengthenedContraction : CFQS.ContractionForcesQuadraticStrong
    signature31Theorem : SU.Signature31Theorem
    signature31Value : CTI.Signature
    signatureForced31 : signature31Value ≡ CTI.sig31
    normalizedQuadratic :
      ∀ x →
        QF.QuadraticForm.Q
          (CFQS.ContractionForcesQuadraticStrong.derivedQuadratic
            strengthenedContraction)
          x
        ≡ QP.Q̂core x

contractionQuadraticToSignatureBridgeFromIntrinsicCore :
  (core : S31ISF.IntrinsicSignatureCoreAxioms) →
  ContractionQuadraticToSignatureBridgeTheorem
contractionQuadraticToSignatureBridgeFromIntrinsicCore core =
  record
    { contractionForcesQuadraticTheorem =
        CFQT.fromStrongContraction
          (S31ISF.IntrinsicSignatureCoreAxioms.strengthenedContraction core)
    ; strengthenedContraction =
        S31ISF.IntrinsicSignatureCoreAxioms.strengthenedContraction core
    ; signature31Theorem =
        S31ISF.signature31-theoremFromIntrinsic core
    ; signature31Value =
        S31ISF.signature31FromIntrinsic core
    ; signatureForced31 =
        S31ISF.signature31FromIntrinsicMatchesCTI core
    ; normalizedQuadratic =
        CFQS.admissibleForNormalization
          (CFQT.ContractionForcesQuadraticTheorem.admissibleQuadratic
            (CFQT.fromStrongContraction
              (S31ISF.IntrinsicSignatureCoreAxioms.strengthenedContraction core)))
    }

contractionQuadraticToSignatureBridgeFromProvider :
  (provider : S31C.IntrinsicCoreProvider) →
  ContractionQuadraticToSignatureBridgeTheorem
contractionQuadraticToSignatureBridgeFromProvider provider =
  contractionQuadraticToSignatureBridgeFromIntrinsicCore
    (S31C.IntrinsicCoreProvider.coreAxioms provider)

canonicalContractionQuadraticToSignatureBridgeTheorem :
  ContractionQuadraticToSignatureBridgeTheorem
canonicalContractionQuadraticToSignatureBridgeTheorem =
  contractionQuadraticToSignatureBridgeFromProvider
    S31C.shiftCoreProvider

signatureBridgeBoundary :
  (bridge : ContractionQuadraticToSignatureBridgeTheorem) →
  CFQS.SignatureCliffordGaugeBoundary
    (ContractionQuadraticToSignatureBridgeTheorem.strengthenedContraction bridge)
signatureBridgeBoundary bridge =
  CFQS.signatureCliffordGaugeBoundary
    (ContractionQuadraticToSignatureBridgeTheorem.strengthenedContraction bridge)
