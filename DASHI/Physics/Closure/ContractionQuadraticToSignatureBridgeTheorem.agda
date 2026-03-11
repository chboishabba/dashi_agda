module DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem where

-- Canonical quadratic -> signature bridge surface.
-- Stage-C pipeline modules should import this bridge rather than alternate
-- quadratic emergence routes.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Geometry.ConeTimeIsotropy as CTI
open import DASHI.Geometry.QuadraticForm as QF
open import DASHI.Geometry.SignatureUniqueness31 as SU
open import DASHI.Physics.Closure.ContractionForcesQuadraticStrong as CFQS
open import DASHI.Physics.QuadraticPolarization as QP
open import DASHI.Physics.Signature31FromShiftOrbitProfile as S31OP

record ContractionQuadraticToSignatureBridgeTheorem : Setω where
  field
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

canonicalContractionQuadraticToSignatureBridgeTheorem :
  ContractionQuadraticToSignatureBridgeTheorem
canonicalContractionQuadraticToSignatureBridgeTheorem =
  record
    { strengthenedContraction = CFQS.canonicalNontrivialInvariantStrong
    ; signature31Theorem = S31OP.signature31-theorem
    ; signature31Value = S31OP.signature31
    ; signatureForced31 = refl
    ; normalizedQuadratic =
        CFQS.uniqueUpToScaleWitness
          CFQS.canonicalNontrivialInvariantStrong
    }
