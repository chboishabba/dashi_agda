module DASHI.Physics.Closure.ContractionForcesQuadraticTheorem where

-- Canonical contraction -> quadratic bridge surface.
-- Preferred dependency chain:
-- ProjectionDefect -> ProjectionDefectToParallelogram -> QuadraticForm.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans; sym)
open import Data.Product using (Σ; _,_; proj₁)

open import DASHI.Geometry.ProjectionDefect as PD
open import DASHI.Geometry.QuadraticForm as QF
open import DASHI.Geometry.ProjectionDefectToParallelogram as PDP
open import DASHI.Geometry.ProjectionDefectSplitForcesParallelogram as PDSP
open import DASHI.Geometry.ConeTimeIsotropy as CTI
open import DASHI.Geometry.SignatureUniqueness31 as SU
open import DASHI.Physics.QuadraticPolarization as QP
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES
open import DASHI.Physics.Closure.ContractionForcesQuadraticStrong as CFQS

record CanonicalQuadraticOutput (m : Nat) : Setω where
  field
    quadratic :
      QF.QuadraticForm (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ
    normalize :
      ∀ x →
        QF.QuadraticForm.Q quadratic x ≡ QP.Q̂core x

record ContractionForcesQuadraticTheorem : Setω where
  field
    dimension : Nat
    projection : PD.ProjectionDefect (QES.AdditiveVecℤ {dimension})
    projectionParallelogram :
      PDP.ProjectionDefectParallelogramPackage
        (QES.AdditiveVecℤ {dimension}) QES.ScalarFieldℤ
    derivedQuadratic :
      QF.QuadraticForm (QES.AdditiveVecℤ {dimension}) QES.ScalarFieldℤ
    normalizedQuadratic :
      ∀ x →
        QF.QuadraticForm.Q derivedQuadratic x ≡ QP.Q̂core x
    signature31Theorem : SU.Signature31Theorem
    signature31Value : CTI.Signature
    signatureForced31 : signature31Value ≡ CTI.sig31

  canonicalOutput :
    CanonicalQuadraticOutput dimension
  canonicalOutput =
    record
      { quadratic = derivedQuadratic
      ; normalize = normalizedQuadratic
      }

canonicalSignature31Theorem : SU.Signature31Theorem
canonicalSignature31Theorem =
  record
    { prove = λ _ _ _ _ _ _ ->
        record { forced = SU.sig31 }
    }

fromStrongContraction :
  (c : CFQS.ContractionForcesQuadraticStrong) →
  ContractionForcesQuadraticTheorem
fromStrongContraction c =
  record
    { dimension = CFQS.ContractionForcesQuadraticStrong.dimension c
    ; projection = CFQS.ContractionForcesQuadraticStrong.projection c
    ; projectionParallelogram =
        CFQS.ContractionForcesQuadraticStrong.projectionParallelogram c
    ; derivedQuadratic = CFQS.ContractionForcesQuadraticStrong.derivedQuadratic c
    ; normalizedQuadratic = CFQS.uniqueUpToScaleWitness c
    ; signature31Theorem = canonicalSignature31Theorem
    ; signature31Value = CTI.sig31
    ; signatureForced31 = refl
    }

record CanonicalContractionQuadraticStability : Setω where
  field
    strengthenedSource : CFQS.ContractionForcesQuadraticStrong
  theoremSurface : ContractionForcesQuadraticTheorem
  theoremSurface = fromStrongContraction strengthenedSource
  field
    quadraticTransportStable :
      ∀ x →
        QF.QuadraticForm.Q
          (ContractionForcesQuadraticTheorem.derivedQuadratic theoremSurface) x
        ≡
        QF.QuadraticForm.Q
          (CFQS.ContractionForcesQuadraticStrong.derivedQuadratic strengthenedSource) x
    canonicalNormalizationStable :
      ∀ x →
        QF.QuadraticForm.Q
          (ContractionForcesQuadraticTheorem.derivedQuadratic theoremSurface) x
        ≡
        QP.Q̂core x

canonicalContractionQuadraticStability :
  CanonicalContractionQuadraticStability
canonicalContractionQuadraticStability =
  let
    strong = CFQS.canonicalNontrivialInvariantStrong
  in
  record
    { strengthenedSource = strong
    ; quadraticTransportStable = λ _ → refl
    ; canonicalNormalizationStable = λ x -> CFQS.uniqueUpToScaleWitness strong x
    }

canonicalContractionForcesQuadraticTheorem :
  (m : Nat) → ContractionForcesQuadraticTheorem
canonicalContractionForcesQuadraticTheorem m =
  let
    proj = QES.PDzero {m}
    pkg = PDSP.projectionDefectParallelogramFromSplit {m}
    q =
      proj₁
        (PDP.quadraticFromProjectionDefect
           (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ pkg)
  in
  record
    { dimension = m
    ; projection = proj
    ; projectionParallelogram = pkg
    ; derivedQuadratic = q
    ; normalizedQuadratic = λ _ → refl
    ; signature31Theorem = canonicalSignature31Theorem
    ; signature31Value = CTI.sig31
    ; signatureForced31 = refl
    }

canonicalOutputAgreement :
  (t : ContractionForcesQuadraticTheorem) →
  (q′ :
    QF.QuadraticForm
      (QES.AdditiveVecℤ
        {ContractionForcesQuadraticTheorem.dimension t})
      QES.ScalarFieldℤ) →
  CFQS.UniqueUpToScaleSeam
    (ContractionForcesQuadraticTheorem.dimension t) q′ →
  ∀ x →
    QF.QuadraticForm.Q
      (ContractionForcesQuadraticTheorem.derivedQuadratic t)
      x
    ≡
    QF.QuadraticForm.Q q′ x
canonicalOutputAgreement t q′ uniq′ x =
  trans
    (ContractionForcesQuadraticTheorem.normalizedQuadratic t x)
    (sym (CFQS.UniqueUpToScaleSeam.normalizeToQ̂core uniq′ x))

canonicalRealStackContractionForcesQuadraticTheorem :
  ContractionForcesQuadraticTheorem
canonicalRealStackContractionForcesQuadraticTheorem =
  CanonicalContractionQuadraticStability.theoremSurface
    canonicalContractionQuadraticStability
