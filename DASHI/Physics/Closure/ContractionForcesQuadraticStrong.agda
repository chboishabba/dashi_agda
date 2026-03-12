module DASHI.Physics.Closure.ContractionForcesQuadraticStrong where

-- Assumptions:
-- - projection-defect/parallelogram package on the shift carrier
-- - chosen dynamics map with quadratic invariance witness
-- - uniqueness seam to normalized quadratic core
--
-- Output:
-- - strong contraction=>quadratic package with explicit invariance and
--   uniqueness witnesses.
--
-- Classification:
-- - strong

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)
open import Data.Bool using (true; false)
open import Data.Vec using (_∷_; [])
open import Data.Product using (Σ; proj₁)
open import Data.Unit using (⊤; tt)

open import DASHI.Geometry.ProjectionDefect as PD
open import DASHI.Geometry.QuadraticForm as QF
open import DASHI.Geometry.ProjectionDefectToParallelogram as PDP
open import DASHI.Geometry.ProjectionDefectSplitForcesParallelogram as PDSP
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES
open import DASHI.Physics.QuadraticPolarization as QP
open import DASHI.Physics.Signature31InstanceShiftZ as S31
open import DASHI.Physics.SignedPerm4 as SP

record UniqueUpToScaleSeam
  (m : Nat)
  (q : QF.QuadraticForm (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ) : Setω where
  field
    normalizeToQ̂core :
      ∀ x →
        QF.QuadraticForm.Q q x ≡ QP.Q̂core x

mkUniqueUpToScaleSeam :
  ∀ {m q} →
  (∀ x → QF.QuadraticForm.Q q x ≡ QP.Q̂core x) →
  UniqueUpToScaleSeam m q
mkUniqueUpToScaleSeam f = record { normalizeToQ̂core = f }

record QuadraticUniquenessBridge
  (m : Nat)
  (q : QF.QuadraticForm (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ) : Setω where
  field
    referenceQuadratic :
      QF.QuadraticForm (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ
    invariantMatchesReference :
      ∀ x →
        QF.QuadraticForm.Q q x
        ≡
        QF.QuadraticForm.Q referenceQuadratic x
    uniqueness :
      UniqueUpToScaleSeam m referenceQuadratic

mkQuadraticUniquenessBridge :
  ∀ {m}
  (q : QF.QuadraticForm (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ) →
  (∀ x → QF.QuadraticForm.Q q x ≡ QF.QuadraticForm.Q q x) →
  (∀ x → QF.QuadraticForm.Q q x ≡ QP.Q̂core x) →
  QuadraticUniquenessBridge m q
mkQuadraticUniquenessBridge q matches uniqueness =
  record
    { referenceQuadratic = q
    ; invariantMatchesReference = matches
    ; uniqueness = mkUniqueUpToScaleSeam uniqueness
    }

record ContractionForcesQuadraticStrong : Setω where
  field
    dimension : Nat
    projection : PD.ProjectionDefect (QES.AdditiveVecℤ {dimension})
    projectionParallelogram :
      PDP.ProjectionDefectParallelogramPackage
        (QES.AdditiveVecℤ {dimension}) QES.ScalarFieldℤ
    projectionQuadraticWitness :
      PDP.ProjectionDefectQuadraticWitness
        (QES.AdditiveVecℤ {dimension}) QES.ScalarFieldℤ
    derivedQuadratic :
      QF.QuadraticForm (QES.AdditiveVecℤ {dimension}) QES.ScalarFieldℤ
    dynamicsMap :
      PD.Additive.Carrier (QES.AdditiveVecℤ {dimension}) →
      PD.Additive.Carrier (QES.AdditiveVecℤ {dimension})
    invariantUnderT :
      ∀ x →
        QF.QuadraticForm.Q derivedQuadratic (dynamicsMap x)
        ≡
        QF.QuadraticForm.Q derivedQuadratic x
    nondegenerate : ⊤
    compatibleWithIsotropy : ⊤
    quadraticUniquenessBridge :
      QuadraticUniquenessBridge dimension derivedQuadratic

invariantQuadraticWitness :
  (c : ContractionForcesQuadraticStrong) →
  ∀ x →
    QF.QuadraticForm.Q
      (ContractionForcesQuadraticStrong.derivedQuadratic c)
      (ContractionForcesQuadraticStrong.dynamicsMap c x)
    ≡
    QF.QuadraticForm.Q
      (ContractionForcesQuadraticStrong.derivedQuadratic c)
      x
invariantQuadraticWitness c =
  ContractionForcesQuadraticStrong.invariantUnderT c

uniqueUpToScaleWitness :
  (c : ContractionForcesQuadraticStrong) →
  ∀ x →
    QF.QuadraticForm.Q
      (ContractionForcesQuadraticStrong.derivedQuadratic c) x
    ≡
    QP.Q̂core x
uniqueUpToScaleWitness c x =
  trans
    (QuadraticUniquenessBridge.invariantMatchesReference
      (ContractionForcesQuadraticStrong.quadraticUniquenessBridge c) x)
    (UniqueUpToScaleSeam.normalizeToQ̂core
      (QuadraticUniquenessBridge.uniqueness
        (ContractionForcesQuadraticStrong.quadraticUniquenessBridge c))
      x)

-- Canonicality lemma: if an alternative admissible quadratic presentation is
-- also normalized to Q^core on the same carrier, it agrees pointwise with the
-- canonical strong output.
canonicalQuadraticAgreement :
  (c : ContractionForcesQuadraticStrong) →
  (q′ :
    QF.QuadraticForm
      (QES.AdditiveVecℤ
        {ContractionForcesQuadraticStrong.dimension c})
      QES.ScalarFieldℤ) →
  UniqueUpToScaleSeam
    (ContractionForcesQuadraticStrong.dimension c) q′ →
  ∀ x →
    QF.QuadraticForm.Q
      (ContractionForcesQuadraticStrong.derivedQuadratic c)
      x
    ≡
    QF.QuadraticForm.Q q′ x
canonicalQuadraticAgreement c q′ uniq′ x =
  trans
    (uniqueUpToScaleWitness c x)
    (sym (UniqueUpToScaleSeam.normalizeToQ̂core uniq′ x))

canonicalQuadraticAgreementToQ̂core :
  (c : ContractionForcesQuadraticStrong) →
  ∀ x →
    QF.QuadraticForm.Q
      (ContractionForcesQuadraticStrong.derivedQuadratic c)
      x
    ≡ QP.Q̂core x
canonicalQuadraticAgreementToQ̂core c =
  uniqueUpToScaleWitness c

buildContractionForcesQuadraticStrong :
  (m : Nat) →
  (dynamics :
    PD.Additive.Carrier (QES.AdditiveVecℤ {m}) →
    PD.Additive.Carrier (QES.AdditiveVecℤ {m})) →
  (invariantQ :
    ∀ x →
      QF.QuadraticForm.Q
        (proj₁
          (PDP.quadraticFromProjectionDefect
            (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ
            (PDSP.projectionDefectParallelogramFromSplit {m})))
        (dynamics x)
      ≡
      QF.QuadraticForm.Q
        (proj₁
          (PDP.quadraticFromProjectionDefect
            (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ
            (PDSP.projectionDefectParallelogramFromSplit {m})))
        x) →
  (uniqueness :
    ∀ x →
      QF.QuadraticForm.Q
        (proj₁
          (PDP.quadraticFromProjectionDefect
            (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ
            (PDSP.projectionDefectParallelogramFromSplit {m})))
        x
      ≡ QP.Q̂core x) →
  ContractionForcesQuadraticStrong
buildContractionForcesQuadraticStrong m dynamics invariantQ uniqueness =
  let
    proj = QES.PDzero {m}
    pkg = PDSP.projectionDefectParallelogramFromSplit {m}
    q = proj₁
          (PDP.quadraticFromProjectionDefect
             (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ pkg)
  in
  record
    { dimension = m
    ; projection = proj
    ; projectionParallelogram = pkg
    ; projectionQuadraticWitness =
        PDP.fromProjectionPackageWitness
          (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ pkg
    ; derivedQuadratic = q
    ; dynamicsMap = dynamics
    ; invariantUnderT = invariantQ
    ; nondegenerate = tt
    ; compatibleWithIsotropy = tt
    ; quadraticUniquenessBridge =
        mkQuadraticUniquenessBridge q (λ _ → refl) uniqueness
    }

canonicalIdentityInvariantStrong :
  (m : Nat) →
  ContractionForcesQuadraticStrong
canonicalIdentityInvariantStrong m =
  buildContractionForcesQuadraticStrong
    m
    (λ x → x)
    (λ _ → refl)
    (λ _ → refl)

canonicalSignedPerm4InvariantStrong :
  (sp : SP.SignedPerm4) →
  ContractionForcesQuadraticStrong
canonicalSignedPerm4InvariantStrong sp =
  buildContractionForcesQuadraticStrong
    4
    (S31.actIso4 sp)
    (S31.qcore-pres4 sp)
    (λ _ → refl)

nontrivialSignedPerm4 : SP.SignedPerm4
nontrivialSignedPerm4 =
  record
    { perm = SP.p120
    ; flipT = false
    ; flipS = false ∷ true ∷ false ∷ []
    }

canonicalNontrivialInvariantStrong : ContractionForcesQuadraticStrong
canonicalNontrivialInvariantStrong =
  canonicalSignedPerm4InvariantStrong nontrivialSignedPerm4
