module DASHI.Physics.QFT.NeutrinoExistingSUN3CarrierWeldExact where

------------------------------------------------------------------------
-- EXACT LEPTONIC Q(zeta) -> PRE-EXISTING YANG-MILLS SU3 GROUP.
--
-- OWNERS:
--   SUNMatrixCarrier.CertifiedSUNMatrixTheory (matrix Group)
--   SU3MatrixInstance.su3MatrixGroup (N=3)
--   NeutrinoHornedSU3RootExact (ACTUAL CP-nonzero lepton matrices).
--
-- NEW: Derive, do not assume, IsSpecialUnitary for BOTH A=TS1
-- and charged T, plus T³=I at the canonical group level,
-- transporting 18+18+9 EXACT finite pointwise cyclotomic proofs
-- along one explicit finite-matrix and function-equality interface.
--
-- No independent SU3 group model is created, and importantly the
-- lepton flavour representation is NOT physical QCD colour SU3
-- just because the abstract Lie groups are both SU(3).
--
-- OPEN STANDARD AUTHORITY: universal 3x3 finite complex matrix
-- laws (CertifiedSUNMatrixTheory), interpretation/operation
-- compatibility, and extensionality for *function-backed* 3x3
-- matrices. The source owners' pointwise Agda proof clauses
-- do not alone derive a function equality by refl.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
import DASHI.Physics.YangMills.CompactLieGroupCore as Core
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.SU3MatrixInstance as SU3
import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C
import DASHI.Physics.QFT.NeutrinoThreeFlavourFiniteExact as Flavour
import DASHI.Physics.QFT.NeutrinoHornedSU3RootExact as Lepton

Lepton3Matrix : Set
Lepton3Matrix = Flavour.Flavour → Flavour.Flavour → C.Cyclotomic3

record ExactLeptonSUN3Weld : Set₂ where
  field
    matrixTheory :
      SUN.CertifiedSUNMatrixTheory 3 Lepton3Matrix C.Cyclotomic3

    -- The only genuinely imported equality authority needed for
    -- intensional Agda functions as a 3x3 matrix representation.
    functionMatrixExt :
      {A B : Lepton3Matrix} →
      (∀ a b → A a b ≡ B a b) → A ≡ B

    identityMatches :
      SUN.identityM (SUN.operations matrixTheory) ≡
        Lepton.kronecker

    multiplyMatches : (A B : Lepton3Matrix) →
      SUN.multiplyM (SUN.operations matrixTheory) A B
        ≡ Lepton.productMatrix A B

    daggerMatches : (A : Lepton3Matrix) →
      SUN.daggerM (SUN.operations matrixTheory) A
        ≡ (λ a b → C.conjugate (A b a))

    determinantMatches : (A : Lepton3Matrix) →
      SUN.determinant (SUN.operations matrixTheory) A
        ≡ Lepton.determinant3 A

    oneMatches :
      SUN.oneC (SUN.operations matrixTheory) ≡ C.one

open ExactLeptonSUN3Weld public

rawRootLeftUnitary :
  (source : ExactLeptonSUN3Weld) →
  SUN.multiplyM (SUN.operations (matrixTheory source))
    (SUN.daggerM (SUN.operations (matrixTheory source))
      Lepton.selectedTS)
    Lepton.selectedTS
    ≡ SUN.identityM (SUN.operations (matrixTheory source))
rawRootLeftUnitary source =
  trans
    (cong
      (λ A → SUN.multiplyM (SUN.operations (matrixTheory source))
        A Lepton.selectedTS)
      (daggerMatches source Lepton.selectedTS))
    (trans
      (multiplyMatches source Lepton.adjointTS Lepton.selectedTS)
      (trans
        (functionMatrixExt source Lepton.selectedTSUnitaryLeft)
        (sym (identityMatches source))))

rawRootRightUnitary :
  (source : ExactLeptonSUN3Weld) →
  SUN.multiplyM (SUN.operations (matrixTheory source))
    Lepton.selectedTS
    (SUN.daggerM (SUN.operations (matrixTheory source))
      Lepton.selectedTS)
    ≡ SUN.identityM (SUN.operations (matrixTheory source))
rawRootRightUnitary source =
  trans
    (cong
      (SUN.multiplyM (SUN.operations (matrixTheory source))
        Lepton.selectedTS)
      (daggerMatches source Lepton.selectedTS))
    (trans
      (multiplyMatches source Lepton.selectedTS Lepton.adjointTS)
      (trans
        (functionMatrixExt source Lepton.selectedTSUnitaryRight)
        (sym (identityMatches source))))

rawRootDeterminant :
  (source : ExactLeptonSUN3Weld) →
  SUN.determinant (SUN.operations (matrixTheory source))
    Lepton.selectedTS
    ≡ SUN.oneC (SUN.operations (matrixTheory source))
rawRootDeterminant source =
  trans
    (determinantMatches source Lepton.selectedTS)
    (trans
      Lepton.selectedTSDeterminantOne
      (sym (oneMatches source)))

rootSpecial :
  (source : ExactLeptonSUN3Weld) →
  SUN.IsSpecialUnitary (SUN.operations (matrixTheory source))
    Lepton.selectedTS
rootSpecial source = record
  { unitaryLeft = rawRootLeftUnitary source
  ; unitaryRight = rawRootRightUnitary source
  ; specialDeterminant =
      record { determinantOne = rawRootDeterminant source }
  }

rawRotationLeftUnitary :
  (source : ExactLeptonSUN3Weld) →
  SUN.multiplyM (SUN.operations (matrixTheory source))
    (SUN.daggerM (SUN.operations (matrixTheory source))
      Lepton.chargedRotationT)
    Lepton.chargedRotationT
    ≡ SUN.identityM (SUN.operations (matrixTheory source))
rawRotationLeftUnitary source =
  trans
    (cong
      (λ A → SUN.multiplyM (SUN.operations (matrixTheory source))
        A Lepton.chargedRotationT)
      (daggerMatches source Lepton.chargedRotationT))
    (trans
      (multiplyMatches source
        Lepton.chargedRotationTAdjoint Lepton.chargedRotationT)
      (trans
        (functionMatrixExt source Lepton.chargedRotationUnitaryLeft)
        (sym (identityMatches source))))

rawRotationRightUnitary :
  (source : ExactLeptonSUN3Weld) →
  SUN.multiplyM (SUN.operations (matrixTheory source))
    Lepton.chargedRotationT
    (SUN.daggerM (SUN.operations (matrixTheory source))
      Lepton.chargedRotationT)
    ≡ SUN.identityM (SUN.operations (matrixTheory source))
rawRotationRightUnitary source =
  trans
    (cong
      (SUN.multiplyM (SUN.operations (matrixTheory source))
        Lepton.chargedRotationT)
      (daggerMatches source Lepton.chargedRotationT))
    (trans
      (multiplyMatches source
        Lepton.chargedRotationT Lepton.chargedRotationTAdjoint)
      (trans
        (functionMatrixExt source Lepton.chargedRotationUnitaryRight)
        (sym (identityMatches source))))

rawRotationDeterminant :
  (source : ExactLeptonSUN3Weld) →
  SUN.determinant (SUN.operations (matrixTheory source))
    Lepton.chargedRotationT
    ≡ SUN.oneC (SUN.operations (matrixTheory source))
rawRotationDeterminant source =
  trans
    (determinantMatches source Lepton.chargedRotationT)
    (trans
      Lepton.chargedRotationSpecialDeterminant
      (sym (oneMatches source)))

chargedRotationSpecial :
  (source : ExactLeptonSUN3Weld) →
  SUN.IsSpecialUnitary (SUN.operations (matrixTheory source))
    Lepton.chargedRotationT
chargedRotationSpecial source = record
  { unitaryLeft = rawRotationLeftUnitary source
  ; unitaryRight = rawRotationRightUnitary source
  ; specialDeterminant =
      record { determinantOne = rawRotationDeterminant source }
  }

rawRotationCube :
  (source : ExactLeptonSUN3Weld) →
  SUN.multiplyM (SUN.operations (matrixTheory source))
    (SUN.multiplyM (SUN.operations (matrixTheory source))
      Lepton.chargedRotationT Lepton.chargedRotationT)
    Lepton.chargedRotationT
    ≡ SUN.identityM (SUN.operations (matrixTheory source))
rawRotationCube source =
  trans
    (SUN.multiplyAssociative (matrixTheory source)
      Lepton.chargedRotationT
      Lepton.chargedRotationT
      Lepton.chargedRotationT)
    (trans
      (cong
        (SUN.multiplyM (SUN.operations (matrixTheory source))
          Lepton.chargedRotationT)
        (multiplyMatches source
          Lepton.chargedRotationT Lepton.chargedRotationT))
      (trans
        (multiplyMatches source
          Lepton.chargedRotationT
          (Lepton.productMatrix
            Lepton.chargedRotationT Lepton.chargedRotationT))
        (trans
          (functionMatrixExt source Lepton.chargedRotationCubeIsIdentity)
          (sym (identityMatches source)))))

sameSU3Group :
  (source : ExactLeptonSUN3Weld) →
  Core.Group (SUN.SUNMatrixElement (matrixTheory source))
sameSU3Group source =
  SU3.su3MatrixGroup (matrixTheory source)

leptonicRootAsExistingSU3 :
  (source : ExactLeptonSUN3Weld) →
  SUN.SUNMatrixElement (matrixTheory source)
leptonicRootAsExistingSU3 source =
  SUN.sunMatrix Lepton.selectedTS (rootSpecial source)

chargedRotationAsExistingSU3 :
  (source : ExactLeptonSUN3Weld) →
  SUN.SUNMatrixElement (matrixTheory source)
chargedRotationAsExistingSU3 source =
  SUN.sunMatrix Lepton.chargedRotationT
    (chargedRotationSpecial source)

-- Actual element-order law for the same Yang–Mills SU3 Group subtype.
-- Downstream PR #1244 can use this as generatorCubed and derive the
-- C3 inner action without assuming an unrelated Ad³ axiom.
chargedRotationHasOrderDividingThree :
  (source : ExactLeptonSUN3Weld) →
  Core.multiply (sameSU3Group source)
    (Core.multiply (sameSU3Group source)
      (chargedRotationAsExistingSU3 source)
      (chargedRotationAsExistingSU3 source))
    (chargedRotationAsExistingSU3 source)
    ≡ Core.identity (sameSU3Group source)
chargedRotationHasOrderDividingThree source =
  SUN.sunMatrixExt (rawRotationCube source)

-- The matrix Theory and pointwise equality compatibility remain
-- typed, explicit UNRESOLVED imports. This theorem does not claim
-- global finite-matrix algebra or Gotô surjectivity kernel-checked.
