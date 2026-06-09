module DASHI.Physics.YM.BiunitaryDiagonalization where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.MatterRepresentationReceiptSurface as Matter

------------------------------------------------------------------------
-- Concrete biunitary diagonalization helper for the diagonal CKM/Yukawa lane.
--
-- The repository does not expose a generic matrix multiplication or dagger
-- operator for arbitrary Yukawa matrices here.  What it does expose is a
-- concrete 3x3 `Matter.MixingMatrix`, the canonical identity matrix, and a
-- definitional left-identity product.  That is enough to give a real helper
-- for the diagonal case: the diagonal carrier is the identity matrix, and the
-- left-unitary product closes by `refl`.

record DiagonalBiunitaryWitness : Set where
  field
    diagonalMatrix : Matter.MixingMatrix
    leftDiagonalizer : Matter.MixingMatrix
    diagonalMatrixIsIdentity : diagonalMatrix ≡ Matter.identityMixingMatrix
    leftDiagonalizerIsIdentity : leftDiagonalizer ≡ Matter.identityMixingMatrix
    leftIdentityProductClosed :
      Matter.leftIdentityMixingProduct diagonalMatrix ≡ diagonalMatrix
    canonicalIdentityProductClosed :
      Matter.leftIdentityMixingProduct Matter.identityMixingMatrix
      ≡
      Matter.identityMixingMatrix

open DiagonalBiunitaryWitness public

canonicalDiagonalBiunitaryWitness : DiagonalBiunitaryWitness
canonicalDiagonalBiunitaryWitness = record
  { diagonalMatrix = Matter.identityMixingMatrix
  ; leftDiagonalizer = Matter.identityMixingMatrix
  ; diagonalMatrixIsIdentity = refl
  ; leftDiagonalizerIsIdentity = refl
  ; leftIdentityProductClosed = refl
  ; canonicalIdentityProductClosed = refl
  }

------------------------------------------------------------------------
-- Explicit helper lemmas for the diagonal identity case.

identityDiagonalizationMatrix : Matter.MixingMatrix
identityDiagonalizationMatrix = Matter.identityMixingMatrix

identityDiagonalizationMatrixIsIdentity :
  identityDiagonalizationMatrix ≡ Matter.identityMixingMatrix
identityDiagonalizationMatrixIsIdentity = refl

identityLeftProductClosure :
  Matter.leftIdentityMixingProduct identityDiagonalizationMatrix
  ≡
  identityDiagonalizationMatrix
identityLeftProductClosure = refl

identityProductWitness :
  Matter.leftIdentityMixingProduct Matter.identityMixingMatrix
  ≡
  Matter.identityMixingMatrix
identityProductWitness = refl

------------------------------------------------------------------------
-- Exact blocker status for this helper module.
--
-- This helper closes the diagonal identity case only.  The first genuine
-- open CKM hole in the repo remains the exact product/residual lane on the
-- concrete non-identity datum, namely:
--   * missingCKMProductClosureWitness
--   * missingUnitarityResidualWitness
-- in `DASHI/Physics/Closure/CKMEntryField.agda`.

data BiunitaryDiagonalizationBlocker : Set where
  exactDiagonalIdentityCaseClosed :
    BiunitaryDiagonalizationBlocker

  exactGeneralCKMYukawaDiagonalizationStillOpen :
    BiunitaryDiagonalizationBlocker

biunitaryDiagonalizationBlockerStatus :
  BiunitaryDiagonalizationBlocker
biunitaryDiagonalizationBlockerStatus =
  exactDiagonalIdentityCaseClosed

