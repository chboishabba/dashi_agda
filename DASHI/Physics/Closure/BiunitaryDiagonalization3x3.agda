module DASHI.Physics.Closure.BiunitaryDiagonalization3x3 where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.MatterRepresentationReceiptSurface as Matter
import DASHI.Physics.Closure.CKMExactWitnesses as Exact
open import DASHI.Physics.YM.BiunitaryDiagonalization
  using (DiagonalBiunitaryWitness; canonicalDiagonalBiunitaryWitness)

------------------------------------------------------------------------
-- Concrete biunitary diagonalization for the actual 3x3 Yukawa matrices
-- already packaged in the repository.
--
-- The upstream CKM witness layer already supplies the concrete diagonal
-- Yukawa matrices.  This module packages those exact inputs into a
-- self-contained biunitary diagonalization surface for Gate 7:
--   * the up and down diagonal Yukawas are the concrete repository matrices;
--   * the diagonalizer is the identity matrix;
--   * the exact diagonalization carrier is inherited from the existing
--     diagonal identity witness in `DASHI.Physics.YM.BiunitaryDiagonalization`.

record ConcreteBiunitaryDiagonalization3x3 : Setω where
  field
    yukawa : Exact.DiagonalYukawa3x3

    diagonalizer : Matter.MixingMatrix

    yukawaMatrixIsDiagonal :
      Exact.DiagonalYukawa3x3.matrix yukawa
      ≡
      Exact.diag3
        (Exact.DiagonalYukawa3x3.y11 yukawa)
        (Exact.DiagonalYukawa3x3.y22 yukawa)
        (Exact.DiagonalYukawa3x3.y33 yukawa)

    diagonalizerIsIdentity :
      diagonalizer ≡ Matter.identityMixingMatrix

    leftIdentityClosure :
      Matter.leftIdentityMixingProduct diagonalizer ≡ diagonalizer

    biunitaryCarrier :
      DiagonalBiunitaryWitness

    diagonalizationNotes :
      List String

open ConcreteBiunitaryDiagonalization3x3 public

canonicalUpBiunitaryDiagonalizationWitness :
  ConcreteBiunitaryDiagonalization3x3
canonicalUpBiunitaryDiagonalizationWitness = record
  { yukawa = Exact.canonicalUpYukawa3x3
  ; diagonalizer = Matter.identityMixingMatrix
  ; yukawaMatrixIsDiagonal =
      Exact.DiagonalYukawa3x3.matrixIsDiagonal Exact.canonicalUpYukawa3x3
  ; diagonalizerIsIdentity = refl
  ; leftIdentityClosure = refl
  ; biunitaryCarrier = canonicalDiagonalBiunitaryWitness
  ; diagonalizationNotes =
      "Concrete up-sector 3x3 Yukawa matrix"
      ∷ "The diagonalizer is the identity matrix already present in the repo"
      ∷ "The exact biunitary carrier is the existing diagonal identity witness"
      ∷ []
  }

canonicalDownBiunitaryDiagonalizationWitness :
  ConcreteBiunitaryDiagonalization3x3
canonicalDownBiunitaryDiagonalizationWitness = record
  { yukawa = Exact.canonicalDownYukawa3x3
  ; diagonalizer = Matter.identityMixingMatrix
  ; yukawaMatrixIsDiagonal =
      Exact.DiagonalYukawa3x3.matrixIsDiagonal Exact.canonicalDownYukawa3x3
  ; diagonalizerIsIdentity = refl
  ; leftIdentityClosure = refl
  ; biunitaryCarrier = canonicalDiagonalBiunitaryWitness
  ; diagonalizationNotes =
      "Concrete down-sector 3x3 Yukawa matrix"
      ∷ "The diagonalizer is the identity matrix already present in the repo"
      ∷ "The exact biunitary carrier is the existing diagonal identity witness"
      ∷ []
  }

------------------------------------------------------------------------
-- Helper lemmas for Gate 7 consumers.

canonicalUpYukawaMatrixIsDiagonal :
  Exact.DiagonalYukawa3x3.matrix
    (ConcreteBiunitaryDiagonalization3x3.yukawa
      canonicalUpBiunitaryDiagonalizationWitness)
  ≡
  Exact.diag3
    (Exact.DiagonalYukawa3x3.y11
      (ConcreteBiunitaryDiagonalization3x3.yukawa
        canonicalUpBiunitaryDiagonalizationWitness))
    (Exact.DiagonalYukawa3x3.y22
      (ConcreteBiunitaryDiagonalization3x3.yukawa
        canonicalUpBiunitaryDiagonalizationWitness))
    (Exact.DiagonalYukawa3x3.y33
      (ConcreteBiunitaryDiagonalization3x3.yukawa
        canonicalUpBiunitaryDiagonalizationWitness))
canonicalUpYukawaMatrixIsDiagonal =
  ConcreteBiunitaryDiagonalization3x3.yukawaMatrixIsDiagonal
    canonicalUpBiunitaryDiagonalizationWitness

canonicalDownYukawaMatrixIsDiagonal :
  Exact.DiagonalYukawa3x3.matrix
    (ConcreteBiunitaryDiagonalization3x3.yukawa
      canonicalDownBiunitaryDiagonalizationWitness)
  ≡
  Exact.diag3
    (Exact.DiagonalYukawa3x3.y11
      (ConcreteBiunitaryDiagonalization3x3.yukawa
        canonicalDownBiunitaryDiagonalizationWitness))
    (Exact.DiagonalYukawa3x3.y22
      (ConcreteBiunitaryDiagonalization3x3.yukawa
        canonicalDownBiunitaryDiagonalizationWitness))
    (Exact.DiagonalYukawa3x3.y33
      (ConcreteBiunitaryDiagonalization3x3.yukawa
        canonicalDownBiunitaryDiagonalizationWitness))
canonicalDownYukawaMatrixIsDiagonal =
  ConcreteBiunitaryDiagonalization3x3.yukawaMatrixIsDiagonal
    canonicalDownBiunitaryDiagonalizationWitness

canonicalUpDiagonalizerIsIdentity :
  ConcreteBiunitaryDiagonalization3x3.diagonalizer
    canonicalUpBiunitaryDiagonalizationWitness
  ≡
  Matter.identityMixingMatrix
canonicalUpDiagonalizerIsIdentity =
  ConcreteBiunitaryDiagonalization3x3.diagonalizerIsIdentity
    canonicalUpBiunitaryDiagonalizationWitness

canonicalDownDiagonalizerIsIdentity :
  ConcreteBiunitaryDiagonalization3x3.diagonalizer
    canonicalDownBiunitaryDiagonalizationWitness
  ≡
  Matter.identityMixingMatrix
canonicalDownDiagonalizerIsIdentity =
  ConcreteBiunitaryDiagonalization3x3.diagonalizerIsIdentity
    canonicalDownBiunitaryDiagonalizationWitness

canonicalUpLeftIdentityClosure :
  Matter.leftIdentityMixingProduct
    (ConcreteBiunitaryDiagonalization3x3.diagonalizer
      canonicalUpBiunitaryDiagonalizationWitness)
  ≡
  ConcreteBiunitaryDiagonalization3x3.diagonalizer
    canonicalUpBiunitaryDiagonalizationWitness
canonicalUpLeftIdentityClosure =
  ConcreteBiunitaryDiagonalization3x3.leftIdentityClosure
    canonicalUpBiunitaryDiagonalizationWitness

canonicalDownLeftIdentityClosure :
  Matter.leftIdentityMixingProduct
    (ConcreteBiunitaryDiagonalization3x3.diagonalizer
      canonicalDownBiunitaryDiagonalizationWitness)
  ≡
  ConcreteBiunitaryDiagonalization3x3.diagonalizer
    canonicalDownBiunitaryDiagonalizationWitness
canonicalDownLeftIdentityClosure =
  ConcreteBiunitaryDiagonalization3x3.leftIdentityClosure
    canonicalDownBiunitaryDiagonalizationWitness

------------------------------------------------------------------------
-- Bundle the actual up/down witnesses for downstream CKM/Gate 7 consumers.

record BiunitaryDiagonalization3x3Receipt : Setω where
  field
    upDiagonalization :
      ConcreteBiunitaryDiagonalization3x3

    downDiagonalization :
      ConcreteBiunitaryDiagonalization3x3

    receiptNotes :
      List String

open BiunitaryDiagonalization3x3Receipt public

canonicalBiunitaryDiagonalization3x3Receipt :
  BiunitaryDiagonalization3x3Receipt
canonicalBiunitaryDiagonalization3x3Receipt = record
  { upDiagonalization = canonicalUpBiunitaryDiagonalizationWitness
  ; downDiagonalization = canonicalDownBiunitaryDiagonalizationWitness
  ; receiptNotes =
      "Gate 7 biunitary diagonalization consumes the concrete up/down Yukawas"
      ∷ "Both diagonalizers are the identity matrix and close by refl"
      ∷ "The diagonalization carrier is the existing exact diagonal witness"
      ∷ []
  }

