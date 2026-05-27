module DASHI.Physics.Closure.CKMCarrierDerived where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CKMExactWitnesses as Exact
import DASHI.Physics.Closure.CKMUnitarityFromCarrier as CKMU
import DASHI.Physics.Closure.MatterRepresentationReceiptSurface as Matter
import DASHI.Physics.YM.BiunitaryDiagonalization as Biunitary

------------------------------------------------------------------------
-- Carrier-derived CKM construction.
--
-- The repository does not expose a general dagger or matrix multiplication
-- operator on `Matter.MixingMatrix`.  What it does expose is a concrete
-- 3x3 carrier, exact diagonal Yukawa witnesses, and exact identity
-- biunitary witnesses.  This module consumes those concrete witnesses and
-- records the canonical carrier CKM construction on the repo's matrix
-- carrier: the diagonalizers are identity, so the carrier CKM collapses to
-- the concrete identity matrix.

upYukawaMatrix : Matter.MixingMatrix
upYukawaMatrix = Exact.DiagonalYukawa3x3.matrix Exact.canonicalUpYukawa3x3

downYukawaMatrix : Matter.MixingMatrix
downYukawaMatrix = Exact.DiagonalYukawa3x3.matrix Exact.canonicalDownYukawa3x3

u_u : Matter.MixingMatrix
u_u = Matter.identityMixingMatrix

u_d : Matter.MixingMatrix
u_d = Matter.identityMixingMatrix

V_CKM : Matter.MixingMatrix
V_CKM = Matter.leftIdentityMixingProduct u_d

record CKMCarrierDerivedReceipt : Setω where
  field
    exactWitnessChain :
      Exact.CKMExactWitnessChain

    yukawaUpMatrix :
      Matter.MixingMatrix

    yukawaDownMatrix :
      Matter.MixingMatrix

    biunitaryDiagonalizationWitness :
      Biunitary.DiagonalBiunitaryWitness

    upDiagonalizer :
      Matter.MixingMatrix

    downDiagonalizer :
      Matter.MixingMatrix

    upDiagonalizerIsIdentity :
      upDiagonalizer ≡ Matter.identityMixingMatrix

    downDiagonalizerIsIdentity :
      downDiagonalizer ≡ Matter.identityMixingMatrix

    ckmCarrierMatrix :
      Matter.MixingMatrix

    ckmCarrierMatrixIsDerived :
      ckmCarrierMatrix ≡ Matter.identityMixingMatrix

    carrierMixingTheoremWitness :
      Exact.CarrierMixingTheoremWitness

    carrierMixingMatrixAgrees :
      ckmCarrierMatrix
      ≡
      Exact.carrierMixingMatrix carrierMixingTheoremWitness

    carrierUnitarityReceipt :
      CKMU.CKMUnitaryReceipt

    carrierUnitarityMatrixAgrees :
      ckmCarrierMatrix
      ≡
      CKMU.carrierCKMMatrix carrierUnitarityReceipt

    splittingFieldEigenbasisLedger :
      Exact.CKMSplittingFieldEigenbasisFailClosedLedger

    splittingFieldStillBlocked :
      Exact.splittingFieldConstructed splittingFieldEigenbasisLedger
      ≡
      false

    eigenbasisStillBlocked :
      Exact.eigenbasisConstructed splittingFieldEigenbasisLedger
      ≡
      false

    carrierDerivedBoundary :
      List String

open CKMCarrierDerivedReceipt public

canonicalCKMCarrierDerived : CKMCarrierDerivedReceipt
canonicalCKMCarrierDerived = record
  { exactWitnessChain = Exact.canonicalCKMExactWitnessChain
  ; yukawaUpMatrix = upYukawaMatrix
  ; yukawaDownMatrix = downYukawaMatrix
  ; biunitaryDiagonalizationWitness =
      Biunitary.canonicalDiagonalBiunitaryWitness
  ; upDiagonalizer = u_u
  ; downDiagonalizer = u_d
  ; upDiagonalizerIsIdentity = refl
  ; downDiagonalizerIsIdentity = refl
  ; ckmCarrierMatrix = V_CKM
  ; ckmCarrierMatrixIsDerived = refl
  ; carrierMixingTheoremWitness =
      Exact.canonicalCarrierMixingTheoremWitness
  ; carrierMixingMatrixAgrees = refl
  ; carrierUnitarityReceipt = CKMU.canonicalCKMUnitary
  ; carrierUnitarityMatrixAgrees = refl
  ; splittingFieldEigenbasisLedger =
      Exact.canonicalCKMSplittingFieldEigenbasisFailClosedLedger
  ; splittingFieldStillBlocked = refl
  ; eigenbasisStillBlocked = refl
  ; carrierDerivedBoundary =
      "The canonical up and down Yukawa matrices are read from the exact witness chain"
      ∷ "The biunitary lane is the concrete diagonal identity witness already present in the repo"
      ∷ "The carrier CKM construction collapses to the concrete identity matrix on the repo's matrix carrier"
      ∷ "Generic splitting-field and non-diagonal eigenbasis construction remains fail-closed upstream"
      ∷ []
  }

canonicalCKMCarrierDerivedAgreesWithUnitarityReceipt :
  ckmCarrierMatrix canonicalCKMCarrierDerived
  ≡
  CKMU.carrierCKMMatrix (carrierUnitarityReceipt canonicalCKMCarrierDerived)
canonicalCKMCarrierDerivedAgreesWithUnitarityReceipt =
  refl
