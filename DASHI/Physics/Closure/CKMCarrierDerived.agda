module DASHI.Physics.Closure.CKMCarrierDerived where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CKMExactWitnesses as Exact
import DASHI.Physics.Closure.CKMUnitarityFromCarrier as CKMU
import DASHI.Physics.Closure.BiunitaryDiagonalization3x3 as B3
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

downYukawaHermitianProductMatrix : Matter.MixingMatrix
downYukawaHermitianProductMatrix =
  Exact.diag3
    (Exact.exactGaussian 25 6051600000000)
    (Exact.exactGaussian 8649 60516000000)
    (Exact.exactGaussian 17472400 60516000000)

u_u : Matter.MixingMatrix
u_u = Matter.identityMixingMatrix

u_d : Matter.MixingMatrix
u_d = Matter.identityMixingMatrix

uuDagger : Matter.MixingMatrix
uuDagger = Matter.identityMixingMatrix

V_CKM : Matter.MixingMatrix
V_CKM = Matter.leftIdentityMixingProduct u_d

record DownWeakBasisEigenbasisTransport : Setω where
  field
    carrierDownYukawa :
      Exact.DiagonalYukawa3x3

    carrierDownYukawaIsCanonical :
      carrierDownYukawa ≡ Exact.canonicalDownYukawa3x3

    carrierDownYukawaMatrix :
      Matter.MixingMatrix

    carrierDownYukawaMatrixIsCanonical :
      carrierDownYukawaMatrix ≡ downYukawaMatrix

    downHermitianProductCarrier :
      Matter.MixingMatrix

    downHermitianProductCarrierIsCanonicalSquare :
      downHermitianProductCarrier ≡ downYukawaHermitianProductMatrix

    downBiunitaryDiagonalization :
      B3.ConcreteBiunitaryDiagonalization3x3

    U_d :
      Matter.MixingMatrix

    U_dIsIdentity :
      U_d ≡ Matter.identityMixingMatrix

    U_dAgreesWithBiunitaryDiagonalizer :
      U_d
      ≡
      B3.ConcreteBiunitaryDiagonalization3x3.diagonalizer
        downBiunitaryDiagonalization

    U_dUnitaryClosure :
      Matter.leftIdentityMixingProduct U_d ≡ U_d

    U_dDiagonalizesYdYdDagger :
      Matter.leftIdentityMixingProduct downHermitianProductCarrier
      ≡
      downHermitianProductCarrier

    downSectorEigenbasisTransportConstructed :
      Bool

    downSectorEigenbasisTransportConstructedIsTrue :
      downSectorEigenbasisTransportConstructed ≡ true

    transportBoundary :
      List String

open DownWeakBasisEigenbasisTransport public

canonicalDownWeakBasisEigenbasisTransport :
  DownWeakBasisEigenbasisTransport
canonicalDownWeakBasisEigenbasisTransport = record
  { carrierDownYukawa = Exact.canonicalDownYukawa3x3
  ; carrierDownYukawaIsCanonical = refl
  ; carrierDownYukawaMatrix = downYukawaMatrix
  ; carrierDownYukawaMatrixIsCanonical = refl
  ; downHermitianProductCarrier = downYukawaHermitianProductMatrix
  ; downHermitianProductCarrierIsCanonicalSquare = refl
  ; downBiunitaryDiagonalization =
      B3.canonicalDownBiunitaryDiagonalizationWitness
  ; U_d = u_d
  ; U_dIsIdentity = refl
  ; U_dAgreesWithBiunitaryDiagonalizer = refl
  ; U_dUnitaryClosure = refl
  ; U_dDiagonalizesYdYdDagger = refl
  ; downSectorEigenbasisTransportConstructed = true
  ; downSectorEigenbasisTransportConstructedIsTrue = refl
  ; transportBoundary =
      "The down Yukawa carrier is the canonical diagonal 3x3 matrix from CKMExactWitnesses"
      ∷ "Because the canonical down Yukawa is real diagonal, Y_d Y_d^dagger is the squared diagonal carrier matrix"
      ∷ "The down weak-basis eigenbasis transport U_d is the identity matrix"
      ∷ "Identity transport is unitary and leaves the diagonal down-sector Hermitian carrier fixed by refl"
      ∷ []
  }

record CKMWeakBasisProductClosureReceipt : Setω where
  field
    downTransport :
      DownWeakBasisEigenbasisTransport

    upDiagonalizer :
      Matter.MixingMatrix

    upDiagonalizerIsIdentity :
      upDiagonalizer ≡ Matter.identityMixingMatrix

    upDagger :
      Matter.MixingMatrix

    upDaggerIsIdentity :
      upDagger ≡ Matter.identityMixingMatrix

    downDiagonalizer :
      Matter.MixingMatrix

    downDiagonalizerAgreesWithTransport :
      downDiagonalizer ≡ U_d downTransport

    productMatrix :
      Matter.MixingMatrix

    productMatrixIsUuDaggerUd :
      productMatrix
      ≡
      Matter.leftIdentityMixingProduct downDiagonalizer

    productMatrixIsIdentity :
      productMatrix ≡ Matter.identityMixingMatrix

    productClosureWitness :
      Exact.CKMProductClosureWitness

    productClosureMatrixAgrees :
      productMatrix
      ≡
      Exact.ckmMatrix productClosureWitness

    productCloses :
      Matter.leftIdentityMixingProduct productMatrix ≡ productMatrix

    weakBasisCKMProductClosureConstructed :
      Bool

    weakBasisCKMProductClosureConstructedIsTrue :
      weakBasisCKMProductClosureConstructed ≡ true

    productBoundary :
      List String

open CKMWeakBasisProductClosureReceipt public

canonicalCKMWeakBasisProductClosureReceipt :
  CKMWeakBasisProductClosureReceipt
canonicalCKMWeakBasisProductClosureReceipt = record
  { downTransport = canonicalDownWeakBasisEigenbasisTransport
  ; upDiagonalizer = u_u
  ; upDiagonalizerIsIdentity = refl
  ; upDagger = uuDagger
  ; upDaggerIsIdentity = refl
  ; downDiagonalizer = u_d
  ; downDiagonalizerAgreesWithTransport = refl
  ; productMatrix = V_CKM
  ; productMatrixIsUuDaggerUd = refl
  ; productMatrixIsIdentity = refl
  ; productClosureWitness = Exact.canonicalCKMProductClosureWitness
  ; productClosureMatrixAgrees = refl
  ; productCloses = refl
  ; weakBasisCKMProductClosureConstructed = true
  ; weakBasisCKMProductClosureConstructedIsTrue = refl
  ; productBoundary =
      "The up-sector dagger diagonalizer is the identity matrix"
      ∷ "The down-sector transport U_d is the identity matrix supplied by canonicalDownWeakBasisEigenbasisTransport"
      ∷ "The concrete CKM product U_u^dagger * U_d reduces to the identity carrier matrix"
      ∷ "This closes the carrier product only; it does not promote the physical Wolfenstein comparison target"
      ∷ []
  }

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

    downWeakBasisEigenbasisTransport :
      DownWeakBasisEigenbasisTransport

    downDiagonalizerAgreesWithTransport :
      downDiagonalizer
      ≡
      U_d downWeakBasisEigenbasisTransport

    weakBasisProductClosureReceipt :
      CKMWeakBasisProductClosureReceipt

    ckmCarrierMatrix :
      Matter.MixingMatrix

    ckmCarrierMatrixIsDerived :
      ckmCarrierMatrix ≡ Matter.identityMixingMatrix

    ckmCarrierMatrixAgreesWithWeakBasisProduct :
      ckmCarrierMatrix
      ≡
      productMatrix weakBasisProductClosureReceipt

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
  ; downWeakBasisEigenbasisTransport =
      canonicalDownWeakBasisEigenbasisTransport
  ; downDiagonalizerAgreesWithTransport = refl
  ; weakBasisProductClosureReceipt =
      canonicalCKMWeakBasisProductClosureReceipt
  ; ckmCarrierMatrix = V_CKM
  ; ckmCarrierMatrixIsDerived = refl
  ; ckmCarrierMatrixAgreesWithWeakBasisProduct = refl
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
      ∷ "The down weak-basis eigenbasis transport U_d is explicitly inhabited as the identity matrix"
      ∷ "The carrier CKM product U_u^dagger * U_d closes concretely to the identity matrix"
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
