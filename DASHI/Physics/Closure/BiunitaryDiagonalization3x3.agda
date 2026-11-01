module DASHI.Physics.Closure.BiunitaryDiagonalization3x3 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.MatterRepresentationReceiptSurface as Matter
import DASHI.Physics.Closure.CKMEntryField as Field
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

record ConcreteBiunitaryDiagonalization3x3 : Set where
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

record BiunitaryDiagonalization3x3Receipt : Set where
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

------------------------------------------------------------------------
-- First non-identity transport socket.
--
-- The exact carrier diagonalization above remains the identity case.  The
-- socket below is deliberately separate: it records a finite Cabibbo-like
-- down-sector transport already present in the concrete `Matter.MixingMatrix`
-- carrier, while keeping the exact physical CKM promotion closed.

record CabibboLikeDownTransportSocket : Set where
  field
    upTransport :
      Matter.MixingMatrix

    upTransportIsIdentity :
      upTransport ≡ Matter.identityMixingMatrix

    downTransport :
      Matter.MixingMatrix

    downTransportIsCanonicalWolfenstein :
      downTransport ≡ Matter.canonicalWolfensteinMixingMatrix

    carrierProduct :
      Matter.MixingMatrix

    carrierProductIsLeftIdentityTransport :
      carrierProduct ≡ Matter.leftIdentityMixingProduct downTransport

    carrierProductIsDownTransport :
      carrierProduct ≡ downTransport

    identityVusEntry :
      Matter.MixingGaussianRationalDatum

    identityVusEntryIsZero :
      identityVusEntry ≡ Matter.zeroMixingGaussianRationalDatum

    cabibboLikeVusEntry :
      Matter.MixingGaussianRationalDatum

    cabibboLikeVusEntryIsOneFifth :
      cabibboLikeVusEntry
      ≡
      Matter.mixingGaussianRationalDatum
        Matter.oneFifthMixingSignedRationalDatum
        Matter.zeroMixingSignedRationalDatum

    distinguishesIdentityCarrier :
      Bool

    distinguishesIdentityCarrierIsTrue :
      distinguishesIdentityCarrier ≡ true

    exactVVdaggerResidualReceipt :
      Field.CKMMatterMixingMatrixExactVVdaggerResidualReceipt

    residualSourceIsCarrierProduct :
      Field.sourceMatrix exactVVdaggerResidualReceipt ≡ carrierProduct

    residual11IsNonzeroTarget :
      Matter.v11
        (Field.vvDaggerMinusIdentityResidual exactVVdaggerResidualReceipt)
      ≡
      Matter.mixingGaussianRationalDatum
        Matter.thirtySevenNinetyThousandMixingSignedRationalDatum
        Matter.zeroMixingSignedRationalDatum

    exactUnitarityRejected :
      Field.exactUnitarityForConcreteWolfenstein exactVVdaggerResidualReceipt
      ≡
      false

    exactPDGMatchClaimed :
      Bool

    exactPDGMatchClaimedIsFalse :
      exactPDGMatchClaimed ≡ false

    physicalCKMPromotionConstructed :
      Bool

    physicalCKMPromotionConstructedIsFalse :
      physicalCKMPromotionConstructed ≡ false

    socketBoundary :
      List String

open CabibboLikeDownTransportSocket public

canonicalCabibboLikeDownTransportSocket :
  CabibboLikeDownTransportSocket
canonicalCabibboLikeDownTransportSocket = record
  { upTransport =
      Matter.identityMixingMatrix
  ; upTransportIsIdentity =
      refl
  ; downTransport =
      Matter.canonicalWolfensteinMixingMatrix
  ; downTransportIsCanonicalWolfenstein =
      refl
  ; carrierProduct =
      Matter.canonicalWolfensteinMixingMatrix
  ; carrierProductIsLeftIdentityTransport =
      refl
  ; carrierProductIsDownTransport =
      refl
  ; identityVusEntry =
      Matter.v12 Matter.identityMixingMatrix
  ; identityVusEntryIsZero =
      refl
  ; cabibboLikeVusEntry =
      Matter.v12 Matter.canonicalWolfensteinMixingMatrix
  ; cabibboLikeVusEntryIsOneFifth =
      refl
  ; distinguishesIdentityCarrier =
      true
  ; distinguishesIdentityCarrierIsTrue =
      refl
  ; exactVVdaggerResidualReceipt =
      Field.canonicalCKMMatterMixingMatrixExactVVdaggerResidualReceipt
  ; residualSourceIsCarrierProduct =
      refl
  ; residual11IsNonzeroTarget =
      refl
  ; exactUnitarityRejected =
      refl
  ; exactPDGMatchClaimed =
      false
  ; exactPDGMatchClaimedIsFalse =
      refl
  ; physicalCKMPromotionConstructed =
      false
  ; physicalCKMPromotionConstructedIsFalse =
      refl
  ; socketBoundary =
      "The exact biunitary carrier remains the identity diagonalization"
      ∷ "The non-identity frontier socket uses identity up transport and canonical Wolfenstein down transport"
      ∷ "The resulting finite carrier product has V_us = 1/5, while the identity carrier has V_us = 0"
      ∷ "The socket consumes the exact finite V V^dagger - I residual receipt, including nonzero residual11 = 37/90000"
      ∷ "This distinguishes identity from a Cabibbo-like transport without claiming an exact PDG match or physical CKM promotion"
      ∷ []
  }

cabibboLikeSocketVusIsOneFifth :
  cabibboLikeVusEntry canonicalCabibboLikeDownTransportSocket
  ≡
  Matter.mixingGaussianRationalDatum
    Matter.oneFifthMixingSignedRationalDatum
    Matter.zeroMixingSignedRationalDatum
cabibboLikeSocketVusIsOneFifth =
  refl

cabibboLikeSocketRejectsExactUnitarity :
  Field.exactUnitarityForConcreteWolfenstein
    (exactVVdaggerResidualReceipt canonicalCabibboLikeDownTransportSocket)
  ≡
  false
cabibboLikeSocketRejectsExactUnitarity =
  refl

cabibboLikeSocketDoesNotPromotePhysicalCKM :
  physicalCKMPromotionConstructed canonicalCabibboLikeDownTransportSocket
  ≡
  false
cabibboLikeSocketDoesNotPromotePhysicalCKM =
  refl
