module DASHI.Physics.Closure.YukawaFromCarrier where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CKMCarrierDerived as CKMD
import DASHI.Physics.Closure.CKMExactWitnesses as Exact
import DASHI.Physics.Closure.CKMUnitarityFromCarrier as CKMU
import DASHI.Physics.Closure.HiggsSymmetryBreakingReceipt as Higgs
import DASHI.Physics.Closure.MatterRepresentationReceiptSurface as Matter
import DASHI.Physics.Closure.YukawaDHRIntertwinerCompatibility as YDHR
import DASHI.Physics.YM.FroggattNielsenExpansion as FN

------------------------------------------------------------------------
-- Carrier-derived Yukawa packaging.
--
-- This module does not introduce a new algebraic theory.  It packages the
-- exact 3x3 up/down Yukawa matrices already present in the repository
-- together with the existing FN and Higgs receipts, so downstream Gate 7
-- consumers can read a concrete carrier-side Yukawa surface.

canonicalUpFlavorBasis : List String
canonicalUpFlavorBasis =
  "e_u" ∷ "e_c" ∷ "e_t" ∷ []

canonicalDownFlavorBasis : List String
canonicalDownFlavorBasis =
  "e_d" ∷ "e_s" ∷ "e_b" ∷ []

record CarrierFlavorBasis : Set where
  field
    upBasis :
      List String

    upBasisIsCanonical :
      upBasis ≡ canonicalUpFlavorBasis

    downBasis :
      List String

    downBasisIsCanonical :
      downBasis ≡ canonicalDownFlavorBasis

open CarrierFlavorBasis public

canonicalCarrierFlavorBasis : CarrierFlavorBasis
canonicalCarrierFlavorBasis = record
  { upBasis = canonicalUpFlavorBasis
  ; upBasisIsCanonical = refl
  ; downBasis = canonicalDownFlavorBasis
  ; downBasisIsCanonical = refl
  }

canonicalUpYukawa3x3 : Exact.DiagonalYukawa3x3
canonicalUpYukawa3x3 = Exact.canonicalUpYukawa3x3

canonicalDownYukawa3x3 : Exact.DiagonalYukawa3x3
canonicalDownYukawa3x3 = Exact.canonicalDownYukawa3x3

canonicalUpYukawaMatrix : Matter.MixingMatrix
canonicalUpYukawaMatrix =
  Exact.DiagonalYukawa3x3.matrix canonicalUpYukawa3x3

canonicalDownYukawaMatrix : Matter.MixingMatrix
canonicalDownYukawaMatrix =
  Exact.DiagonalYukawa3x3.matrix canonicalDownYukawa3x3

canonicalUpYukawaYukawaDaggerMatrix : Matter.MixingMatrix
canonicalUpYukawaYukawaDaggerMatrix =
  Exact.diag3
    (Exact.exactGaussian 1 1)
    (Exact.exactGaussian 4 1)
    (Exact.exactGaussian 9 1)

data UltrametricUpSectorSlot : Set where
  upFirstFirstSlot :
    UltrametricUpSectorSlot

  upFirstSecondSlot :
    UltrametricUpSectorSlot

  upFirstThirdSlot :
    UltrametricUpSectorSlot

canonicalFirstGenerationUpSectorSlots :
  List UltrametricUpSectorSlot
canonicalFirstGenerationUpSectorSlots =
  upFirstFirstSlot
  ∷ upFirstSecondSlot
  ∷ upFirstThirdSlot
  ∷ []

upSectorSlotColumn :
  UltrametricUpSectorSlot →
  YDHR.YukawaGenerationIndex
upSectorSlotColumn upFirstFirstSlot =
  YDHR.firstGeneration
upSectorSlotColumn upFirstSecondSlot =
  YDHR.secondGeneration
upSectorSlotColumn upFirstThirdSlot =
  YDHR.thirdGeneration

upSectorSlotDepth :
  UltrametricUpSectorSlot →
  Nat
upSectorSlotDepth upFirstFirstSlot =
  zero
upSectorSlotDepth upFirstSecondSlot =
  suc zero
upSectorSlotDepth upFirstThirdSlot =
  suc (suc zero)

upSectorSlotWeight :
  UltrametricUpSectorSlot →
  Matter.MixingGaussianRationalDatum
upSectorSlotWeight upFirstFirstSlot =
  Exact.exactGaussian 1 1
upSectorSlotWeight upFirstSecondSlot =
  Exact.zeroGaussian
upSectorSlotWeight upFirstThirdSlot =
  Exact.zeroGaussian

upSectorSlotEntry :
  UltrametricUpSectorSlot →
  Matter.MixingGaussianRationalDatum
upSectorSlotEntry slot =
  YDHR.matrixEntry
    canonicalUpYukawaMatrix
    YDHR.firstGeneration
    (upSectorSlotColumn slot)

record FirstGenerationUpUltrametricDepthCarrier : Set where
  field
    rowGeneration :
      YDHR.YukawaGenerationIndex

    rowGenerationIsFirst :
      rowGeneration ≡ YDHR.firstGeneration

    carrierMatrix :
      Matter.MixingMatrix

    carrierMatrixIsCanonicalUp :
      carrierMatrix ≡ canonicalUpYukawaMatrix

    ultrametricSlots :
      List UltrametricUpSectorSlot

    ultrametricSlotsAreCanonical :
      ultrametricSlots ≡ canonicalFirstGenerationUpSectorSlots

    firstFirstDepth :
      Nat

    firstFirstDepthIsCanonical :
      firstFirstDepth ≡ upSectorSlotDepth upFirstFirstSlot

    firstSecondDepth :
      Nat

    firstSecondDepthIsCanonical :
      firstSecondDepth ≡ upSectorSlotDepth upFirstSecondSlot

    firstThirdDepth :
      Nat

    firstThirdDepthIsCanonical :
      firstThirdDepth ≡ upSectorSlotDepth upFirstThirdSlot

    firstFirstEntry :
      Matter.MixingGaussianRationalDatum

    firstFirstEntryIsMatrixEntry :
      firstFirstEntry
      ≡
      YDHR.matrixEntry
        carrierMatrix
        YDHR.firstGeneration
        YDHR.firstGeneration

    firstFirstEntryIsDepthWeight :
      firstFirstEntry ≡ upSectorSlotWeight upFirstFirstSlot

    firstSecondEntry :
      Matter.MixingGaussianRationalDatum

    firstSecondEntryIsMatrixEntry :
      firstSecondEntry
      ≡
      YDHR.matrixEntry
        carrierMatrix
        YDHR.firstGeneration
        YDHR.secondGeneration

    firstSecondEntryIsDepthWeight :
      firstSecondEntry ≡ upSectorSlotWeight upFirstSecondSlot

    firstThirdEntry :
      Matter.MixingGaussianRationalDatum

    firstThirdEntryIsMatrixEntry :
      firstThirdEntry
      ≡
      YDHR.matrixEntry
        carrierMatrix
        YDHR.firstGeneration
        YDHR.thirdGeneration

    firstThirdEntryIsDepthWeight :
      firstThirdEntry ≡ upSectorSlotWeight upFirstThirdSlot

    y11 :
      Matter.MixingGaussianRationalDatum

    y11IsFirstFirstEntry :
      y11 ≡ firstFirstEntry

    y12 :
      Matter.MixingGaussianRationalDatum

    y12IsFirstSecondEntry :
      y12 ≡ firstSecondEntry

    y13 :
      Matter.MixingGaussianRationalDatum

    y13IsFirstThirdEntry :
      y13 ≡ firstThirdEntry

    carrierDerivedEntries :
      Bool

    carrierDerivedEntriesIsTrue :
      carrierDerivedEntries ≡ true

    physicalValuesInhabited :
      Bool

    physicalValuesInhabitedIsFalse :
      physicalValuesInhabited ≡ false

    offDiagonalEntriesVanish :
      Bool

    offDiagonalEntriesVanishIsTrue :
      offDiagonalEntriesVanish ≡ true

    ultrametricDepthCarrierRecorded :
      Bool

    ultrametricDepthCarrierRecordedIsTrue :
      ultrametricDepthCarrierRecorded ≡ true

    physicalMassCalibrationPromoted :
      Bool

    physicalMassCalibrationPromotedIsFalse :
      physicalMassCalibrationPromoted ≡ false

    ultrametricDepthBoundary :
      List String

open FirstGenerationUpUltrametricDepthCarrier public

canonicalFirstGenerationUpUltrametricDepthCarrier :
  FirstGenerationUpUltrametricDepthCarrier
canonicalFirstGenerationUpUltrametricDepthCarrier =
  record
    { rowGeneration =
        YDHR.firstGeneration
    ; rowGenerationIsFirst =
        refl
    ; carrierMatrix =
        canonicalUpYukawaMatrix
    ; carrierMatrixIsCanonicalUp =
        refl
    ; ultrametricSlots =
        canonicalFirstGenerationUpSectorSlots
    ; ultrametricSlotsAreCanonical =
        refl
    ; firstFirstDepth =
        zero
    ; firstFirstDepthIsCanonical =
        refl
    ; firstSecondDepth =
        suc zero
    ; firstSecondDepthIsCanonical =
        refl
    ; firstThirdDepth =
        suc (suc zero)
    ; firstThirdDepthIsCanonical =
        refl
    ; firstFirstEntry =
        Exact.exactGaussian 1 1
    ; firstFirstEntryIsMatrixEntry =
        refl
    ; firstFirstEntryIsDepthWeight =
        refl
    ; firstSecondEntry =
        Exact.zeroGaussian
    ; firstSecondEntryIsMatrixEntry =
        refl
    ; firstSecondEntryIsDepthWeight =
        refl
    ; firstThirdEntry =
        Exact.zeroGaussian
    ; firstThirdEntryIsMatrixEntry =
        refl
    ; firstThirdEntryIsDepthWeight =
        refl
    ; y11 =
        Exact.exactGaussian 1 1
    ; y11IsFirstFirstEntry =
        refl
    ; y12 =
        Exact.zeroGaussian
    ; y12IsFirstSecondEntry =
        refl
    ; y13 =
        Exact.zeroGaussian
    ; y13IsFirstThirdEntry =
        refl
    ; carrierDerivedEntries =
        true
    ; carrierDerivedEntriesIsTrue =
        refl
    ; physicalValuesInhabited =
        false
    ; physicalValuesInhabitedIsFalse =
        refl
    ; offDiagonalEntriesVanish =
        true
    ; offDiagonalEntriesVanishIsTrue =
        refl
    ; ultrametricDepthCarrierRecorded =
        true
    ; ultrametricDepthCarrierRecordedIsTrue =
        refl
    ; physicalMassCalibrationPromoted =
        false
    ; physicalMassCalibrationPromotedIsFalse =
        refl
    ; ultrametricDepthBoundary =
        "The first-generation up-sector row is recorded as three explicit ultrametric-depth slots"
        ∷ "Depth zero carries the canonical u-u diagonal entry exactGaussian 1/1"
        ∷ "Depth one and depth two carry the u-c and u-t off-diagonal zero entries from the diagonal carrier matrix"
        ∷ "This is carrier-side depth data only; no physical mass calibration or Higgs-VEV promotion is claimed"
        ∷ []
    }

data UpperTriangularUpOffDiagonalSlot : Set where
  upY12Slot :
    UpperTriangularUpOffDiagonalSlot

  upY13Slot :
    UpperTriangularUpOffDiagonalSlot

  upY23Slot :
    UpperTriangularUpOffDiagonalSlot

canonicalUpperTriangularUpOffDiagonalSlots :
  List UpperTriangularUpOffDiagonalSlot
canonicalUpperTriangularUpOffDiagonalSlots =
  upY12Slot
  ∷ upY13Slot
  ∷ upY23Slot
  ∷ []

upOffDiagonalSlotDepth :
  UpperTriangularUpOffDiagonalSlot →
  Nat
upOffDiagonalSlotDepth upY12Slot =
  suc zero
upOffDiagonalSlotDepth upY13Slot =
  suc (suc zero)
upOffDiagonalSlotDepth upY23Slot =
  suc zero

upInterLaneSuppressionY12 :
  Matter.MixingGaussianRationalDatum
upInterLaneSuppressionY12 =
  Matter.mixingGaussianRationalDatum
    (Matter.mixingSignedRationalDatum 1 5 true)
    Matter.zeroMixingSignedRationalDatum

upInterLaneSuppressionY13 :
  Matter.MixingGaussianRationalDatum
upInterLaneSuppressionY13 =
  Matter.mixingGaussianRationalDatum
    (Matter.mixingSignedRationalDatum 1 25 true)
    Matter.zeroMixingSignedRationalDatum

upInterLaneSuppressionY23 :
  Matter.MixingGaussianRationalDatum
upInterLaneSuppressionY23 =
  Matter.mixingGaussianRationalDatum
    (Matter.mixingSignedRationalDatum 1 5 true)
    Matter.zeroMixingSignedRationalDatum

record UpperTriangularUpOffDiagonalYukawaCarrierReceipt : Set where
  field
    sourceUpYukawaMatrix :
      Matter.MixingMatrix

    sourceUpYukawaMatrixIsCanonical :
      sourceUpYukawaMatrix ≡ canonicalUpYukawaMatrix

    upperTriangularSlots :
      List UpperTriangularUpOffDiagonalSlot

    upperTriangularSlotsAreCanonical :
      upperTriangularSlots
      ≡
      canonicalUpperTriangularUpOffDiagonalSlots

    y12Depth :
      Nat

    y12DepthIsInterLane :
      y12Depth ≡ upOffDiagonalSlotDepth upY12Slot

    y13Depth :
      Nat

    y13DepthIsInterLane :
      y13Depth ≡ upOffDiagonalSlotDepth upY13Slot

    y23Depth :
      Nat

    y23DepthIsInterLane :
      y23Depth ≡ upOffDiagonalSlotDepth upY23Slot

    y12 :
      Matter.MixingGaussianRationalDatum

    y12IsInterLaneSuppressed :
      y12 ≡ upInterLaneSuppressionY12

    y13 :
      Matter.MixingGaussianRationalDatum

    y13IsDepthSuppressed :
      y13 ≡ upInterLaneSuppressionY13

    y23 :
      Matter.MixingGaussianRationalDatum

    y23IsInterLaneSuppressed :
      y23 ≡ upInterLaneSuppressionY23

    offDiagonalEntriesInhabited :
      Bool

    offDiagonalEntriesInhabitedIsTrue :
      offDiagonalEntriesInhabited ≡ true

    physicalCouplingScaleUnknown :
      Bool

    physicalCouplingScaleUnknownIsTrue :
      physicalCouplingScaleUnknown ≡ true

    physicalValuesPromoted :
      Bool

    physicalValuesPromotedIsFalse :
      physicalValuesPromoted ≡ false

    ckmPromotionConstructed :
      Bool

    ckmPromotionConstructedIsFalse :
      ckmPromotionConstructed ≡ false

    offDiagonalCarrierBoundary :
      List String

open UpperTriangularUpOffDiagonalYukawaCarrierReceipt public

canonicalUpperTriangularUpOffDiagonalYukawaCarrierReceipt :
  UpperTriangularUpOffDiagonalYukawaCarrierReceipt
canonicalUpperTriangularUpOffDiagonalYukawaCarrierReceipt =
  record
    { sourceUpYukawaMatrix =
        canonicalUpYukawaMatrix
    ; sourceUpYukawaMatrixIsCanonical =
        refl
    ; upperTriangularSlots =
        canonicalUpperTriangularUpOffDiagonalSlots
    ; upperTriangularSlotsAreCanonical =
        refl
    ; y12Depth =
        suc zero
    ; y12DepthIsInterLane =
        refl
    ; y13Depth =
        suc (suc zero)
    ; y13DepthIsInterLane =
        refl
    ; y23Depth =
        suc zero
    ; y23DepthIsInterLane =
        refl
    ; y12 =
        upInterLaneSuppressionY12
    ; y12IsInterLaneSuppressed =
        refl
    ; y13 =
        upInterLaneSuppressionY13
    ; y13IsDepthSuppressed =
        refl
    ; y23 =
        upInterLaneSuppressionY23
    ; y23IsInterLaneSuppressed =
        refl
    ; offDiagonalEntriesInhabited =
        true
    ; offDiagonalEntriesInhabitedIsTrue =
        refl
    ; physicalCouplingScaleUnknown =
        true
    ; physicalCouplingScaleUnknownIsTrue =
        refl
    ; physicalValuesPromoted =
        false
    ; physicalValuesPromotedIsFalse =
        refl
    ; ckmPromotionConstructed =
        false
    ; ckmPromotionConstructedIsFalse =
        refl
    ; offDiagonalCarrierBoundary =
        "Upper-triangular up-sector carrier entries y12, y13, and y23 are inhabited as symbolic inter-lane/depth-suppressed Gaussian rational data"
        ∷ "The concrete carrier entries use real suppressions 1/5, 1/25, and 1/5 with zero imaginary parts"
        ∷ "These entries are not physical Yukawa values; the physical coupling scale remains unknown"
        ∷ "No CKM promotion or physical weak-mass-basis identification is constructed here"
        ∷ []
    }

record UpWeakBasisEigenbasisTransport : Set where
  field
    carrierUpYukawa :
      Exact.DiagonalYukawa3x3

    carrierUpYukawaIsCanonical :
      carrierUpYukawa ≡ canonicalUpYukawa3x3

    carrierUpYukawaMatrix :
      Matter.MixingMatrix

    carrierUpYukawaMatrixIsCarrierMatrix :
      carrierUpYukawaMatrix
      ≡
      Exact.DiagonalYukawa3x3.matrix carrierUpYukawa

    carrierUpYukawaMatrixIsCanonical :
      carrierUpYukawaMatrix ≡ canonicalUpYukawaMatrix

    upHermitianProductMatrix :
      Matter.MixingMatrix

    upHermitianProductMatrixIsExplicitDiagonal :
      upHermitianProductMatrix
      ≡
      canonicalUpYukawaYukawaDaggerMatrix

    U_u :
      Matter.MixingMatrix

    U_uIsIdentity :
      U_u ≡ Matter.identityMixingMatrix

    U_uUnitaryClosure :
      Matter.leftIdentityMixingProduct U_u ≡ U_u

    transportedUpHermitianProduct :
      Matter.MixingMatrix

    transportedUpHermitianProductIsUuTransport :
      transportedUpHermitianProduct
      ≡
      Matter.leftIdentityMixingProduct upHermitianProductMatrix

    transportedUpHermitianProductIsExplicitDiagonal :
      transportedUpHermitianProduct
      ≡
      canonicalUpYukawaYukawaDaggerMatrix

    U_uDiagonalisesY_uY_uDagger :
      transportedUpHermitianProduct ≡ upHermitianProductMatrix

    upWeakBasisEigenbasisTransportConstructed :
      Bool

    upWeakBasisEigenbasisTransportConstructedIsTrue :
      upWeakBasisEigenbasisTransportConstructed ≡ true

    upWeakBasisEigenbasisTransportBoundary :
      List String

open UpWeakBasisEigenbasisTransport public

canonicalUpWeakBasisEigenbasisTransport :
  UpWeakBasisEigenbasisTransport
canonicalUpWeakBasisEigenbasisTransport = record
  { carrierUpYukawa = canonicalUpYukawa3x3
  ; carrierUpYukawaIsCanonical = refl
  ; carrierUpYukawaMatrix = canonicalUpYukawaMatrix
  ; carrierUpYukawaMatrixIsCarrierMatrix = refl
  ; carrierUpYukawaMatrixIsCanonical = refl
  ; upHermitianProductMatrix = canonicalUpYukawaYukawaDaggerMatrix
  ; upHermitianProductMatrixIsExplicitDiagonal = refl
  ; U_u = Matter.identityMixingMatrix
  ; U_uIsIdentity = refl
  ; U_uUnitaryClosure = refl
  ; transportedUpHermitianProduct =
      Matter.leftIdentityMixingProduct canonicalUpYukawaYukawaDaggerMatrix
  ; transportedUpHermitianProductIsUuTransport = refl
  ; transportedUpHermitianProductIsExplicitDiagonal = refl
  ; U_uDiagonalisesY_uY_uDagger = refl
  ; upWeakBasisEigenbasisTransportConstructed = true
  ; upWeakBasisEigenbasisTransportConstructedIsTrue = refl
  ; upWeakBasisEigenbasisTransportBoundary =
      "The carrier up Yukawa is the existing canonical diagonal matrix diag(1,2,3)"
      ∷ "The carrier up Hermitian product surface Y_u Y_u^dagger is recorded as the explicit diagonal matrix diag(1,4,9)"
      ∷ "The weak-basis up eigenbasis transport matrix U_u is the concrete identity MixingMatrix"
      ∷ "Identity transport leaves the diagonal Hermitian product fixed, so U_u diagonalises the up-sector carrier surface by refl"
      ∷ []
  }

data YukawaCarrierFailClosedBlocker : Set where
  missingAbsoluteHiggsVEVW4CalibrationForPhysicalYukawa :
    YukawaCarrierFailClosedBlocker

  missingPhysicalFermionMassEigenvalueReceipt :
    YukawaCarrierFailClosedBlocker

  missingSplittingFieldForGenericYukawaEigenvalues :
    YukawaCarrierFailClosedBlocker

  missingEigenbasisTransportForNonDiagonalYukawa :
    YukawaCarrierFailClosedBlocker

  missingPhysicalWeakMassBasisCKMIdentification :
    YukawaCarrierFailClosedBlocker

  missingActualDHRSectorRepresentationsForNonIdentityAction :
    YukawaCarrierFailClosedBlocker

  missingPhysicalYukawaMatricesForDHRPromotion :
    YukawaCarrierFailClosedBlocker

canonicalYukawaCarrierFailClosedBlockers :
  List YukawaCarrierFailClosedBlocker
canonicalYukawaCarrierFailClosedBlockers =
  missingAbsoluteHiggsVEVW4CalibrationForPhysicalYukawa
  ∷ missingPhysicalFermionMassEigenvalueReceipt
  ∷ missingSplittingFieldForGenericYukawaEigenvalues
  ∷ missingEigenbasisTransportForNonDiagonalYukawa
  ∷ missingPhysicalWeakMassBasisCKMIdentification
  ∷ missingActualDHRSectorRepresentationsForNonIdentityAction
  ∷ missingPhysicalYukawaMatricesForDHRPromotion
  ∷ []

record YukawaFromCarrierReceipt : Setω where
  field
    carrierFlavorBasis :
      CarrierFlavorBasis

    fnWitness :
      FN.FroggattNielsenWitness

    higgsReceipt :
      Higgs.HiggsSymmetryBreakingReceipt

    exactWitnessChain :
      Exact.CKMExactWitnessChain

    matterReceipt :
      Matter.MatterRepresentationReceiptSurface

    ckmCarrierDerivedReceipt :
      CKMD.CKMCarrierDerivedReceipt

    ckmUnitaryReceipt :
      CKMU.CKMUnitaryReceipt

    yukawaDHRIntertwinerCompatibilityReceipt :
      YDHR.YukawaDHRIntertwinerCompatibilityReceipt

    carrierDHRYukawaFormulaSurface :
      YDHR.CarrierDHRYukawaFormulaSurface

    carrierDHRYukawaFormulaSurfaceLabel :
      YDHR.formulaLabel carrierDHRYukawaFormulaSurface
      ≡
      "Y_ij = <rho_i, Phi_H * rho_j>"

    ckmCarrierMatrix :
      Matter.MixingMatrix

    ckmCarrierMatrixIsCarrierDerived :
      ckmCarrierMatrix
      ≡
      CKMD.ckmCarrierMatrix ckmCarrierDerivedReceipt

    ckmCarrierMatrixIsUnitaryReceiptMatrix :
      ckmCarrierMatrix
      ≡
      CKMU.carrierCKMMatrix ckmUnitaryReceipt

    ckmCarrierMatrixIsIdentity :
      ckmCarrierMatrix ≡ Matter.identityMixingMatrix

    upYukawa :
      Exact.DiagonalYukawa3x3

    upYukawaIsCanonical :
      upYukawa ≡ canonicalUpYukawa3x3

    downYukawa :
      Exact.DiagonalYukawa3x3

    downYukawaIsCanonical :
      downYukawa ≡ canonicalDownYukawa3x3

    upYukawaMatrix :
      Matter.MixingMatrix

    upYukawaMatrixIsCanonical :
      upYukawaMatrix ≡ canonicalUpYukawaMatrix

    downYukawaMatrix :
      Matter.MixingMatrix

    downYukawaMatrixIsCanonical :
      downYukawaMatrix ≡ canonicalDownYukawaMatrix

    upYukawaMatrixAgreesWithCarrierDerivedCKM :
      upYukawaMatrix
      ≡
      CKMD.yukawaUpMatrix ckmCarrierDerivedReceipt

    upWeakBasisEigenbasisTransport :
      UpWeakBasisEigenbasisTransport

    upWeakBasisEigenbasisTransportIsCanonical :
      upWeakBasisEigenbasisTransport
      ≡
      canonicalUpWeakBasisEigenbasisTransport

    firstGenerationUpUltrametricDepthCarrier :
      FirstGenerationUpUltrametricDepthCarrier

    firstGenerationUpUltrametricDepthCarrierIsCanonical :
      firstGenerationUpUltrametricDepthCarrier
      ≡
      canonicalFirstGenerationUpUltrametricDepthCarrier

    firstGenerationUpUltrametricDepthCarrierRecorded :
      ultrametricDepthCarrierRecorded
        firstGenerationUpUltrametricDepthCarrier
      ≡
      true

    firstGenerationUpCarrierDerivedEntriesRecorded :
      carrierDerivedEntries
        firstGenerationUpUltrametricDepthCarrier
      ≡
      true

    firstGenerationUpPhysicalValuesInhabitedClosed :
      physicalValuesInhabited
        firstGenerationUpUltrametricDepthCarrier
      ≡
      false

    firstGenerationUpUltrametricDepthCarrierMatrixAgrees :
      FirstGenerationUpUltrametricDepthCarrier.carrierMatrix
        firstGenerationUpUltrametricDepthCarrier
      ≡
      upYukawaMatrix

    firstGenerationUpUltrametricDepthPhysicalPromotionClosed :
      physicalMassCalibrationPromoted
        firstGenerationUpUltrametricDepthCarrier
      ≡
      false

    upperTriangularUpOffDiagonalReceipt :
      UpperTriangularUpOffDiagonalYukawaCarrierReceipt

    upperTriangularUpOffDiagonalReceiptIsCanonical :
      upperTriangularUpOffDiagonalReceipt
      ≡
      canonicalUpperTriangularUpOffDiagonalYukawaCarrierReceipt

    upperTriangularUpOffDiagonalEntriesInhabited :
      offDiagonalEntriesInhabited upperTriangularUpOffDiagonalReceipt
      ≡
      true

    upperTriangularUpPhysicalCouplingScaleUnknown :
      physicalCouplingScaleUnknown upperTriangularUpOffDiagonalReceipt
      ≡
      true

    upperTriangularUpPhysicalValuesNotPromoted :
      physicalValuesPromoted upperTriangularUpOffDiagonalReceipt
      ≡
      false

    upperTriangularUpCKMPromotionClosed :
      ckmPromotionConstructed upperTriangularUpOffDiagonalReceipt
      ≡
      false

    U_u :
      Matter.MixingMatrix

    U_uMatchesUpWeakBasisTransport :
      U_u
      ≡
      UpWeakBasisEigenbasisTransport.U_u
        upWeakBasisEigenbasisTransport

    U_uIsIdentity :
      U_u ≡ Matter.identityMixingMatrix

    U_uUnitaryClosure :
      Matter.leftIdentityMixingProduct U_u ≡ U_u

    U_uDiagonalisesCarrierUpYukawaYukawaDagger :
      UpWeakBasisEigenbasisTransport.transportedUpHermitianProduct
        upWeakBasisEigenbasisTransport
      ≡
      UpWeakBasisEigenbasisTransport.upHermitianProductMatrix
        upWeakBasisEigenbasisTransport

    downYukawaMatrixAgreesWithCarrierDerivedCKM :
      downYukawaMatrix
      ≡
      CKMD.yukawaDownMatrix ckmCarrierDerivedReceipt

    upYukawaFormulaEntriesAgreeWithMatrix :
      (i j : YDHR.YukawaGenerationIndex) →
      YDHR.upFormulaEntry carrierDHRYukawaFormulaSurface i j
      ≡
      YDHR.matrixEntry upYukawaMatrix i j

    downYukawaFormulaEntriesAgreeWithMatrix :
      (i j : YDHR.YukawaGenerationIndex) →
      YDHR.downFormulaEntry carrierDHRYukawaFormulaSurface i j
      ≡
      YDHR.matrixEntry downYukawaMatrix i j

    carrierDHRYukawaFormulaPhysicalPromotionClosed :
      YDHR.physicalDHRYukawaFormulaPromoted
        carrierDHRYukawaFormulaSurface
      ≡
      false

    yukawaDHRCarrierDerivedReceiptThreaded :
      Bool

    yukawaDHRCarrierDerivedReceiptThreadedIsTrue :
      yukawaDHRCarrierDerivedReceiptThreaded ≡ true

    yukawaDHRIdentitySectorActionExplicit :
      Bool

    yukawaDHRIdentitySectorActionExplicitMatchesReceipt :
      yukawaDHRIdentitySectorActionExplicit
      ≡
      YDHR.identitySectorActionExplicit
        yukawaDHRIntertwinerCompatibilityReceipt

    yukawaDHRIdentitySectorActionExplicitIsTrue :
      yukawaDHRIdentitySectorActionExplicit ≡ true

    yukawaDHRNonIdentitySymbolicSectorActionsConstructed :
      Bool

    yukawaDHRNonIdentitySymbolicSectorActionsConstructedMatchesReceipt :
      yukawaDHRNonIdentitySymbolicSectorActionsConstructed
      ≡
      YDHR.nonIdentitySymbolicSectorActionsConstructed
        yukawaDHRIntertwinerCompatibilityReceipt

    yukawaDHRNonIdentitySymbolicSectorActionsConstructedIsTrue :
      yukawaDHRNonIdentitySymbolicSectorActionsConstructed ≡ true

    yukawaDHRU1PhaseChargeSelectionReceipt :
      YDHR.U1PhaseChargeSelectionSymbolicIntertwinerReceipt

    yukawaDHRU1PhaseChargeSelectionReceiptMatchesDHR :
      yukawaDHRU1PhaseChargeSelectionReceipt
      ≡
      YDHR.u1PhaseChargeSelectionReceipt
        yukawaDHRIntertwinerCompatibilityReceipt

    yukawaDHRU1PhaseChargeSelectionConstructed :
      Bool

    yukawaDHRU1PhaseChargeSelectionConstructedMatchesDHR :
      yukawaDHRU1PhaseChargeSelectionConstructed
      ≡
      YDHR.u1PhaseChargeSelectionConstructed
        yukawaDHRIntertwinerCompatibilityReceipt

    yukawaDHRU1PhaseChargeSelectionConstructedIsTrue :
      yukawaDHRU1PhaseChargeSelectionConstructed ≡ true

    yukawaDHRU1PhysicalSectorRepresentationConstructed :
      Bool

    yukawaDHRU1PhysicalSectorRepresentationConstructedMatchesDHR :
      yukawaDHRU1PhysicalSectorRepresentationConstructed
      ≡
      YDHR.u1PhysicalSectorRepresentationConstructed
        yukawaDHRIntertwinerCompatibilityReceipt

    yukawaDHRU1PhysicalSectorRepresentationConstructedIsFalse :
      yukawaDHRU1PhysicalSectorRepresentationConstructed ≡ false

    yukawaDHRSU2DoubletShapeReceipt :
      YDHR.SU2DoubletShapeSymbolicIntertwinerReceipt

    yukawaDHRSU2DoubletShapeReceiptMatchesDHR :
      yukawaDHRSU2DoubletShapeReceipt
      ≡
      YDHR.su2DoubletShapeReceipt
        yukawaDHRIntertwinerCompatibilityReceipt

    yukawaDHRSU2DoubletShapeCheckConstructed :
      Bool

    yukawaDHRSU2DoubletShapeCheckConstructedMatchesDHR :
      yukawaDHRSU2DoubletShapeCheckConstructed
      ≡
      YDHR.su2DoubletShapeCheckConstructed
        yukawaDHRIntertwinerCompatibilityReceipt

    yukawaDHRSU2DoubletShapeCheckConstructedIsTrue :
      yukawaDHRSU2DoubletShapeCheckConstructed ≡ true

    yukawaDHRSU2PhysicalMatrixRepresentationConstructed :
      Bool

    yukawaDHRSU2PhysicalMatrixRepresentationConstructedMatchesDHR :
      yukawaDHRSU2PhysicalMatrixRepresentationConstructed
      ≡
      YDHR.su2PhysicalMatrixRepresentationConstructed
        yukawaDHRIntertwinerCompatibilityReceipt

    yukawaDHRSU2PhysicalMatrixRepresentationConstructedIsFalse :
      yukawaDHRSU2PhysicalMatrixRepresentationConstructed ≡ false

    yukawaDHRPhysicalNonIdentityActionConstructed :
      Bool

    yukawaDHRPhysicalNonIdentityActionConstructedMatchesReceipt :
      yukawaDHRPhysicalNonIdentityActionConstructed
      ≡
      YDHR.physicalNonIdentityDHRActionConstructed
        yukawaDHRIntertwinerCompatibilityReceipt

    yukawaDHRPhysicalNonIdentityActionConstructedIsFalse :
      yukawaDHRPhysicalNonIdentityActionConstructed ≡ false

    yukawaDHRCarrierCKMMatrixAgrees :
      YDHR.carrierCKMMatrix
        yukawaDHRIntertwinerCompatibilityReceipt
      ≡
      ckmCarrierMatrix

    yukawaDHRUpMatrixAgrees :
      YDHR.upYukawaMatrix
      ≡
      upYukawaMatrix

    yukawaDHRDownMatrixAgrees :
      YDHR.downYukawaMatrix
      ≡
      downYukawaMatrix

    yukawaDHRPhysicalPromotionClosed :
      YDHR.physicalYukawaDHRPromotionConstructed
        yukawaDHRIntertwinerCompatibilityReceipt
      ≡
      false

    yukawaDHRIntertwinerBeyondIdentityClosed :
      YDHR.dhrActionBeyondIdentityConstructed
        yukawaDHRIntertwinerCompatibilityReceipt
      ≡
      false

    yukawaDHRActualSectorRepresentationsConstructed :
      Bool

    yukawaDHRActualSectorRepresentationsConstructedMatchesReceipt :
      yukawaDHRActualSectorRepresentationsConstructed
      ≡
      YDHR.actualDHRSectorRepresentationsConstructed
        yukawaDHRIntertwinerCompatibilityReceipt

    yukawaDHRActualSectorRepresentationsConstructedIsFalse :
      yukawaDHRActualSectorRepresentationsConstructed ≡ false

    yukawaDHRPhysicalYukawaMatricesSupplied :
      Bool

    yukawaDHRPhysicalYukawaMatricesSuppliedMatchesReceipt :
      yukawaDHRPhysicalYukawaMatricesSupplied
      ≡
      YDHR.physicalYukawaMatricesSupplied
        yukawaDHRIntertwinerCompatibilityReceipt

    yukawaDHRPhysicalYukawaMatricesSuppliedIsFalse :
      yukawaDHRPhysicalYukawaMatricesSupplied ≡ false

    failClosedBlockers :
      List YukawaCarrierFailClosedBlocker

    failClosedBlockersAreCanonical :
      failClosedBlockers ≡ canonicalYukawaCarrierFailClosedBlockers

    firstFailClosedBlocker :
      YukawaCarrierFailClosedBlocker

    firstFailClosedBlockerIsAbsoluteHiggsVEVW4 :
      firstFailClosedBlocker
      ≡
      missingAbsoluteHiggsVEVW4CalibrationForPhysicalYukawa

    absoluteHiggsVEVW4CalibrationConstructed :
      Bool

    absoluteHiggsVEVW4CalibrationConstructedIsFalse :
      absoluteHiggsVEVW4CalibrationConstructed ≡ false

    splittingFieldEigenbasisConstructed :
      Bool

    splittingFieldEigenbasisConstructedIsFalse :
      splittingFieldEigenbasisConstructed ≡ false

    physicalYukawaPromotionConstructed :
      Bool

    physicalYukawaPromotionConstructedIsFalse :
      physicalYukawaPromotionConstructed ≡ false

    upSectorLabel :
      String

    upSectorLabelIsCanonical :
      upSectorLabel ≡ "carrier-up-Yukawa"

    downSectorLabel :
      String

    downSectorLabelIsCanonical :
      downSectorLabel ≡ "carrier-down-Yukawa"

    carrierDerivedTargetRecorded :
      Bool

    carrierDerivedTargetRecordedIsTrue :
      carrierDerivedTargetRecorded ≡ true

    boundary :
      List String

open YukawaFromCarrierReceipt public

canonicalYukawaFromCarrier : YukawaFromCarrierReceipt
canonicalYukawaFromCarrier = record
  { carrierFlavorBasis = canonicalCarrierFlavorBasis
  ; fnWitness = FN.canonicalFroggattNielsenWitness
  ; higgsReceipt = Higgs.canonicalHiggsSymmetryBreakingReceipt
  ; exactWitnessChain = Exact.canonicalCKMExactWitnessChain
  ; matterReceipt = Matter.canonicalMatterRepresentationReceiptSurface
  ; ckmCarrierDerivedReceipt = CKMD.canonicalCKMCarrierDerived
  ; ckmUnitaryReceipt = CKMU.canonicalCKMUnitary
  ; yukawaDHRIntertwinerCompatibilityReceipt =
      YDHR.canonicalYukawaDHRIntertwinerCompatibility
  ; carrierDHRYukawaFormulaSurface =
      YDHR.carrierDHRYukawaFormulaSurface
        YDHR.canonicalYukawaDHRIntertwinerCompatibility
  ; carrierDHRYukawaFormulaSurfaceLabel =
      refl
  ; ckmCarrierMatrix =
      CKMD.ckmCarrierMatrix CKMD.canonicalCKMCarrierDerived
  ; ckmCarrierMatrixIsCarrierDerived = refl
  ; ckmCarrierMatrixIsUnitaryReceiptMatrix = refl
  ; ckmCarrierMatrixIsIdentity = refl
  ; upYukawa = canonicalUpYukawa3x3
  ; upYukawaIsCanonical = refl
  ; downYukawa = canonicalDownYukawa3x3
  ; downYukawaIsCanonical = refl
  ; upYukawaMatrix = canonicalUpYukawaMatrix
  ; upYukawaMatrixIsCanonical = refl
  ; downYukawaMatrix = canonicalDownYukawaMatrix
  ; downYukawaMatrixIsCanonical = refl
  ; upYukawaMatrixAgreesWithCarrierDerivedCKM = refl
  ; upWeakBasisEigenbasisTransport =
      canonicalUpWeakBasisEigenbasisTransport
  ; upWeakBasisEigenbasisTransportIsCanonical =
      refl
  ; firstGenerationUpUltrametricDepthCarrier =
      canonicalFirstGenerationUpUltrametricDepthCarrier
  ; firstGenerationUpUltrametricDepthCarrierIsCanonical =
      refl
  ; firstGenerationUpUltrametricDepthCarrierRecorded =
      refl
  ; firstGenerationUpCarrierDerivedEntriesRecorded =
      refl
  ; firstGenerationUpPhysicalValuesInhabitedClosed =
      refl
  ; firstGenerationUpUltrametricDepthCarrierMatrixAgrees =
      refl
  ; firstGenerationUpUltrametricDepthPhysicalPromotionClosed =
      refl
  ; upperTriangularUpOffDiagonalReceipt =
      canonicalUpperTriangularUpOffDiagonalYukawaCarrierReceipt
  ; upperTriangularUpOffDiagonalReceiptIsCanonical =
      refl
  ; upperTriangularUpOffDiagonalEntriesInhabited =
      refl
  ; upperTriangularUpPhysicalCouplingScaleUnknown =
      refl
  ; upperTriangularUpPhysicalValuesNotPromoted =
      refl
  ; upperTriangularUpCKMPromotionClosed =
      refl
  ; U_u =
      UpWeakBasisEigenbasisTransport.U_u
        canonicalUpWeakBasisEigenbasisTransport
  ; U_uMatchesUpWeakBasisTransport =
      refl
  ; U_uIsIdentity =
      refl
  ; U_uUnitaryClosure =
      refl
  ; U_uDiagonalisesCarrierUpYukawaYukawaDagger =
      UpWeakBasisEigenbasisTransport.U_uDiagonalisesY_uY_uDagger
        canonicalUpWeakBasisEigenbasisTransport
  ; downYukawaMatrixAgreesWithCarrierDerivedCKM = refl
  ; upYukawaFormulaEntriesAgreeWithMatrix =
      λ _ _ → refl
  ; downYukawaFormulaEntriesAgreeWithMatrix =
      λ _ _ → refl
  ; carrierDHRYukawaFormulaPhysicalPromotionClosed =
      refl
  ; yukawaDHRCarrierDerivedReceiptThreaded = true
  ; yukawaDHRCarrierDerivedReceiptThreadedIsTrue = refl
  ; yukawaDHRIdentitySectorActionExplicit =
      YDHR.identitySectorActionExplicit
        YDHR.canonicalYukawaDHRIntertwinerCompatibility
  ; yukawaDHRIdentitySectorActionExplicitMatchesReceipt = refl
  ; yukawaDHRIdentitySectorActionExplicitIsTrue = refl
  ; yukawaDHRNonIdentitySymbolicSectorActionsConstructed =
      YDHR.nonIdentitySymbolicSectorActionsConstructed
        YDHR.canonicalYukawaDHRIntertwinerCompatibility
  ; yukawaDHRNonIdentitySymbolicSectorActionsConstructedMatchesReceipt =
      refl
  ; yukawaDHRNonIdentitySymbolicSectorActionsConstructedIsTrue =
      refl
  ; yukawaDHRU1PhaseChargeSelectionReceipt =
      YDHR.u1PhaseChargeSelectionReceipt
        YDHR.canonicalYukawaDHRIntertwinerCompatibility
  ; yukawaDHRU1PhaseChargeSelectionReceiptMatchesDHR =
      refl
  ; yukawaDHRU1PhaseChargeSelectionConstructed =
      YDHR.u1PhaseChargeSelectionConstructed
        YDHR.canonicalYukawaDHRIntertwinerCompatibility
  ; yukawaDHRU1PhaseChargeSelectionConstructedMatchesDHR =
      refl
  ; yukawaDHRU1PhaseChargeSelectionConstructedIsTrue =
      refl
  ; yukawaDHRU1PhysicalSectorRepresentationConstructed =
      YDHR.u1PhysicalSectorRepresentationConstructed
        YDHR.canonicalYukawaDHRIntertwinerCompatibility
  ; yukawaDHRU1PhysicalSectorRepresentationConstructedMatchesDHR =
      refl
  ; yukawaDHRU1PhysicalSectorRepresentationConstructedIsFalse =
      refl
  ; yukawaDHRSU2DoubletShapeReceipt =
      YDHR.su2DoubletShapeReceipt
        YDHR.canonicalYukawaDHRIntertwinerCompatibility
  ; yukawaDHRSU2DoubletShapeReceiptMatchesDHR =
      refl
  ; yukawaDHRSU2DoubletShapeCheckConstructed =
      YDHR.su2DoubletShapeCheckConstructed
        YDHR.canonicalYukawaDHRIntertwinerCompatibility
  ; yukawaDHRSU2DoubletShapeCheckConstructedMatchesDHR =
      refl
  ; yukawaDHRSU2DoubletShapeCheckConstructedIsTrue =
      refl
  ; yukawaDHRSU2PhysicalMatrixRepresentationConstructed =
      YDHR.su2PhysicalMatrixRepresentationConstructed
        YDHR.canonicalYukawaDHRIntertwinerCompatibility
  ; yukawaDHRSU2PhysicalMatrixRepresentationConstructedMatchesDHR =
      refl
  ; yukawaDHRSU2PhysicalMatrixRepresentationConstructedIsFalse =
      refl
  ; yukawaDHRPhysicalNonIdentityActionConstructed =
      YDHR.physicalNonIdentityDHRActionConstructed
        YDHR.canonicalYukawaDHRIntertwinerCompatibility
  ; yukawaDHRPhysicalNonIdentityActionConstructedMatchesReceipt =
      refl
  ; yukawaDHRPhysicalNonIdentityActionConstructedIsFalse =
      refl
  ; yukawaDHRCarrierCKMMatrixAgrees = refl
  ; yukawaDHRUpMatrixAgrees = refl
  ; yukawaDHRDownMatrixAgrees = refl
  ; yukawaDHRPhysicalPromotionClosed = refl
  ; yukawaDHRIntertwinerBeyondIdentityClosed = refl
  ; yukawaDHRActualSectorRepresentationsConstructed =
      YDHR.actualDHRSectorRepresentationsConstructed
        YDHR.canonicalYukawaDHRIntertwinerCompatibility
  ; yukawaDHRActualSectorRepresentationsConstructedMatchesReceipt =
      refl
  ; yukawaDHRActualSectorRepresentationsConstructedIsFalse =
      refl
  ; yukawaDHRPhysicalYukawaMatricesSupplied =
      YDHR.physicalYukawaMatricesSupplied
        YDHR.canonicalYukawaDHRIntertwinerCompatibility
  ; yukawaDHRPhysicalYukawaMatricesSuppliedMatchesReceipt =
      refl
  ; yukawaDHRPhysicalYukawaMatricesSuppliedIsFalse =
      refl
  ; failClosedBlockers = canonicalYukawaCarrierFailClosedBlockers
  ; failClosedBlockersAreCanonical = refl
  ; firstFailClosedBlocker =
      missingAbsoluteHiggsVEVW4CalibrationForPhysicalYukawa
  ; firstFailClosedBlockerIsAbsoluteHiggsVEVW4 = refl
  ; absoluteHiggsVEVW4CalibrationConstructed = false
  ; absoluteHiggsVEVW4CalibrationConstructedIsFalse = refl
  ; splittingFieldEigenbasisConstructed = false
  ; splittingFieldEigenbasisConstructedIsFalse = refl
  ; physicalYukawaPromotionConstructed = false
  ; physicalYukawaPromotionConstructedIsFalse = refl
  ; upSectorLabel = "carrier-up-Yukawa"
  ; upSectorLabelIsCanonical = refl
  ; downSectorLabel = "carrier-down-Yukawa"
  ; downSectorLabelIsCanonical = refl
  ; carrierDerivedTargetRecorded = true
  ; carrierDerivedTargetRecordedIsTrue = refl
  ; boundary =
      "The carrier package reuses the exact up/down 3x3 Yukawa matrices already present in CKMExactWitnesses"
      ∷ "FN and Higgs receipts are threaded in as concrete upstream anchors"
      ∷ "The carrier-derived CKM and CKM-unitarity receipts agree on the concrete identity matrix"
      ∷ "MatterRepresentationReceiptSurface is threaded as the matter constructor surface for the quark/Higgs sockets"
      ∷ "The Yukawa/DHR compatibility receipt consumes the same carrier-derived CKM/Yukawa matrices"
      ∷ "The carrier/DHR formula surface exposes Y_ij = <rho_i, Phi_H * rho_j> as concrete up/down matrix-entry access for each generation pair"
      ∷ "The first-generation up-sector row is now exposed as explicit ultrametric-depth carrier data for the u-u, u-c, and u-t entries"
      ∷ "The DHR receipt exposes explicit identity-sector coverage plus finite symbolic non-identity sector actions"
      ∷ "The DHR receipt also threads concrete U(1) phase/charge-selection and SU(2) doublet-shape symbolic checks"
      ∷ "The up-sector y11, y12, and y13 entries are read from the carrier matrix first row; carrierDerivedEntries is true and physicalValuesInhabited is false"
      ∷ "The upper-triangular up-sector off-diagonal carrier receipt inhabits symbolic y12, y13, and y23 entries with inter-lane/depth suppression"
      ∷ "The off-diagonal receipt keeps physicalCouplingScaleUnknown true and does not promote physical values or CKM"
      ∷ "Physical fermion masses, absolute Higgs/VEV/W4 calibration, splitting-field/eigenbasis lifts, actual DHR sector representations, and physical Yukawa matrices are explicit fail-closed blockers"
      ∷ "Actual DHR sector representations and physical Yukawa matrices are still absent, so non-identity physical promotion remains false"
      ∷ "Physical non-identity DHR action and physical Yukawa promotion remain fail-closed"
      ∷ "The matrices live in the repo's concrete Matter.MixingMatrix carrier"
      ∷ "No postulate or placeholder field is introduced"
      ∷ []
  }

canonicalYukawaFromCarrierUsesCarrierDerivedCKM :
  ckmCarrierMatrix canonicalYukawaFromCarrier
  ≡
  CKMD.ckmCarrierMatrix
    (ckmCarrierDerivedReceipt canonicalYukawaFromCarrier)
canonicalYukawaFromCarrierUsesCarrierDerivedCKM =
  refl

canonicalYukawaFromCarrierKeepsPhysicalPromotionClosed :
  physicalYukawaPromotionConstructed canonicalYukawaFromCarrier
  ≡
  false
canonicalYukawaFromCarrierKeepsPhysicalPromotionClosed =
  refl

canonicalYukawaFromCarrierThreadsU1PhaseChargeSelection :
  yukawaDHRU1PhaseChargeSelectionConstructed canonicalYukawaFromCarrier
  ≡
  true
canonicalYukawaFromCarrierThreadsU1PhaseChargeSelection =
  refl

canonicalYukawaFromCarrierRecordsFirstGenerationUpUltrametricDepth :
  ultrametricDepthCarrierRecorded
    (firstGenerationUpUltrametricDepthCarrier canonicalYukawaFromCarrier)
  ≡
  true
canonicalYukawaFromCarrierRecordsFirstGenerationUpUltrametricDepth =
  refl

canonicalYukawaFromCarrierRecordsCarrierDerivedEntries :
  carrierDerivedEntries
    (firstGenerationUpUltrametricDepthCarrier canonicalYukawaFromCarrier)
  ≡
  true
canonicalYukawaFromCarrierRecordsCarrierDerivedEntries =
  refl

canonicalYukawaFromCarrierKeepsPhysicalValuesUninhabited :
  physicalValuesInhabited
    (firstGenerationUpUltrametricDepthCarrier canonicalYukawaFromCarrier)
  ≡
  false
canonicalYukawaFromCarrierKeepsPhysicalValuesUninhabited =
  refl

canonicalYukawaFromCarrierFirstGenerationUpDepthMatrixAgrees :
  FirstGenerationUpUltrametricDepthCarrier.carrierMatrix
    (firstGenerationUpUltrametricDepthCarrier canonicalYukawaFromCarrier)
  ≡
  upYukawaMatrix canonicalYukawaFromCarrier
canonicalYukawaFromCarrierFirstGenerationUpDepthMatrixAgrees =
  refl

canonicalYukawaFromCarrierUpperTriangularOffDiagonalInhabited :
  offDiagonalEntriesInhabited
    (upperTriangularUpOffDiagonalReceipt canonicalYukawaFromCarrier)
  ≡
  true
canonicalYukawaFromCarrierUpperTriangularOffDiagonalInhabited =
  refl

canonicalYukawaFromCarrierUpperTriangularPhysicalScaleUnknown :
  physicalCouplingScaleUnknown
    (upperTriangularUpOffDiagonalReceipt canonicalYukawaFromCarrier)
  ≡
  true
canonicalYukawaFromCarrierUpperTriangularPhysicalScaleUnknown =
  refl

canonicalYukawaFromCarrierUpperTriangularPhysicalValuesNotPromoted :
  physicalValuesPromoted
    (upperTriangularUpOffDiagonalReceipt canonicalYukawaFromCarrier)
  ≡
  false
canonicalYukawaFromCarrierUpperTriangularPhysicalValuesNotPromoted =
  refl

canonicalYukawaFromCarrierUpperTriangularCKMPromotionClosed :
  ckmPromotionConstructed
    (upperTriangularUpOffDiagonalReceipt canonicalYukawaFromCarrier)
  ≡
  false
canonicalYukawaFromCarrierUpperTriangularCKMPromotionClosed =
  refl

canonicalYukawaFromCarrierKeepsU1PhysicalRepresentationClosed :
  yukawaDHRU1PhysicalSectorRepresentationConstructed
    canonicalYukawaFromCarrier
  ≡
  false
canonicalYukawaFromCarrierKeepsU1PhysicalRepresentationClosed =
  refl

canonicalYukawaFromCarrierThreadsSU2DoubletShapeCheck :
  yukawaDHRSU2DoubletShapeCheckConstructed canonicalYukawaFromCarrier
  ≡
  true
canonicalYukawaFromCarrierThreadsSU2DoubletShapeCheck =
  refl

canonicalYukawaFromCarrierKeepsSU2PhysicalRepresentationClosed :
  yukawaDHRSU2PhysicalMatrixRepresentationConstructed
    canonicalYukawaFromCarrier
  ≡
  false
canonicalYukawaFromCarrierKeepsSU2PhysicalRepresentationClosed =
  refl

canonicalYukawaFromCarrierKeepsActualDHRSectorsClosed :
  yukawaDHRActualSectorRepresentationsConstructed
    canonicalYukawaFromCarrier
  ≡
  false
canonicalYukawaFromCarrierKeepsActualDHRSectorsClosed =
  refl

canonicalYukawaFromCarrierKeepsPhysicalMatricesClosed :
  yukawaDHRPhysicalYukawaMatricesSupplied
    canonicalYukawaFromCarrier
  ≡
  false
canonicalYukawaFromCarrierKeepsPhysicalMatricesClosed =
  refl
