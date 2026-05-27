module DASHI.Physics.Closure.CKMExactWitnesses where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.MatterRepresentationReceiptSurface as Matter
open import DASHI.Physics.YM.BiunitaryDiagonalization
  using (DiagonalBiunitaryWitness; canonicalDiagonalBiunitaryWitness)
open import DASHI.Physics.YM.FroggattNielsenExpansion using
  (FroggattNielsenWitness; canonicalFroggattNielsenWitness)
open import DASHI.Physics.YM.WolfensteinCKM using
  (WolfensteinCKMWitness; canonicalWolfensteinCKMWitness)

------------------------------------------------------------------------
-- Exact CKM/Yukawa upstream witnesses.
--
-- This module stays upstream of the receipt surfaces.  It packages concrete
-- diagonal Yukawa data together with the exact identity biunitary/CKM chain
-- that is already definitional in the repository's concrete 3x3 matrix type.

zeroGaussian : Matter.MixingGaussianRationalDatum
zeroGaussian = Matter.zeroMixingGaussianRationalDatum

exactGaussian :
  Nat →
  Nat →
  Matter.MixingGaussianRationalDatum
exactGaussian numerator denominator =
  Matter.mixingGaussianRationalDatum
    (Matter.mixingSignedRationalDatum numerator denominator true)
    Matter.zeroMixingSignedRationalDatum

diag3 :
  Matter.MixingGaussianRationalDatum →
  Matter.MixingGaussianRationalDatum →
  Matter.MixingGaussianRationalDatum →
  Matter.MixingMatrix
diag3 a b c =
  Matter.mixingMatrix3x3
    a zeroGaussian zeroGaussian
    zeroGaussian b zeroGaussian
    zeroGaussian zeroGaussian c

record DiagonalYukawa3x3 : Set where
  constructor diagonalYukawa3x3
  field
    y11 y22 y33 : Matter.MixingGaussianRationalDatum
    matrix : Matter.MixingMatrix
    matrixIsDiagonal : matrix ≡ diag3 y11 y22 y33

open DiagonalYukawa3x3 public

canonicalUpYukawa3x3 : DiagonalYukawa3x3
canonicalUpYukawa3x3 =
  diagonalYukawa3x3
    (exactGaussian 1 1)
    (exactGaussian 2 1)
    (exactGaussian 3 1)
    (diag3 (exactGaussian 1 1) (exactGaussian 2 1) (exactGaussian 3 1))
    refl

canonicalDownYukawa3x3 : DiagonalYukawa3x3
canonicalDownYukawa3x3 =
  diagonalYukawa3x3
    (exactGaussian 5 2460000)
    (exactGaussian 93 246000)
    (exactGaussian 4180 246000)
    (diag3 (exactGaussian 5 2460000) (exactGaussian 93 246000)
           (exactGaussian 4180 246000))
    refl

record ExactBiunitaryDiagonalizationWitness : Set where
  field
    upYukawa : DiagonalYukawa3x3
    downYukawa : DiagonalYukawa3x3
    upDiagonalizer : Matter.MixingMatrix
    downDiagonalizer : Matter.MixingMatrix
    upDiagonalizerIsIdentity :
      upDiagonalizer ≡ Matter.identityMixingMatrix
    downDiagonalizerIsIdentity :
      downDiagonalizer ≡ Matter.identityMixingMatrix
    biunitaryCarrier :
      DiagonalBiunitaryWitness

open ExactBiunitaryDiagonalizationWitness public

canonicalExactBiunitaryDiagonalizationWitness :
  ExactBiunitaryDiagonalizationWitness
canonicalExactBiunitaryDiagonalizationWitness = record
  { upYukawa = canonicalUpYukawa3x3
  ; downYukawa = canonicalDownYukawa3x3
  ; upDiagonalizer = Matter.identityMixingMatrix
  ; downDiagonalizer = Matter.identityMixingMatrix
  ; upDiagonalizerIsIdentity = refl
  ; downDiagonalizerIsIdentity = refl
  ; biunitaryCarrier = canonicalDiagonalBiunitaryWitness
  }

record CKMProductClosureWitness : Set where
  field
    ckmMatrix : Matter.MixingMatrix
    ckmMatrixIsIdentity :
      ckmMatrix ≡ Matter.identityMixingMatrix
    leftIdentityClosure :
      Matter.leftIdentityMixingProduct ckmMatrix ≡ ckmMatrix

open CKMProductClosureWitness public

canonicalCKMProductClosureWitness : CKMProductClosureWitness
canonicalCKMProductClosureWitness = record
  { ckmMatrix = Matter.identityMixingMatrix
  ; ckmMatrixIsIdentity = refl
  ; leftIdentityClosure = refl
  }

record UnitarityResidualWitness : Set where
  field
    ckmMatrix : Matter.MixingMatrix
    residualMatrix : Matter.MixingMatrix
    residualMatrixIsZero :
      residualMatrix ≡
      Matter.mixingMatrix3x3
        zeroGaussian zeroGaussian zeroGaussian
        zeroGaussian zeroGaussian zeroGaussian
        zeroGaussian zeroGaussian zeroGaussian
    exactResidualForIdentityCKM :
      ckmMatrix ≡ Matter.identityMixingMatrix

open UnitarityResidualWitness public

canonicalUnitarityResidualWitness : UnitarityResidualWitness
canonicalUnitarityResidualWitness = record
  { ckmMatrix = Matter.identityMixingMatrix
  ; residualMatrix =
      Matter.mixingMatrix3x3
        zeroGaussian zeroGaussian zeroGaussian
        zeroGaussian zeroGaussian zeroGaussian
        zeroGaussian zeroGaussian zeroGaussian
  ; residualMatrixIsZero = refl
  ; exactResidualForIdentityCKM = refl
  }

record CarrierMixingTheoremWitness : Set where
  field
    biunitary : ExactBiunitaryDiagonalizationWitness
    ckmProduct : CKMProductClosureWitness
    carrierMixingMatrix : Matter.MixingMatrix
    carrierMixingMatrixIsIdentity :
      carrierMixingMatrix ≡ Matter.identityMixingMatrix
    carrierMixingProductClosed :
      Matter.leftIdentityMixingProduct carrierMixingMatrix ≡ carrierMixingMatrix

open CarrierMixingTheoremWitness public

canonicalCarrierMixingTheoremWitness : CarrierMixingTheoremWitness
canonicalCarrierMixingTheoremWitness = record
  { biunitary = canonicalExactBiunitaryDiagonalizationWitness
  ; ckmProduct = canonicalCKMProductClosureWitness
  ; carrierMixingMatrix = Matter.identityMixingMatrix
  ; carrierMixingMatrixIsIdentity = refl
  ; carrierMixingProductClosed = refl
  }

record YukawaDHRIntertwinerCompatibilityWitness : Set where
  field
    dhrAction : Matter.MixingMatrix → Matter.MixingMatrix
    upCompatible :
      dhrAction (DiagonalYukawa3x3.matrix canonicalUpYukawa3x3)
      ≡ DiagonalYukawa3x3.matrix canonicalUpYukawa3x3
    downCompatible :
      dhrAction (DiagonalYukawa3x3.matrix canonicalDownYukawa3x3)
      ≡ DiagonalYukawa3x3.matrix canonicalDownYukawa3x3
    identityOnCarrier :
      ∀ m → dhrAction m ≡ m

open YukawaDHRIntertwinerCompatibilityWitness public

canonicalYukawaDHRIntertwinerCompatibilityWitness :
  YukawaDHRIntertwinerCompatibilityWitness
canonicalYukawaDHRIntertwinerCompatibilityWitness = record
  { dhrAction = λ m → m
  ; upCompatible = refl
  ; downCompatible = refl
  ; identityOnCarrier = λ m → refl
  }

record CKMExactWitnessChain : Set where
  field
    biunitaryDiagonalization :
      ExactBiunitaryDiagonalizationWitness
    productClosure :
      CKMProductClosureWitness
    unitarityResidual :
      UnitarityResidualWitness
    carrierMixingTheorem :
      CarrierMixingTheoremWitness
    yukawaDHRIntertwinerCompatibility :
      YukawaDHRIntertwinerCompatibilityWitness

open CKMExactWitnessChain public

canonicalCKMExactWitnessChain : CKMExactWitnessChain
canonicalCKMExactWitnessChain = record
  { biunitaryDiagonalization =
      canonicalExactBiunitaryDiagonalizationWitness
  ; productClosure =
      canonicalCKMProductClosureWitness
  ; unitarityResidual =
      canonicalUnitarityResidualWitness
  ; carrierMixingTheorem =
      canonicalCarrierMixingTheoremWitness
  ; yukawaDHRIntertwinerCompatibility =
      canonicalYukawaDHRIntertwinerCompatibilityWitness
  }

record FroggattNielsenPhysicalCKMWitness : Setω where
  field
    froggattNielsenWitness : FroggattNielsenWitness
    wolfensteinWitness : WolfensteinCKMWitness
    ckmMatrix : Matter.MixingMatrix
    ckmMatrixIsCanonical :
      ckmMatrix ≡ Matter.canonicalWolfensteinMixingMatrix
    residualMatrix : Matter.MixingMatrix
    residualMatrixIsCanonical :
      residualMatrix ≡
      Matter.canonicalWolfensteinVVdaggerMinusIdentityResidual
    boundary : List String

open FroggattNielsenPhysicalCKMWitness public

canonicalFroggattNielsenPhysicalCKMWitness :
  FroggattNielsenPhysicalCKMWitness
canonicalFroggattNielsenPhysicalCKMWitness = record
  { froggattNielsenWitness = canonicalFroggattNielsenWitness
  ; wolfensteinWitness = canonicalWolfensteinCKMWitness
  ; ckmMatrix = Matter.canonicalWolfensteinMixingMatrix
  ; ckmMatrixIsCanonical = refl
  ; residualMatrix =
      Matter.canonicalWolfensteinVVdaggerMinusIdentityResidual
  ; residualMatrixIsCanonical = refl
  ; boundary =
      "The physical CKM lane is packaged as the concrete FN/Wolfenstein witness bundle"
      ∷ "The existing matter-surface carrier provides the concrete matrix data"
      ∷ "This witness remains a package, not a promotion of the exact carrier theorem"
      ∷ []
  }

------------------------------------------------------------------------
-- Fail-closed splitting-field / eigenbasis ledger.

data CKMSplittingFieldEigenbasisBlocker : Set where
  missingGenericYukawaSplittingField :
    CKMSplittingFieldEigenbasisBlocker

  missingNonDiagonalYukawaEigenbasis :
    CKMSplittingFieldEigenbasisBlocker

  missingBiunitaryTransportOutOfIdentityCase :
    CKMSplittingFieldEigenbasisBlocker

  missingWeakMassBasisIdentificationForPhysicalCKM :
    CKMSplittingFieldEigenbasisBlocker

canonicalCKMSplittingFieldEigenbasisBlockers :
  List CKMSplittingFieldEigenbasisBlocker
canonicalCKMSplittingFieldEigenbasisBlockers =
  missingGenericYukawaSplittingField
  ∷ missingNonDiagonalYukawaEigenbasis
  ∷ missingBiunitaryTransportOutOfIdentityCase
  ∷ missingWeakMassBasisIdentificationForPhysicalCKM
  ∷ []

record CKMSplittingFieldEigenbasisFailClosedLedger : Setω where
  field
    exactWitnessChain :
      CKMExactWitnessChain

    carrierMixingTheorem :
      CarrierMixingTheoremWitness

    carrierCKMMatrix :
      Matter.MixingMatrix

    carrierCKMMatrixIsIdentity :
      carrierCKMMatrix ≡ Matter.identityMixingMatrix

    blockers :
      List CKMSplittingFieldEigenbasisBlocker

    blockersAreCanonical :
      blockers ≡ canonicalCKMSplittingFieldEigenbasisBlockers

    firstBlocker :
      CKMSplittingFieldEigenbasisBlocker

    firstBlockerIsSplittingField :
      firstBlocker ≡ missingGenericYukawaSplittingField

    splittingFieldConstructed :
      Bool

    splittingFieldConstructedIsFalse :
      splittingFieldConstructed ≡ false

    eigenbasisConstructed :
      Bool

    eigenbasisConstructedIsFalse :
      eigenbasisConstructed ≡ false

    weakMassBasisIdentificationConstructed :
      Bool

    weakMassBasisIdentificationConstructedIsFalse :
      weakMassBasisIdentificationConstructed ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    ledgerBoundary :
      List String

open CKMSplittingFieldEigenbasisFailClosedLedger public

canonicalCKMSplittingFieldEigenbasisFailClosedLedger :
  CKMSplittingFieldEigenbasisFailClosedLedger
canonicalCKMSplittingFieldEigenbasisFailClosedLedger = record
  { exactWitnessChain = canonicalCKMExactWitnessChain
  ; carrierMixingTheorem = canonicalCarrierMixingTheoremWitness
  ; carrierCKMMatrix = Matter.identityMixingMatrix
  ; carrierCKMMatrixIsIdentity = refl
  ; blockers = canonicalCKMSplittingFieldEigenbasisBlockers
  ; blockersAreCanonical = refl
  ; firstBlocker = missingGenericYukawaSplittingField
  ; firstBlockerIsSplittingField = refl
  ; splittingFieldConstructed = false
  ; splittingFieldConstructedIsFalse = refl
  ; eigenbasisConstructed = false
  ; eigenbasisConstructedIsFalse = refl
  ; weakMassBasisIdentificationConstructed = false
  ; weakMassBasisIdentificationConstructedIsFalse = refl
  ; physicalCKMPromoted = false
  ; physicalCKMPromotedIsFalse = refl
  ; ledgerBoundary =
      "The exact carrier theorem is the diagonal identity case on the concrete 3x3 carrier"
      ∷ "No generic Yukawa splitting field or non-diagonal eigenbasis is constructed by this witness chain"
      ∷ "Weak-to-mass basis identification for physical CKM remains a typed blocker"
      ∷ "The ledger is fail-closed: it records blockers and false promotion flags only"
      ∷ []
  }

ckmSplittingFieldEigenbasisLedgerFirstBlocker :
  firstBlocker canonicalCKMSplittingFieldEigenbasisFailClosedLedger
  ≡
  missingGenericYukawaSplittingField
ckmSplittingFieldEigenbasisLedgerFirstBlocker =
  refl

ckmSplittingFieldEigenbasisLedgerDoesNotPromote :
  physicalCKMPromoted canonicalCKMSplittingFieldEigenbasisFailClosedLedger
  ≡
  false
ckmSplittingFieldEigenbasisLedgerDoesNotPromote =
  refl
