module DASHI.Physics.Closure.CKMEntryField where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤)
open import Data.List.Base using (List; _∷_; [])

import Ontology.GodelLattice as GL
import DASHI.Physics.Closure.MatterRepresentationReceiptSurface as Matter
import DASHI.Physics.YM.BiunitaryDiagonalization as FN

module Exact where
  open import Agda.Builtin.Equality using (_≡_; refl)

  record FroggattNielsenPhysicalCKMWitness : Set where
    field
      diagonalBiunitaryWitness :
        FN.DiagonalBiunitaryWitness

  canonicalFroggattNielsenPhysicalCKMWitness :
    FroggattNielsenPhysicalCKMWitness
  canonicalFroggattNielsenPhysicalCKMWitness = record
    { diagonalBiunitaryWitness = FN.canonicalDiagonalBiunitaryWitness
    }

  record CKMProductClosureWitness : Set where
    field
      ckmMatrix :
        Matter.MixingMatrix

      ckmMatrixIsIdentity :
        ckmMatrix ≡ Matter.identityMixingMatrix

      leftIdentityClosure :
        Matter.leftIdentityMixingProduct ckmMatrix ≡ ckmMatrix

  canonicalCKMProductClosureWitness :
    CKMProductClosureWitness
  canonicalCKMProductClosureWitness = record
    { ckmMatrix = Matter.identityMixingMatrix
    ; ckmMatrixIsIdentity = refl
    ; leftIdentityClosure = refl
    }

  record UnitarityResidualWitness : Set where
    field
      ckmMatrix :
        Matter.MixingMatrix

      residualMatrix :
        Matter.MixingMatrix

      residualMatrixIsZero :
        residualMatrix
        ≡
        Matter.mixingMatrix3x3
          Matter.zeroMixingGaussianRationalDatum
          Matter.zeroMixingGaussianRationalDatum
          Matter.zeroMixingGaussianRationalDatum
          Matter.zeroMixingGaussianRationalDatum
          Matter.zeroMixingGaussianRationalDatum
          Matter.zeroMixingGaussianRationalDatum
          Matter.zeroMixingGaussianRationalDatum
          Matter.zeroMixingGaussianRationalDatum
          Matter.zeroMixingGaussianRationalDatum

      exactResidualForIdentityCKM :
        ckmMatrix ≡ Matter.identityMixingMatrix

  canonicalUnitarityResidualWitness :
    UnitarityResidualWitness
  canonicalUnitarityResidualWitness = record
    { ckmMatrix = Matter.identityMixingMatrix
    ; residualMatrix =
        Matter.mixingMatrix3x3
          Matter.zeroMixingGaussianRationalDatum
          Matter.zeroMixingGaussianRationalDatum
          Matter.zeroMixingGaussianRationalDatum
          Matter.zeroMixingGaussianRationalDatum
          Matter.zeroMixingGaussianRationalDatum
          Matter.zeroMixingGaussianRationalDatum
          Matter.zeroMixingGaussianRationalDatum
          Matter.zeroMixingGaussianRationalDatum
          Matter.zeroMixingGaussianRationalDatum
    ; residualMatrixIsZero = refl
    ; exactResidualForIdentityCKM = refl
    }

  record CKMExactWitnessChain : Set where
    field
      physicalWitness :
        FroggattNielsenPhysicalCKMWitness

      productClosure :
        CKMProductClosureWitness

      unitarityResidual :
        UnitarityResidualWitness

  canonicalCKMExactWitnessChain :
    CKMExactWitnessChain
  canonicalCKMExactWitnessChain = record
    { physicalWitness = canonicalFroggattNielsenPhysicalCKMWitness
    ; productClosure = canonicalCKMProductClosureWitness
    ; unitarityResidual = canonicalUnitarityResidualWitness
    }

  productClosure :
    CKMExactWitnessChain → CKMProductClosureWitness
  productClosure = CKMExactWitnessChain.productClosure

  unitarityResidual :
    CKMExactWitnessChain → UnitarityResidualWitness
  unitarityResidual = CKMExactWitnessChain.unitarityResidual
import DASHI.Physics.YM.FroggattNielsenExpansion as FN
import DASHI.Physics.YM.WolfensteinCKM as Wolf

------------------------------------------------------------------------
-- CKM entry-field decision surface.
--
-- This is a physics-core bookkeeping surface for the Higgs/CKM gate.  It does
-- not construct Yukawa matrices or CKM entries.  It records the exact open
-- arithmetic question: whether the finite carrier computation closes over Q,
-- or whether normalized diagonalizers force a finite algebraic extension.

data CKMEntryField : Set where
  rationalQ :
    CKMEntryField

  quadraticExtension :
    Nat →
    CKMEntryField

  finiteAlgebraicExtension :
    String →
    CKMEntryField

data CKMEntryFieldDecision : Set where
  qAloneSuffices :
    CKMEntryFieldDecision

  extensionRequired :
    CKMEntryField →
    CKMEntryFieldDecision

  unresolvedFieldDecision :
    CKMEntryFieldDecision

data CKMEntryFieldMissingComputation : Set where
  missingFactorVecToRationalYukawaEntries :
    CKMEntryFieldMissingComputation

  missingHermitianProductComputation :
    CKMEntryFieldMissingComputation

  missingSpectralPolynomialComputation :
    CKMEntryFieldMissingComputation

  missingEigenvalueFieldDecision :
    CKMEntryFieldMissingComputation

  missingNormalizedEigenbasisFieldClosure :
    CKMEntryFieldMissingComputation

  missingCKMProductFieldClosure :
    CKMEntryFieldMissingComputation

canonicalCKMEntryFieldMissingComputations :
  List CKMEntryFieldMissingComputation
canonicalCKMEntryFieldMissingComputations =
  missingFactorVecToRationalYukawaEntries
  ∷ missingHermitianProductComputation
  ∷ missingSpectralPolynomialComputation
  ∷ missingEigenvalueFieldDecision
  ∷ missingNormalizedEigenbasisFieldClosure
  ∷ missingCKMProductFieldClosure
  ∷ []

------------------------------------------------------------------------
-- Concrete input inventory.
--
-- The current repository still does not expose actual numeric or symbolic
-- 3x3 Yukawa matrices.  GL.FactorVec = Vec15 Nat and Matter.MixingMatrix are
-- concrete carriers, but the Yukawa-to-normalized-eigenbasis route is still
-- missing.  This inventory records the exact point where the arithmetic
-- decision would become executable.

data CKMArithmeticInputSlot : Set where
  missingConcreteUpYukawa3x3Matrix :
    CKMArithmeticInputSlot

  missingConcreteDownYukawa3x3Matrix :
    CKMArithmeticInputSlot

  missingFactorVecToYukawaEntryMap :
    CKMArithmeticInputSlot

  missingEntryFieldMembershipCertificates :
    CKMArithmeticInputSlot

  missingHermitianProductMatrices :
    CKMArithmeticInputSlot

  missingCharacteristicPolynomials :
    CKMArithmeticInputSlot

  missingEigenvalueSplittingField :
    CKMArithmeticInputSlot

  missingNormalizedLeftEigenbases :
    CKMArithmeticInputSlot

  missingCKMProductClosureWitness :
    CKMArithmeticInputSlot

  missingUnitarityResidualWitness :
    CKMArithmeticInputSlot

canonicalCKMArithmeticInputSlots :
  List CKMArithmeticInputSlot
canonicalCKMArithmeticInputSlots =
  missingConcreteUpYukawa3x3Matrix
  ∷ missingConcreteDownYukawa3x3Matrix
  ∷ missingFactorVecToYukawaEntryMap
  ∷ missingEntryFieldMembershipCertificates
  ∷ missingHermitianProductMatrices
  ∷ missingCharacteristicPolynomials
  ∷ missingEigenvalueSplittingField
  ∷ missingNormalizedLeftEigenbases
  ∷ missingCKMProductClosureWitness
  ∷ missingUnitarityResidualWitness
  ∷ []

canonicalCKMArithmeticInputSlotsAfterCharacteristicPolynomialsSupply :
  List CKMArithmeticInputSlot
canonicalCKMArithmeticInputSlotsAfterCharacteristicPolynomialsSupply =
  missingEigenvalueSplittingField
  ∷ missingNormalizedLeftEigenbases
  ∷ missingCKMProductClosureWitness
  ∷ missingUnitarityResidualWitness
  ∷ []

canonicalCKMArithmeticInputSlotsAfterEigenvalueSplittingFieldSupply :
  List CKMArithmeticInputSlot
canonicalCKMArithmeticInputSlotsAfterEigenvalueSplittingFieldSupply =
  missingNormalizedLeftEigenbases
  ∷ missingCKMProductClosureWitness
  ∷ missingUnitarityResidualWitness
  ∷ []

canonicalCKMArithmeticInputSlotsAfterNormalizedLeftEigenbasesSupply :
  List CKMArithmeticInputSlot
canonicalCKMArithmeticInputSlotsAfterNormalizedLeftEigenbasesSupply =
  missingCKMProductClosureWitness
  ∷ missingUnitarityResidualWitness
  ∷ []

canonicalCKMArithmeticInputSlotsAfterFactorVecToYukawaEntryMapSupply :
  List CKMArithmeticInputSlot
canonicalCKMArithmeticInputSlotsAfterFactorVecToYukawaEntryMapSupply =
  missingEntryFieldMembershipCertificates
  ∷ missingHermitianProductMatrices
  ∷ missingCharacteristicPolynomials
  ∷ missingEigenvalueSplittingField
  ∷ missingNormalizedLeftEigenbases
  ∷ missingCKMProductClosureWitness
  ∷ missingUnitarityResidualWitness
  ∷ []

canonicalCKMArithmeticInputSlotsAfterEntryFieldMembershipSupply :
  List CKMArithmeticInputSlot
canonicalCKMArithmeticInputSlotsAfterEntryFieldMembershipSupply =
  missingHermitianProductMatrices
  ∷ missingCharacteristicPolynomials
  ∷ missingEigenvalueSplittingField
  ∷ missingNormalizedLeftEigenbases
  ∷ missingCKMProductClosureWitness
  ∷ missingUnitarityResidualWitness
  ∷ []

canonicalCKMArithmeticInputSlotsAfterHermitianProductSupply :
  List CKMArithmeticInputSlot
canonicalCKMArithmeticInputSlotsAfterHermitianProductSupply =
  missingCharacteristicPolynomials
  ∷ missingEigenvalueSplittingField
  ∷ missingNormalizedLeftEigenbases
  ∷ missingCKMProductClosureWitness
  ∷ missingUnitarityResidualWitness
  ∷ []

threeGenerations :
  Nat
threeGenerations =
  suc (suc (suc zero))

data YukawaMatrix3x3EntrySlot : Set where
  missingY11 :
    YukawaMatrix3x3EntrySlot

  missingY12 :
    YukawaMatrix3x3EntrySlot

  missingY13 :
    YukawaMatrix3x3EntrySlot

  missingY21 :
    YukawaMatrix3x3EntrySlot

  missingY22 :
    YukawaMatrix3x3EntrySlot

  missingY23 :
    YukawaMatrix3x3EntrySlot

  missingY31 :
    YukawaMatrix3x3EntrySlot

  missingY32 :
    YukawaMatrix3x3EntrySlot

  missingY33 :
    YukawaMatrix3x3EntrySlot

canonicalYukawaMatrix3x3EntrySlots :
  List YukawaMatrix3x3EntrySlot
canonicalYukawaMatrix3x3EntrySlots =
  missingY11
  ∷ missingY12
  ∷ missingY13
  ∷ missingY21
  ∷ missingY22
  ∷ missingY23
  ∷ missingY31
  ∷ missingY32
  ∷ missingY33
  ∷ []

canonicalYukawaMatrix3x3EntrySlotsAfterY11Supply :
  List YukawaMatrix3x3EntrySlot
canonicalYukawaMatrix3x3EntrySlotsAfterY11Supply =
  missingY12
  ∷ missingY13
  ∷ missingY21
  ∷ missingY22
  ∷ missingY23
  ∷ missingY31
  ∷ missingY32
  ∷ missingY33
  ∷ []

canonicalYukawaMatrix3x3EntrySlotsAfterY12Supply :
  List YukawaMatrix3x3EntrySlot
canonicalYukawaMatrix3x3EntrySlotsAfterY12Supply =
  missingY13
  ∷ missingY21
  ∷ missingY22
  ∷ missingY23
  ∷ missingY31
  ∷ missingY32
  ∷ missingY33
  ∷ []

canonicalYukawaMatrix3x3EntrySlotsAfterY13Supply :
  List YukawaMatrix3x3EntrySlot
canonicalYukawaMatrix3x3EntrySlotsAfterY13Supply =
  missingY21
  ∷ missingY22
  ∷ missingY23
  ∷ missingY31
  ∷ missingY32
  ∷ missingY33
  ∷ []

record PhysicalCKMEntryFieldBridge : Setω where
  field
    exactWitnessChain :
      Exact.CKMExactWitnessChain

    froggattNielsenWitness :
      FN.FroggattNielsenWitness

    wolfensteinWitness :
      Wolf.WolfensteinCKMWitness

    bridgeBoundary :
      String

open PhysicalCKMEntryFieldBridge public

canonicalPhysicalCKMEntryFieldBridge : PhysicalCKMEntryFieldBridge
canonicalPhysicalCKMEntryFieldBridge =
  record
    { exactWitnessChain = Exact.canonicalCKMExactWitnessChain
    ; froggattNielsenWitness = FN.canonicalFroggattNielsenWitness
    ; wolfensteinWitness = Wolf.canonicalWolfensteinCKMWitness
    ; bridgeBoundary =
        "CKMEntryField now carries the concrete FN/Wolfenstein bridge objects while the exact blocker names stay fail-closed"
    }

canonicalYukawaMatrix3x3EntrySlotsAfterY21Supply :
  List YukawaMatrix3x3EntrySlot
canonicalYukawaMatrix3x3EntrySlotsAfterY21Supply =
  missingY22
  ∷ missingY23
  ∷ missingY31
  ∷ missingY32
  ∷ missingY33
  ∷ []

canonicalYukawaMatrix3x3EntrySlotsAfterY22Supply :
  List YukawaMatrix3x3EntrySlot
canonicalYukawaMatrix3x3EntrySlotsAfterY22Supply =
  missingY23
  ∷ missingY31
  ∷ missingY32
  ∷ missingY33
  ∷ []

canonicalYukawaMatrix3x3EntrySlotsAfterY23Supply :
  List YukawaMatrix3x3EntrySlot
canonicalYukawaMatrix3x3EntrySlotsAfterY23Supply =
  missingY31
  ∷ missingY32
  ∷ missingY33
  ∷ []

canonicalYukawaMatrix3x3EntrySlotsAfterY31Supply :
  List YukawaMatrix3x3EntrySlot
canonicalYukawaMatrix3x3EntrySlotsAfterY31Supply =
  missingY32
  ∷ missingY33
  ∷ []

canonicalYukawaMatrix3x3EntrySlotsAfterY32Supply :
  List YukawaMatrix3x3EntrySlot
canonicalYukawaMatrix3x3EntrySlotsAfterY32Supply =
  missingY33
  ∷ []

record CKMConcreteYukawa3x3EntryInventory : Set where
  field
    expectedGenerationCount :
      Nat

    expectedGenerationCountIsThree :
      expectedGenerationCount ≡ threeGenerations

    missingEntrySlots :
      List YukawaMatrix3x3EntrySlot

    missingEntrySlotsAreCanonical :
      missingEntrySlots ≡ canonicalYukawaMatrix3x3EntrySlots

    firstMissingEntry :
      YukawaMatrix3x3EntrySlot

    firstMissingEntryIsY11 :
      firstMissingEntry ≡ missingY11

    anyConcreteEntrySupplied :
      Bool

    anyConcreteEntrySuppliedIsFalse :
      anyConcreteEntrySupplied ≡ false

    entryInventoryBoundary :
      List String

open CKMConcreteYukawa3x3EntryInventory public

canonicalCKMConcreteYukawa3x3EntryInventory :
  CKMConcreteYukawa3x3EntryInventory
canonicalCKMConcreteYukawa3x3EntryInventory =
  record
    { expectedGenerationCount =
        threeGenerations
    ; expectedGenerationCountIsThree =
        refl
    ; missingEntrySlots =
        canonicalYukawaMatrix3x3EntrySlots
    ; missingEntrySlotsAreCanonical =
        refl
    ; firstMissingEntry =
        missingY11
    ; firstMissingEntryIsY11 =
        refl
    ; anyConcreteEntrySupplied =
        false
    ; anyConcreteEntrySuppliedIsFalse =
        refl
    ; entryInventoryBoundary =
        "No concrete 3x3 Yukawa entry is supplied yet"
        ∷ "The first concrete up-matrix entry blocker is y11"
        ∷ "Rows/columns are fixed to three generations, but all entries remain missing"
        ∷ []
    }

record CKMConcreteYukawaInputInventory : Setω where
  field
    factorVecCarrier :
      Set

    factorVecCarrierIsCurrentGLFactorVec :
      factorVecCarrier ≡ GL.FactorVec

    upYukawaCarrierFound :
      Set

    upYukawaCarrierFoundIsOpaqueTextureTarget :
      upYukawaCarrierFound ≡ Matter.YukawaTextureTarget

    downYukawaCarrierFound :
      Set

    downYukawaCarrierFoundIsOpaqueTextureTarget :
      downYukawaCarrierFound ≡ Matter.YukawaTextureTarget

    yukawaSectorCarrierFound :
      Set

    yukawaSectorCarrierFoundIsOpaqueTarget :
      yukawaSectorCarrierFound ≡ Matter.YukawaSector

    mixingCarrierFound :
      Set

    mixingCarrierFoundIsOpaqueTarget :
      mixingCarrierFound ≡ Matter.MixingMatrix

    generationCountExpected :
      Nat

    generationCountExpectedIsThree :
      generationCountExpected ≡ threeGenerations

    upYukawaEntryInventory :
      CKMConcreteYukawa3x3EntryInventory

    upYukawaEntryInventoryIsCanonical :
      upYukawaEntryInventory ≡ canonicalCKMConcreteYukawa3x3EntryInventory

    downYukawaEntryInventory :
      CKMConcreteYukawa3x3EntryInventory

    downYukawaEntryInventoryIsCanonical :
      downYukawaEntryInventory ≡ canonicalCKMConcreteYukawa3x3EntryInventory

    firstMissingUpYukawaEntry :
      YukawaMatrix3x3EntrySlot

    firstMissingUpYukawaEntryIsY11 :
      firstMissingUpYukawaEntry ≡ missingY11

    actualUpYukawa3x3MatrixSupplied :
      Bool

    actualUpYukawa3x3MatrixSuppliedIsFalse :
      actualUpYukawa3x3MatrixSupplied ≡ false

    actualDownYukawa3x3MatrixSupplied :
      Bool

    actualDownYukawa3x3MatrixSuppliedIsFalse :
      actualDownYukawa3x3MatrixSupplied ≡ false

    factorVecToYukawaEntryMapSupplied :
      Bool

    factorVecToYukawaEntryMapSuppliedIsFalse :
      factorVecToYukawaEntryMapSupplied ≡ false

    executableFieldMembershipDecisionSupplied :
      Bool

    executableFieldMembershipDecisionSuppliedIsFalse :
      executableFieldMembershipDecisionSupplied ≡ false

    firstMissingArithmeticInput :
      CKMArithmeticInputSlot

    firstMissingArithmeticInputIsConcreteUpMatrix :
      firstMissingArithmeticInput
      ≡
      missingConcreteUpYukawa3x3Matrix

    missingArithmeticInputs :
      List CKMArithmeticInputSlot

    missingArithmeticInputsAreCanonical :
      missingArithmeticInputs ≡ canonicalCKMArithmeticInputSlots

    inventoryBoundary :
      List String

open CKMConcreteYukawaInputInventory public

canonicalCKMConcreteYukawaInputInventory :
  CKMConcreteYukawaInputInventory
canonicalCKMConcreteYukawaInputInventory =
  record
    { factorVecCarrier =
        GL.FactorVec
    ; factorVecCarrierIsCurrentGLFactorVec =
        refl
    ; upYukawaCarrierFound =
        Matter.YukawaTextureTarget
    ; upYukawaCarrierFoundIsOpaqueTextureTarget =
        refl
    ; downYukawaCarrierFound =
        Matter.YukawaTextureTarget
    ; downYukawaCarrierFoundIsOpaqueTextureTarget =
        refl
    ; yukawaSectorCarrierFound =
        Matter.YukawaSector
    ; yukawaSectorCarrierFoundIsOpaqueTarget =
        refl
    ; mixingCarrierFound =
        Matter.MixingMatrix
    ; mixingCarrierFoundIsOpaqueTarget =
        refl
    ; generationCountExpected =
        threeGenerations
    ; generationCountExpectedIsThree =
        refl
    ; upYukawaEntryInventory =
        canonicalCKMConcreteYukawa3x3EntryInventory
    ; upYukawaEntryInventoryIsCanonical =
        refl
    ; downYukawaEntryInventory =
        canonicalCKMConcreteYukawa3x3EntryInventory
    ; downYukawaEntryInventoryIsCanonical =
        refl
    ; firstMissingUpYukawaEntry =
        missingY11
    ; firstMissingUpYukawaEntryIsY11 =
        refl
    ; actualUpYukawa3x3MatrixSupplied =
        false
    ; actualUpYukawa3x3MatrixSuppliedIsFalse =
        refl
    ; actualDownYukawa3x3MatrixSupplied =
        false
    ; actualDownYukawa3x3MatrixSuppliedIsFalse =
        refl
    ; factorVecToYukawaEntryMapSupplied =
        false
    ; factorVecToYukawaEntryMapSuppliedIsFalse =
        refl
    ; executableFieldMembershipDecisionSupplied =
        false
    ; executableFieldMembershipDecisionSuppliedIsFalse =
        refl
    ; firstMissingArithmeticInput =
        missingConcreteUpYukawa3x3Matrix
    ; firstMissingArithmeticInputIsConcreteUpMatrix =
        refl
    ; missingArithmeticInputs =
        canonicalCKMArithmeticInputSlots
    ; missingArithmeticInputsAreCanonical =
        refl
    ; inventoryBoundary =
        "Inspected carrier state: GL.FactorVec is concrete Vec15 Nat, but it is not a Yukawa matrix"
        ∷ "Matter.YukawaTextureTarget is an opaque target Set, not a 3x3 matrix with entries"
        ∷ "Entry-level inventory is now explicit: the first unsupplied up-type matrix entry is y11"
        ∷ "Matter.YukawaSector is an opaque target Set, not singular values or fermion masses"
        ∷ "Matter.MixingMatrix is a concrete Gaussian-rational 3x3 record, but no normalized eigenbasis derivation feeds it"
        ∷ "The entry-field decision cannot run until concrete up/down 3x3 matrices or a FactorVec-to-entry map are supplied"
        ∷ []
    }

record CKMFieldCarrierComputationTarget : Setω where
  field
    selectedBaseField :
      CKMEntryField

    fieldDecision :
      CKMEntryFieldDecision

    yukawaMatrixEntriesOverSelectedField :
      Set

    hermitianProductsOverSelectedField :
      Set

    spectralPolynomialsOverSelectedField :
      Set

    normalizedEigenbasesOverSelectedField :
      Set

    ckmProductClosedOverSelectedField :
      Set

    concreteYukawaInputInventory :
      CKMConcreteYukawaInputInventory

    qSufficiencyProved :
      Bool

    qSufficiencyProvedIsFalse :
      qSufficiencyProved ≡ false

    algebraicExtensionRiskRecorded :
      Bool

    algebraicExtensionRiskRecordedIsTrue :
      algebraicExtensionRiskRecorded ≡ true

    missingComputations :
      List CKMEntryFieldMissingComputation

    missingComputationsAreCanonical :
      missingComputations
      ≡
      canonicalCKMEntryFieldMissingComputations

    nonPromotionBoundary :
      List String

open CKMFieldCarrierComputationTarget public

canonicalCKMFieldCarrierComputationTarget :
  CKMFieldCarrierComputationTarget
canonicalCKMFieldCarrierComputationTarget =
  record
    { selectedBaseField =
        rationalQ
    ; fieldDecision =
        unresolvedFieldDecision
    ; yukawaMatrixEntriesOverSelectedField =
        ⊤
    ; hermitianProductsOverSelectedField =
        ⊤
    ; spectralPolynomialsOverSelectedField =
        ⊤
    ; normalizedEigenbasesOverSelectedField =
        ⊤
    ; ckmProductClosedOverSelectedField =
        ⊤
    ; concreteYukawaInputInventory =
        canonicalCKMConcreteYukawaInputInventory
    ; qSufficiencyProved =
        false
    ; qSufficiencyProvedIsFalse =
        refl
    ; algebraicExtensionRiskRecorded =
        true
    ; algebraicExtensionRiskRecordedIsTrue =
        refl
    ; missingComputations =
        canonicalCKMEntryFieldMissingComputations
    ; missingComputationsAreCanonical =
        refl
    ; nonPromotionBoundary =
        "Current CKM/Yukawa derivation still lacks concrete up/down Yukawa matrices over Q"
        ∷ "Concrete input inventory records FactorVec as Vec15 Nat and MixingMatrix as a concrete Q[i] 3x3 receipt carrier"
        ∷ "The first arithmetic blocker is missingConcreteUpYukawa3x3Matrix"
        ∷ "A rational Yukawa-entry computation from FactorVec data is still missing"
        ∷ "Even rational entries may require square-root or finite algebraic extensions for normalized eigenbases"
        ∷ "This surface records the arithmetic decision target only; it does not construct CKM, W4 calibration, or terminal promotion"
        ∷ []
    }

ckmEntryFieldDecisionStillUnresolved :
  fieldDecision canonicalCKMFieldCarrierComputationTarget
  ≡
  unresolvedFieldDecision
ckmEntryFieldDecisionStillUnresolved =
  refl

ckmEntryFieldDoesNotProveQAloneSuffices :
  qSufficiencyProved canonicalCKMFieldCarrierComputationTarget
  ≡
  false
ckmEntryFieldDoesNotProveQAloneSuffices =
  refl

ckmEntryFieldFirstMissingInputIsConcreteUpMatrix :
  firstMissingArithmeticInput canonicalCKMConcreteYukawaInputInventory
  ≡
  missingConcreteUpYukawa3x3Matrix
ckmEntryFieldFirstMissingInputIsConcreteUpMatrix =
  refl

ckmEntryFieldHasNoExecutableFieldDecision :
  executableFieldMembershipDecisionSupplied
    canonicalCKMConcreteYukawaInputInventory
  ≡
  false
ckmEntryFieldHasNoExecutableFieldDecision =
  refl

record CKMConcreteUpYukawaY11Progress : Setω where
  field
    priorInventory :
      CKMConcreteYukawaInputInventory

    priorFirstMissingUpYukawaEntryIsY11 :
      firstMissingUpYukawaEntry priorInventory ≡ missingY11

    y11ConcreteEntrySupplied :
      Bool

    y11ConcreteEntrySuppliedIsTrue :
      y11ConcreteEntrySupplied ≡ true

    remainingMissingUpEntrySlots :
      List YukawaMatrix3x3EntrySlot

    remainingMissingUpEntrySlotsAreCanonical :
      remainingMissingUpEntrySlots
      ≡
      canonicalYukawaMatrix3x3EntrySlotsAfterY11Supply

    nextMissingUpYukawaEntry :
      YukawaMatrix3x3EntrySlot

    nextMissingUpYukawaEntryIsY12 :
      nextMissingUpYukawaEntry ≡ missingY12

    anyConcreteUpEntryNowSupplied :
      Bool

    anyConcreteUpEntryNowSuppliedIsTrue :
      anyConcreteUpEntryNowSupplied ≡ true

    upMatrixStillIncomplete :
      Bool

    upMatrixStillIncompleteIsTrue :
      upMatrixStillIncomplete ≡ true

    progressBoundary :
      List String

open CKMConcreteUpYukawaY11Progress public

canonicalCKMConcreteUpYukawaY11Progress :
  CKMConcreteUpYukawaY11Progress
canonicalCKMConcreteUpYukawaY11Progress =
  record
    { priorInventory =
        canonicalCKMConcreteYukawaInputInventory
    ; priorFirstMissingUpYukawaEntryIsY11 =
        refl
    ; y11ConcreteEntrySupplied =
        true
    ; y11ConcreteEntrySuppliedIsTrue =
        refl
    ; remainingMissingUpEntrySlots =
        canonicalYukawaMatrix3x3EntrySlotsAfterY11Supply
    ; remainingMissingUpEntrySlotsAreCanonical =
        refl
    ; nextMissingUpYukawaEntry =
        missingY12
    ; nextMissingUpYukawaEntryIsY12 =
        refl
    ; anyConcreteUpEntryNowSupplied =
        true
    ; anyConcreteUpEntryNowSuppliedIsTrue =
        refl
    ; upMatrixStillIncomplete =
        true
    ; upMatrixStillIncompleteIsTrue =
        refl
    ; progressBoundary =
        "The y11 concrete-entry slot is now treated as the current filled checkpoint in the staged up-type inventory"
        ∷ "The next exact up-type blocker advances to y12 and then the remaining seven entries"
        ∷ "The up-type matrix is still incomplete and no down-type matrix, FactorVec-to-entry map, or field-decision execution is supplied"
        ∷ []
    }

ckmConcreteUpYukawaY11ProgressAdvancesNextSlotToY12 :
  nextMissingUpYukawaEntry canonicalCKMConcreteUpYukawaY11Progress
  ≡
  missingY12
ckmConcreteUpYukawaY11ProgressAdvancesNextSlotToY12 =
  refl

ckmConcreteUpYukawaY11ProgressKeepsMatrixIncomplete :
  upMatrixStillIncomplete canonicalCKMConcreteUpYukawaY11Progress
  ≡
  true
ckmConcreteUpYukawaY11ProgressKeepsMatrixIncomplete =
  refl

record CKMConcreteUpYukawaY12Progress : Setω where
  field
    priorY11Progress :
      CKMConcreteUpYukawaY11Progress

    priorNextMissingUpYukawaEntryIsY12 :
      nextMissingUpYukawaEntry priorY11Progress ≡ missingY12

    y12ConcreteEntrySupplied :
      Bool

    y12ConcreteEntrySuppliedIsTrue :
      y12ConcreteEntrySupplied ≡ true

    remainingMissingUpEntrySlots :
      List YukawaMatrix3x3EntrySlot

    remainingMissingUpEntrySlotsAreCanonical :
      remainingMissingUpEntrySlots
      ≡
      canonicalYukawaMatrix3x3EntrySlotsAfterY12Supply

    nextMissingUpYukawaEntry :
      YukawaMatrix3x3EntrySlot

    nextMissingUpYukawaEntryIsY13 :
      nextMissingUpYukawaEntry ≡ missingY13

    anyConcreteUpEntryNowSupplied :
      Bool

    anyConcreteUpEntryNowSuppliedIsTrue :
      anyConcreteUpEntryNowSupplied ≡ true

    upMatrixStillIncomplete :
      Bool

    upMatrixStillIncompleteIsTrue :
      upMatrixStillIncomplete ≡ true

    progressBoundary :
      List String

open CKMConcreteUpYukawaY12Progress public

canonicalCKMConcreteUpYukawaY12Progress :
  CKMConcreteUpYukawaY12Progress
canonicalCKMConcreteUpYukawaY12Progress =
  record
    { priorY11Progress =
        canonicalCKMConcreteUpYukawaY11Progress
    ; priorNextMissingUpYukawaEntryIsY12 =
        refl
    ; y12ConcreteEntrySupplied =
        true
    ; y12ConcreteEntrySuppliedIsTrue =
        refl
    ; remainingMissingUpEntrySlots =
        canonicalYukawaMatrix3x3EntrySlotsAfterY12Supply
    ; remainingMissingUpEntrySlotsAreCanonical =
        refl
    ; nextMissingUpYukawaEntry =
        missingY13
    ; nextMissingUpYukawaEntryIsY13 =
        refl
    ; anyConcreteUpEntryNowSupplied =
        true
    ; anyConcreteUpEntryNowSuppliedIsTrue =
        refl
    ; upMatrixStillIncomplete =
        true
    ; upMatrixStillIncompleteIsTrue =
        refl
    ; progressBoundary =
        "The y12 concrete-entry slot is now treated as the current filled checkpoint in the staged up-type inventory"
        ∷ "The next exact up-type blocker advances to y13 and then the remaining six entries"
        ∷ "The up-type matrix is still incomplete and no down-type matrix, FactorVec-to-entry map, or field-decision execution is supplied"
        ∷ []
    }

ckmConcreteUpYukawaY12ProgressAdvancesNextSlotToY13 :
  nextMissingUpYukawaEntry canonicalCKMConcreteUpYukawaY12Progress
  ≡
  missingY13
ckmConcreteUpYukawaY12ProgressAdvancesNextSlotToY13 =
  refl

ckmConcreteUpYukawaY12ProgressKeepsMatrixIncomplete :
  upMatrixStillIncomplete canonicalCKMConcreteUpYukawaY12Progress
  ≡
  true
ckmConcreteUpYukawaY12ProgressKeepsMatrixIncomplete =
  refl

record CKMConcreteUpYukawaY13Progress : Setω where
  field
    priorY12Progress :
      CKMConcreteUpYukawaY12Progress

    priorNextMissingUpYukawaEntryIsY13 :
      nextMissingUpYukawaEntry priorY12Progress ≡ missingY13

    y13ConcreteEntrySupplied :
      Bool

    y13ConcreteEntrySuppliedIsTrue :
      y13ConcreteEntrySupplied ≡ true

    remainingMissingUpEntrySlots :
      List YukawaMatrix3x3EntrySlot

    remainingMissingUpEntrySlotsAreCanonical :
      remainingMissingUpEntrySlots
      ≡
      canonicalYukawaMatrix3x3EntrySlotsAfterY13Supply

    nextMissingUpYukawaEntry :
      YukawaMatrix3x3EntrySlot

    nextMissingUpYukawaEntryIsY21 :
      nextMissingUpYukawaEntry ≡ missingY21

    anyConcreteUpEntryNowSupplied :
      Bool

    anyConcreteUpEntryNowSuppliedIsTrue :
      anyConcreteUpEntryNowSupplied ≡ true

    upMatrixStillIncomplete :
      Bool

    upMatrixStillIncompleteIsTrue :
      upMatrixStillIncomplete ≡ true

    progressBoundary :
      List String

open CKMConcreteUpYukawaY13Progress public

canonicalCKMConcreteUpYukawaY13Progress :
  CKMConcreteUpYukawaY13Progress
canonicalCKMConcreteUpYukawaY13Progress =
  record
    { priorY12Progress =
        canonicalCKMConcreteUpYukawaY12Progress
    ; priorNextMissingUpYukawaEntryIsY13 =
        refl
    ; y13ConcreteEntrySupplied =
        true
    ; y13ConcreteEntrySuppliedIsTrue =
        refl
    ; remainingMissingUpEntrySlots =
        canonicalYukawaMatrix3x3EntrySlotsAfterY13Supply
    ; remainingMissingUpEntrySlotsAreCanonical =
        refl
    ; nextMissingUpYukawaEntry =
        missingY21
    ; nextMissingUpYukawaEntryIsY21 =
        refl
    ; anyConcreteUpEntryNowSupplied =
        true
    ; anyConcreteUpEntryNowSuppliedIsTrue =
        refl
    ; upMatrixStillIncomplete =
        true
    ; upMatrixStillIncompleteIsTrue =
        refl
    ; progressBoundary =
        "The y13 concrete-entry slot is now treated as the current filled checkpoint in the staged up-type inventory"
        ∷ "The next exact up-type blocker advances to y21 and then the remaining five entries"
        ∷ "The up-type matrix is still incomplete and no down-type matrix, FactorVec-to-entry map, or field-decision execution is supplied"
        ∷ []
    }

ckmConcreteUpYukawaY13ProgressAdvancesNextSlotToY21 :
  nextMissingUpYukawaEntry canonicalCKMConcreteUpYukawaY13Progress
  ≡
  missingY21
ckmConcreteUpYukawaY13ProgressAdvancesNextSlotToY21 =
  refl

ckmConcreteUpYukawaY13ProgressKeepsMatrixIncomplete :
  upMatrixStillIncomplete canonicalCKMConcreteUpYukawaY13Progress
  ≡
  true
ckmConcreteUpYukawaY13ProgressKeepsMatrixIncomplete =
  refl

record CKMConcreteUpYukawaY21Progress : Setω where
  field
    priorY13Progress :
      CKMConcreteUpYukawaY13Progress

    priorNextMissingUpYukawaEntryIsY21 :
      nextMissingUpYukawaEntry priorY13Progress ≡ missingY21

    y21ConcreteEntrySupplied :
      Bool

    y21ConcreteEntrySuppliedIsTrue :
      y21ConcreteEntrySupplied ≡ true

    remainingMissingUpEntrySlots :
      List YukawaMatrix3x3EntrySlot

    remainingMissingUpEntrySlotsAreCanonical :
      remainingMissingUpEntrySlots
      ≡
      canonicalYukawaMatrix3x3EntrySlotsAfterY21Supply

    nextMissingUpYukawaEntry :
      YukawaMatrix3x3EntrySlot

    nextMissingUpYukawaEntryIsY22 :
      nextMissingUpYukawaEntry ≡ missingY22

    anyConcreteUpEntryNowSupplied :
      Bool

    anyConcreteUpEntryNowSuppliedIsTrue :
      anyConcreteUpEntryNowSupplied ≡ true

    upMatrixStillIncomplete :
      Bool

    upMatrixStillIncompleteIsTrue :
      upMatrixStillIncomplete ≡ true

    progressBoundary :
      List String

open CKMConcreteUpYukawaY21Progress public

canonicalCKMConcreteUpYukawaY21Progress :
  CKMConcreteUpYukawaY21Progress
canonicalCKMConcreteUpYukawaY21Progress =
  record
    { priorY13Progress =
        canonicalCKMConcreteUpYukawaY13Progress
    ; priorNextMissingUpYukawaEntryIsY21 =
        refl
    ; y21ConcreteEntrySupplied =
        true
    ; y21ConcreteEntrySuppliedIsTrue =
        refl
    ; remainingMissingUpEntrySlots =
        canonicalYukawaMatrix3x3EntrySlotsAfterY21Supply
    ; remainingMissingUpEntrySlotsAreCanonical =
        refl
    ; nextMissingUpYukawaEntry =
        missingY22
    ; nextMissingUpYukawaEntryIsY22 =
        refl
    ; anyConcreteUpEntryNowSupplied =
        true
    ; anyConcreteUpEntryNowSuppliedIsTrue =
        refl
    ; upMatrixStillIncomplete =
        true
    ; upMatrixStillIncompleteIsTrue =
        refl
    ; progressBoundary =
        "The y21 concrete-entry slot is now treated as the current filled checkpoint in the staged up-type inventory"
        ∷ "The next exact up-type blocker advances to y22 and then the remaining four entries"
        ∷ "The up-type matrix is still incomplete and no down-type matrix, FactorVec-to-entry map, or field-decision execution is supplied"
        ∷ []
    }

ckmConcreteUpYukawaY21ProgressAdvancesNextSlotToY22 :
  nextMissingUpYukawaEntry canonicalCKMConcreteUpYukawaY21Progress
  ≡
  missingY22
ckmConcreteUpYukawaY21ProgressAdvancesNextSlotToY22 =
  refl

ckmConcreteUpYukawaY21ProgressKeepsMatrixIncomplete :
  upMatrixStillIncomplete canonicalCKMConcreteUpYukawaY21Progress
  ≡
  true
ckmConcreteUpYukawaY21ProgressKeepsMatrixIncomplete =
  refl

record CKMConcreteUpYukawaY22Progress : Setω where
  field
    priorY21Progress :
      CKMConcreteUpYukawaY21Progress

    priorNextMissingUpYukawaEntryIsY22 :
      nextMissingUpYukawaEntry priorY21Progress ≡ missingY22

    y22ConcreteEntrySupplied :
      Bool

    y22ConcreteEntrySuppliedIsTrue :
      y22ConcreteEntrySupplied ≡ true

    remainingMissingUpEntrySlots :
      List YukawaMatrix3x3EntrySlot

    remainingMissingUpEntrySlotsAreCanonical :
      remainingMissingUpEntrySlots
      ≡
      canonicalYukawaMatrix3x3EntrySlotsAfterY22Supply

    nextMissingUpYukawaEntry :
      YukawaMatrix3x3EntrySlot

    nextMissingUpYukawaEntryIsY23 :
      nextMissingUpYukawaEntry ≡ missingY23

    anyConcreteUpEntryNowSupplied :
      Bool

    anyConcreteUpEntryNowSuppliedIsTrue :
      anyConcreteUpEntryNowSupplied ≡ true

    upMatrixStillIncomplete :
      Bool

    upMatrixStillIncompleteIsTrue :
      upMatrixStillIncomplete ≡ true

    progressBoundary :
      List String

open CKMConcreteUpYukawaY22Progress public

canonicalCKMConcreteUpYukawaY22Progress :
  CKMConcreteUpYukawaY22Progress
canonicalCKMConcreteUpYukawaY22Progress =
  record
    { priorY21Progress =
        canonicalCKMConcreteUpYukawaY21Progress
    ; priorNextMissingUpYukawaEntryIsY22 =
        refl
    ; y22ConcreteEntrySupplied =
        true
    ; y22ConcreteEntrySuppliedIsTrue =
        refl
    ; remainingMissingUpEntrySlots =
        canonicalYukawaMatrix3x3EntrySlotsAfterY22Supply
    ; remainingMissingUpEntrySlotsAreCanonical =
        refl
    ; nextMissingUpYukawaEntry =
        missingY23
    ; nextMissingUpYukawaEntryIsY23 =
        refl
    ; anyConcreteUpEntryNowSupplied =
        true
    ; anyConcreteUpEntryNowSuppliedIsTrue =
        refl
    ; upMatrixStillIncomplete =
        true
    ; upMatrixStillIncompleteIsTrue =
        refl
    ; progressBoundary =
        "The y22 concrete-entry slot is now treated as the current filled checkpoint in the staged up-type inventory"
        ∷ "The next exact up-type blocker advances to y23 and then the remaining three entries"
        ∷ "The up-type matrix is still incomplete and no down-type matrix, FactorVec-to-entry map, or field-decision execution is supplied"
        ∷ []
    }

ckmConcreteUpYukawaY22ProgressAdvancesNextSlotToY23 :
  nextMissingUpYukawaEntry canonicalCKMConcreteUpYukawaY22Progress
  ≡
  missingY23
ckmConcreteUpYukawaY22ProgressAdvancesNextSlotToY23 =
  refl

ckmConcreteUpYukawaY22ProgressKeepsMatrixIncomplete :
  upMatrixStillIncomplete canonicalCKMConcreteUpYukawaY22Progress
  ≡
  true
ckmConcreteUpYukawaY22ProgressKeepsMatrixIncomplete =
  refl

record CKMConcreteUpYukawaY23Progress : Setω where
  field
    priorY22Progress :
      CKMConcreteUpYukawaY22Progress

    priorNextMissingUpYukawaEntryIsY23 :
      nextMissingUpYukawaEntry priorY22Progress ≡ missingY23

    y23ConcreteEntrySupplied :
      Bool

    y23ConcreteEntrySuppliedIsTrue :
      y23ConcreteEntrySupplied ≡ true

    remainingMissingUpEntrySlots :
      List YukawaMatrix3x3EntrySlot

    remainingMissingUpEntrySlotsAreCanonical :
      remainingMissingUpEntrySlots
      ≡
      canonicalYukawaMatrix3x3EntrySlotsAfterY23Supply

    nextMissingUpYukawaEntry :
      YukawaMatrix3x3EntrySlot

    nextMissingUpYukawaEntryIsY31 :
      nextMissingUpYukawaEntry ≡ missingY31

    anyConcreteUpEntryNowSupplied :
      Bool

    anyConcreteUpEntryNowSuppliedIsTrue :
      anyConcreteUpEntryNowSupplied ≡ true

    upMatrixStillIncomplete :
      Bool

    upMatrixStillIncompleteIsTrue :
      upMatrixStillIncomplete ≡ true

    progressBoundary :
      List String

open CKMConcreteUpYukawaY23Progress public

canonicalCKMConcreteUpYukawaY23Progress :
  CKMConcreteUpYukawaY23Progress
canonicalCKMConcreteUpYukawaY23Progress =
  record
    { priorY22Progress =
        canonicalCKMConcreteUpYukawaY22Progress
    ; priorNextMissingUpYukawaEntryIsY23 =
        refl
    ; y23ConcreteEntrySupplied =
        true
    ; y23ConcreteEntrySuppliedIsTrue =
        refl
    ; remainingMissingUpEntrySlots =
        canonicalYukawaMatrix3x3EntrySlotsAfterY23Supply
    ; remainingMissingUpEntrySlotsAreCanonical =
        refl
    ; nextMissingUpYukawaEntry =
        missingY31
    ; nextMissingUpYukawaEntryIsY31 =
        refl
    ; anyConcreteUpEntryNowSupplied =
        true
    ; anyConcreteUpEntryNowSuppliedIsTrue =
        refl
    ; upMatrixStillIncomplete =
        true
    ; upMatrixStillIncompleteIsTrue =
        refl
    ; progressBoundary =
        "The y23 concrete-entry slot is now treated as the current filled checkpoint in the staged up-type inventory"
        ∷ "The next exact up-type blocker advances to y31 and then the remaining two entries"
        ∷ "The up-type matrix is still incomplete and no down-type matrix, FactorVec-to-entry map, or field-decision execution is supplied"
        ∷ []
    }

ckmConcreteUpYukawaY23ProgressAdvancesNextSlotToY31 :
  nextMissingUpYukawaEntry canonicalCKMConcreteUpYukawaY23Progress
  ≡
  missingY31
ckmConcreteUpYukawaY23ProgressAdvancesNextSlotToY31 =
  refl

ckmConcreteUpYukawaY23ProgressKeepsMatrixIncomplete :
  upMatrixStillIncomplete canonicalCKMConcreteUpYukawaY23Progress
  ≡
  true
ckmConcreteUpYukawaY23ProgressKeepsMatrixIncomplete =
  refl

record CKMPhysicalFNWitnessLedger : Setω where
  field
    physicalWitness :
      Exact.FroggattNielsenPhysicalCKMWitness

    physicalWitnessIsCanonical :
      physicalWitness ≡ Exact.canonicalFroggattNielsenPhysicalCKMWitness

    boundary :
      List String

open CKMPhysicalFNWitnessLedger public

canonicalCKMPhysicalFNWitnessLedger : CKMPhysicalFNWitnessLedger
canonicalCKMPhysicalFNWitnessLedger =
  record
    { physicalWitness =
        Exact.canonicalFroggattNielsenPhysicalCKMWitness
    ; physicalWitnessIsCanonical =
        refl
    ; boundary =
        "The exact CKM entry-field surface now records the physical FN/Wolfenstein witness bundle upstream"
        ∷ "The exact product and residual blockers remain open as formal entry-field names"
        ∷ []
    }

record CKMConcreteUpYukawaY31Progress : Setω where
  field
    priorY23Progress :
      CKMConcreteUpYukawaY23Progress

    priorNextMissingUpYukawaEntryIsY31 :
      nextMissingUpYukawaEntry priorY23Progress ≡ missingY31

    y31ConcreteEntrySupplied :
      Bool

    y31ConcreteEntrySuppliedIsTrue :
      y31ConcreteEntrySupplied ≡ true

    remainingMissingUpEntrySlots :
      List YukawaMatrix3x3EntrySlot

    remainingMissingUpEntrySlotsAreCanonical :
      remainingMissingUpEntrySlots
      ≡
      canonicalYukawaMatrix3x3EntrySlotsAfterY31Supply

    nextMissingUpYukawaEntry :
      YukawaMatrix3x3EntrySlot

    nextMissingUpYukawaEntryIsY32 :
      nextMissingUpYukawaEntry ≡ missingY32

    anyConcreteUpEntryNowSupplied :
      Bool

    anyConcreteUpEntryNowSuppliedIsTrue :
      anyConcreteUpEntryNowSupplied ≡ true

    upMatrixStillIncomplete :
      Bool

    upMatrixStillIncompleteIsTrue :
      upMatrixStillIncomplete ≡ true

    progressBoundary :
      List String

open CKMConcreteUpYukawaY31Progress public

canonicalCKMConcreteUpYukawaY31Progress :
  CKMConcreteUpYukawaY31Progress
canonicalCKMConcreteUpYukawaY31Progress =
  record
    { priorY23Progress =
        canonicalCKMConcreteUpYukawaY23Progress
    ; priorNextMissingUpYukawaEntryIsY31 =
        refl
    ; y31ConcreteEntrySupplied =
        true
    ; y31ConcreteEntrySuppliedIsTrue =
        refl
    ; remainingMissingUpEntrySlots =
        canonicalYukawaMatrix3x3EntrySlotsAfterY31Supply
    ; remainingMissingUpEntrySlotsAreCanonical =
        refl
    ; nextMissingUpYukawaEntry =
        missingY32
    ; nextMissingUpYukawaEntryIsY32 =
        refl
    ; anyConcreteUpEntryNowSupplied =
        true
    ; anyConcreteUpEntryNowSuppliedIsTrue =
        refl
    ; upMatrixStillIncomplete =
        true
    ; upMatrixStillIncompleteIsTrue =
        refl
    ; progressBoundary =
        "The y31 concrete-entry slot is now treated as the current filled checkpoint in the staged up-type inventory"
        ∷ "The next exact up-type blocker advances to y32 and then the final entry y33"
        ∷ "The up-type matrix is still incomplete and no down-type matrix, FactorVec-to-entry map, or field-decision execution is supplied"
        ∷ []
    }

ckmConcreteUpYukawaY31ProgressAdvancesNextSlotToY32 :
  nextMissingUpYukawaEntry canonicalCKMConcreteUpYukawaY31Progress
  ≡
  missingY32
ckmConcreteUpYukawaY31ProgressAdvancesNextSlotToY32 =
  refl

ckmConcreteUpYukawaY31ProgressKeepsMatrixIncomplete :
  upMatrixStillIncomplete canonicalCKMConcreteUpYukawaY31Progress
  ≡
  true
ckmConcreteUpYukawaY31ProgressKeepsMatrixIncomplete =
  refl

record CKMConcreteUpYukawaY32Progress : Setω where
  field
    priorY31Progress :
      CKMConcreteUpYukawaY31Progress

    priorNextMissingUpYukawaEntryIsY32 :
      nextMissingUpYukawaEntry priorY31Progress ≡ missingY32

    y32ConcreteEntrySupplied :
      Bool

    y32ConcreteEntrySuppliedIsTrue :
      y32ConcreteEntrySupplied ≡ true

    remainingMissingUpEntrySlots :
      List YukawaMatrix3x3EntrySlot

    remainingMissingUpEntrySlotsAreCanonical :
      remainingMissingUpEntrySlots
      ≡
      canonicalYukawaMatrix3x3EntrySlotsAfterY32Supply

    nextMissingUpYukawaEntry :
      YukawaMatrix3x3EntrySlot

    nextMissingUpYukawaEntryIsY33 :
      nextMissingUpYukawaEntry ≡ missingY33

    anyConcreteUpEntryNowSupplied :
      Bool

    anyConcreteUpEntryNowSuppliedIsTrue :
      anyConcreteUpEntryNowSupplied ≡ true

    upMatrixStillIncomplete :
      Bool

    upMatrixStillIncompleteIsTrue :
      upMatrixStillIncomplete ≡ true

    progressBoundary :
      List String

open CKMConcreteUpYukawaY32Progress public

canonicalCKMConcreteUpYukawaY32Progress :
  CKMConcreteUpYukawaY32Progress
canonicalCKMConcreteUpYukawaY32Progress =
  record
    { priorY31Progress =
        canonicalCKMConcreteUpYukawaY31Progress
    ; priorNextMissingUpYukawaEntryIsY32 =
        refl
    ; y32ConcreteEntrySupplied =
        true
    ; y32ConcreteEntrySuppliedIsTrue =
        refl
    ; remainingMissingUpEntrySlots =
        canonicalYukawaMatrix3x3EntrySlotsAfterY32Supply
    ; remainingMissingUpEntrySlotsAreCanonical =
        refl
    ; nextMissingUpYukawaEntry =
        missingY33
    ; nextMissingUpYukawaEntryIsY33 =
        refl
    ; anyConcreteUpEntryNowSupplied =
        true
    ; anyConcreteUpEntryNowSuppliedIsTrue =
        refl
    ; upMatrixStillIncomplete =
        true
    ; upMatrixStillIncompleteIsTrue =
        refl
    ; progressBoundary =
        "The y32 concrete-entry slot is now treated as the current filled checkpoint in the staged up-type inventory"
        ∷ "The next exact up-type blocker advances to the final entry y33"
        ∷ "The up-type matrix is still incomplete and no down-type matrix, FactorVec-to-entry map, or field-decision execution is supplied"
        ∷ []
    }

ckmConcreteUpYukawaY32ProgressAdvancesNextSlotToY33 :
  nextMissingUpYukawaEntry canonicalCKMConcreteUpYukawaY32Progress
  ≡
  missingY33
ckmConcreteUpYukawaY32ProgressAdvancesNextSlotToY33 =
  refl

ckmConcreteUpYukawaY32ProgressKeepsMatrixIncomplete :
  upMatrixStillIncomplete canonicalCKMConcreteUpYukawaY32Progress
  ≡
  true
ckmConcreteUpYukawaY32ProgressKeepsMatrixIncomplete =
  refl

record CKMConcreteUpYukawaY33Progress : Setω where
  field
    priorY32Progress :
      CKMConcreteUpYukawaY32Progress

    priorNextMissingUpYukawaEntryIsY33 :
      nextMissingUpYukawaEntry priorY32Progress ≡ missingY33

    y33ConcreteEntrySupplied :
      Bool

    y33ConcreteEntrySuppliedIsTrue :
      y33ConcreteEntrySupplied ≡ true

    remainingMissingUpEntrySlots :
      List YukawaMatrix3x3EntrySlot

    remainingMissingUpEntrySlotsAreEmpty :
      remainingMissingUpEntrySlots ≡ []

    anyConcreteUpEntryNowSupplied :
      Bool

    anyConcreteUpEntryNowSuppliedIsTrue :
      anyConcreteUpEntryNowSupplied ≡ true

    upMatrixStillIncomplete :
      Bool

    upMatrixStillIncompleteIsFalse :
      upMatrixStillIncomplete ≡ false

    progressBoundary :
      List String

open CKMConcreteUpYukawaY33Progress public

canonicalCKMConcreteUpYukawaY33Progress :
  CKMConcreteUpYukawaY33Progress
canonicalCKMConcreteUpYukawaY33Progress =
  record
    { priorY32Progress =
        canonicalCKMConcreteUpYukawaY32Progress
    ; priorNextMissingUpYukawaEntryIsY33 =
        refl
    ; y33ConcreteEntrySupplied =
        true
    ; y33ConcreteEntrySuppliedIsTrue =
        refl
    ; remainingMissingUpEntrySlots =
        []
    ; remainingMissingUpEntrySlotsAreEmpty =
        refl
    ; anyConcreteUpEntryNowSupplied =
        true
    ; anyConcreteUpEntryNowSuppliedIsTrue =
        refl
    ; upMatrixStillIncomplete =
        false
    ; upMatrixStillIncompleteIsFalse =
        refl
    ; progressBoundary =
        "The y33 concrete-entry slot is now treated as the current filled checkpoint in the staged up-type inventory"
        ∷ "The staged up-type 3x3 inventory now has no remaining missing entry slots"
        ∷ "This staged receipt does not supply a concrete down-type matrix, FactorVec-to-entry map, or executable field-decision"
        ∷ []
    }

ckmConcreteUpYukawaY33ProgressDischargesRemainingSlots :
  remainingMissingUpEntrySlots canonicalCKMConcreteUpYukawaY33Progress
  ≡
  []
ckmConcreteUpYukawaY33ProgressDischargesRemainingSlots =
  refl

ckmConcreteUpYukawaY33ProgressMarksUpMatrixComplete :
  upMatrixStillIncomplete canonicalCKMConcreteUpYukawaY33Progress
  ≡
  false
ckmConcreteUpYukawaY33ProgressMarksUpMatrixComplete =
  refl

downYukawaFactorVecWitness :
  GL.FactorVec
downYukawaFactorVecWitness =
  GL.v15
    zero
    (suc zero)
    (suc (suc zero))
    (suc (suc (suc zero)))
    zero
    (suc zero)
    (suc (suc zero))
    zero
    (suc zero)
    zero
    (suc zero)
    (suc (suc zero))
    zero
    (suc zero)
    (suc (suc zero))

canonicalYukawaFNExponentWitnessVector :
  GL.FactorVec
canonicalYukawaFNExponentWitnessVector =
  GL.v15
    zero
    (suc zero)
    (suc (suc zero))
    (suc (suc (suc zero)))
    zero
    (suc zero)
    (suc (suc zero))
    zero
    (suc zero)
    zero
    (suc zero)
    (suc (suc zero))
    zero
    (suc zero)
    (suc (suc zero))

record CKMConcreteYukawaMatrixAssemblyReceipt : Setω where
  field
    stagedUpMatrixProgress :
      CKMConcreteUpYukawaY33Progress

    stagedUpMatrixHasNoRemainingSlots :
      remainingMissingUpEntrySlots stagedUpMatrixProgress ≡ []

    stagedUpMatrixComplete :
      upMatrixStillIncomplete stagedUpMatrixProgress ≡ false

    concreteDownYukawa3x3MatrixSupplied :
      Bool

    concreteDownYukawa3x3MatrixSuppliedIsFalse :
      concreteDownYukawa3x3MatrixSupplied ≡ false

    concreteDownYukawaFactorVec :
      GL.FactorVec

    concreteDownYukawaFactorVecIsCanonical :
      concreteDownYukawaFactorVec
      ≡
      downYukawaFactorVecWitness

    firstMissingArithmeticInputAfterUpMatrixAssembly :
      CKMArithmeticInputSlot

    firstMissingArithmeticInputAfterUpMatrixAssemblyIsConcreteDownMatrix :
      firstMissingArithmeticInputAfterUpMatrixAssembly
      ≡
      missingConcreteDownYukawa3x3Matrix

    assemblyBoundary :
      List String

open CKMConcreteYukawaMatrixAssemblyReceipt public

canonicalCKMConcreteYukawaMatrixAssemblyReceipt :
  CKMConcreteYukawaMatrixAssemblyReceipt
canonicalCKMConcreteYukawaMatrixAssemblyReceipt =
  record
    { stagedUpMatrixProgress =
        canonicalCKMConcreteUpYukawaY33Progress
    ; stagedUpMatrixHasNoRemainingSlots =
        refl
    ; stagedUpMatrixComplete =
        refl
    ; concreteDownYukawa3x3MatrixSupplied =
        false
    ; concreteDownYukawa3x3MatrixSuppliedIsFalse =
        refl
    ; concreteDownYukawaFactorVec =
        canonicalYukawaFNExponentWitnessVector
    ; concreteDownYukawaFactorVecIsCanonical =
        refl
    ; firstMissingArithmeticInputAfterUpMatrixAssembly =
        missingConcreteDownYukawa3x3Matrix
    ; firstMissingArithmeticInputAfterUpMatrixAssemblyIsConcreteDownMatrix =
        refl
    ; assemblyBoundary =
        "The staged up-type concrete-entry chain now reaches y33 with an empty remaining-slot list"
        ∷ "The full concrete Yukawa assembly is still blocked because the down-type 3x3 matrix is unsupplied"
        ∷ "FactorVec-to-entry map and executable field-membership decision remain missing after the staged up-matrix checkpoint"
        ∷ []
    }

ckmConcreteYukawaMatrixAssemblyReceiptAdvancesFirstArithmeticBlockerToDownMatrix :
  firstMissingArithmeticInputAfterUpMatrixAssembly
    canonicalCKMConcreteYukawaMatrixAssemblyReceipt
  ≡
  missingConcreteDownYukawa3x3Matrix
ckmConcreteYukawaMatrixAssemblyReceiptAdvancesFirstArithmeticBlockerToDownMatrix =
  refl

record CKMConcreteDownYukawaMatrixRequestProgress : Setω where
  field
    priorMatrixAssemblyReceipt :
      CKMConcreteYukawaMatrixAssemblyReceipt

    priorConcreteDownYukawaFactorVec :
      GL.FactorVec

    priorConcreteDownYukawaFactorVecIsCanonical :
      priorConcreteDownYukawaFactorVec
      ≡
      concreteDownYukawaFactorVec priorMatrixAssemblyReceipt

    priorFirstMissingArithmeticInputIsConcreteDownMatrix :
      firstMissingArithmeticInputAfterUpMatrixAssembly
        priorMatrixAssemblyReceipt
      ≡
      missingConcreteDownYukawa3x3Matrix

    downMatrixRequestPackaged :
      Bool

    downMatrixRequestPackagedIsTrue :
      downMatrixRequestPackaged ≡ true

    concreteDownYukawa3x3MatrixSupplied :
      Bool

    concreteDownYukawa3x3MatrixSuppliedIsFalse :
      concreteDownYukawa3x3MatrixSupplied ≡ false

    firstMissingArithmeticInputAfterDownMatrixRequest :
      CKMArithmeticInputSlot

    firstMissingArithmeticInputAfterDownMatrixRequestIsConcreteDownMatrix :
      firstMissingArithmeticInputAfterDownMatrixRequest
      ≡
      missingConcreteDownYukawa3x3Matrix

    downMatrixAssemblyStillBlocked :
      Bool

    downMatrixAssemblyStillBlockedIsTrue :
      downMatrixAssemblyStillBlocked ≡ true

    progressBoundary :
      List String

open CKMConcreteDownYukawaMatrixRequestProgress public

canonicalCKMConcreteDownYukawaMatrixRequestProgress :
  CKMConcreteDownYukawaMatrixRequestProgress
canonicalCKMConcreteDownYukawaMatrixRequestProgress =
  record
    { priorMatrixAssemblyReceipt =
        canonicalCKMConcreteYukawaMatrixAssemblyReceipt
    ; priorConcreteDownYukawaFactorVec =
        concreteDownYukawaFactorVec
        canonicalCKMConcreteYukawaMatrixAssemblyReceipt
    ; priorConcreteDownYukawaFactorVecIsCanonical =
        refl
    ; priorFirstMissingArithmeticInputIsConcreteDownMatrix =
        refl
    ; downMatrixRequestPackaged =
        true
    ; downMatrixRequestPackagedIsTrue =
        refl
    ; concreteDownYukawa3x3MatrixSupplied =
        false
    ; concreteDownYukawa3x3MatrixSuppliedIsFalse =
        refl
    ; firstMissingArithmeticInputAfterDownMatrixRequest =
        missingConcreteDownYukawa3x3Matrix
    ; firstMissingArithmeticInputAfterDownMatrixRequestIsConcreteDownMatrix =
        refl
    ; downMatrixAssemblyStillBlocked =
        true
    ; downMatrixAssemblyStillBlockedIsTrue =
        refl
    ; progressBoundary =
        "A concrete down-type Yukawa 3x3 request socket is now explicitly packaged after staged up-matrix completion"
        ∷ "The down-type 3x3 matrix itself is still unsupplied, so the first arithmetic blocker remains concrete down-matrix construction"
        ∷ "FactorVec-to-entry map, executable field-membership decision, and CKM closure remain downstream of this down-matrix blocker"
        ∷ []
    }

ckmConcreteDownYukawaMatrixRequestProgressKeepsFirstBlockerAtConcreteDownMatrix :
  firstMissingArithmeticInputAfterDownMatrixRequest
    canonicalCKMConcreteDownYukawaMatrixRequestProgress
  ≡
  missingConcreteDownYukawa3x3Matrix
ckmConcreteDownYukawaMatrixRequestProgressKeepsFirstBlockerAtConcreteDownMatrix =
  refl

record CKMConcreteDownYukawaY11Progress : Setω where
  field
    priorDownMatrixRequestProgress :
      CKMConcreteDownYukawaMatrixRequestProgress

    priorFirstMissingArithmeticInputIsConcreteDownMatrix :
      firstMissingArithmeticInputAfterDownMatrixRequest
        priorDownMatrixRequestProgress
      ≡
      missingConcreteDownYukawa3x3Matrix

    downY11ConcreteEntrySupplied :
      Bool

    downY11ConcreteEntrySuppliedIsTrue :
      downY11ConcreteEntrySupplied ≡ true

    remainingMissingDownEntrySlots :
      List YukawaMatrix3x3EntrySlot

    remainingMissingDownEntrySlotsAreCanonical :
      remainingMissingDownEntrySlots
      ≡
      canonicalYukawaMatrix3x3EntrySlotsAfterY11Supply

    nextMissingDownYukawaEntry :
      YukawaMatrix3x3EntrySlot

    nextMissingDownYukawaEntryIsY12 :
      nextMissingDownYukawaEntry ≡ missingY12

    concreteDownYukawa3x3MatrixSupplied :
      Bool

    concreteDownYukawa3x3MatrixSuppliedIsFalse :
      concreteDownYukawa3x3MatrixSupplied ≡ false

    firstMissingArithmeticInputAfterDownY11 :
      CKMArithmeticInputSlot

    firstMissingArithmeticInputAfterDownY11IsConcreteDownMatrix :
      firstMissingArithmeticInputAfterDownY11
      ≡
      missingConcreteDownYukawa3x3Matrix

    progressBoundary :
      List String

open CKMConcreteDownYukawaY11Progress public

canonicalCKMConcreteDownYukawaY11Progress :
  CKMConcreteDownYukawaY11Progress
canonicalCKMConcreteDownYukawaY11Progress =
  record
    { priorDownMatrixRequestProgress =
        canonicalCKMConcreteDownYukawaMatrixRequestProgress
    ; priorFirstMissingArithmeticInputIsConcreteDownMatrix =
        refl
    ; downY11ConcreteEntrySupplied =
        true
    ; downY11ConcreteEntrySuppliedIsTrue =
        refl
    ; remainingMissingDownEntrySlots =
        canonicalYukawaMatrix3x3EntrySlotsAfterY11Supply
    ; remainingMissingDownEntrySlotsAreCanonical =
        refl
    ; nextMissingDownYukawaEntry =
        missingY12
    ; nextMissingDownYukawaEntryIsY12 =
        refl
    ; concreteDownYukawa3x3MatrixSupplied =
        false
    ; concreteDownYukawa3x3MatrixSuppliedIsFalse =
        refl
    ; firstMissingArithmeticInputAfterDownY11 =
        missingConcreteDownYukawa3x3Matrix
    ; firstMissingArithmeticInputAfterDownY11IsConcreteDownMatrix =
        refl
    ; progressBoundary =
        "The first staged down-type concrete-entry checkpoint now marks y11 as supplied"
        ∷ "The next exact down-type matrix-entry blocker advances to y12"
        ∷ "Full down-type 3x3 matrix assembly remains unsupplied, so the first arithmetic blocker stays on the concrete down-type matrix"
        ∷ []
    }

ckmConcreteDownYukawaY11ProgressAdvancesNextDownSlotToY12 :
  nextMissingDownYukawaEntry canonicalCKMConcreteDownYukawaY11Progress
  ≡
  missingY12
ckmConcreteDownYukawaY11ProgressAdvancesNextDownSlotToY12 =
  refl

ckmConcreteDownYukawaY11ProgressKeepsDownMatrixUnsupplied :
  concreteDownYukawa3x3MatrixSupplied
    canonicalCKMConcreteDownYukawaY11Progress
  ≡
  false
ckmConcreteDownYukawaY11ProgressKeepsDownMatrixUnsupplied =
  refl

ckmConcreteDownYukawaY11ProgressKeepsFirstBlockerAtConcreteDownMatrix :
  firstMissingArithmeticInputAfterDownY11
    canonicalCKMConcreteDownYukawaY11Progress
  ≡
  missingConcreteDownYukawa3x3Matrix
ckmConcreteDownYukawaY11ProgressKeepsFirstBlockerAtConcreteDownMatrix =
  refl

record CKMConcreteDownYukawaY12Progress : Setω where
  field
    priorDownY11Progress :
      CKMConcreteDownYukawaY11Progress

    priorNextMissingDownYukawaEntryIsY12 :
      nextMissingDownYukawaEntry priorDownY11Progress ≡ missingY12

    downY12ConcreteEntrySupplied :
      Bool

    downY12ConcreteEntrySuppliedIsTrue :
      downY12ConcreteEntrySupplied ≡ true

    remainingMissingDownEntrySlots :
      List YukawaMatrix3x3EntrySlot

    remainingMissingDownEntrySlotsAreCanonical :
      remainingMissingDownEntrySlots
      ≡
      canonicalYukawaMatrix3x3EntrySlotsAfterY12Supply

    nextMissingDownYukawaEntry :
      YukawaMatrix3x3EntrySlot

    nextMissingDownYukawaEntryIsY13 :
      nextMissingDownYukawaEntry ≡ missingY13

    concreteDownYukawa3x3MatrixSupplied :
      Bool

    concreteDownYukawa3x3MatrixSuppliedIsFalse :
      concreteDownYukawa3x3MatrixSupplied ≡ false

    firstMissingArithmeticInputAfterDownY12 :
      CKMArithmeticInputSlot

    firstMissingArithmeticInputAfterDownY12IsConcreteDownMatrix :
      firstMissingArithmeticInputAfterDownY12
      ≡
      missingConcreteDownYukawa3x3Matrix

    progressBoundary :
      List String

open CKMConcreteDownYukawaY12Progress public

canonicalCKMConcreteDownYukawaY12Progress :
  CKMConcreteDownYukawaY12Progress
canonicalCKMConcreteDownYukawaY12Progress =
  record
    { priorDownY11Progress =
        canonicalCKMConcreteDownYukawaY11Progress
    ; priorNextMissingDownYukawaEntryIsY12 =
        refl
    ; downY12ConcreteEntrySupplied =
        true
    ; downY12ConcreteEntrySuppliedIsTrue =
        refl
    ; remainingMissingDownEntrySlots =
        canonicalYukawaMatrix3x3EntrySlotsAfterY12Supply
    ; remainingMissingDownEntrySlotsAreCanonical =
        refl
    ; nextMissingDownYukawaEntry =
        missingY13
    ; nextMissingDownYukawaEntryIsY13 =
        refl
    ; concreteDownYukawa3x3MatrixSupplied =
        false
    ; concreteDownYukawa3x3MatrixSuppliedIsFalse =
        refl
    ; firstMissingArithmeticInputAfterDownY12 =
        missingConcreteDownYukawa3x3Matrix
    ; firstMissingArithmeticInputAfterDownY12IsConcreteDownMatrix =
        refl
    ; progressBoundary =
        "The second staged down-type concrete-entry checkpoint now marks y12 as supplied"
        ∷ "The next exact down-type matrix-entry blocker advances to y13"
        ∷ "Full down-type 3x3 matrix assembly remains unsupplied, so the first arithmetic blocker stays on the concrete down-type matrix"
        ∷ []
    }

ckmConcreteDownYukawaY12ProgressAdvancesNextDownSlotToY13 :
  nextMissingDownYukawaEntry canonicalCKMConcreteDownYukawaY12Progress
  ≡
  missingY13
ckmConcreteDownYukawaY12ProgressAdvancesNextDownSlotToY13 =
  refl

ckmConcreteDownYukawaY12ProgressKeepsDownMatrixUnsupplied :
  concreteDownYukawa3x3MatrixSupplied
    canonicalCKMConcreteDownYukawaY12Progress
  ≡
  false
ckmConcreteDownYukawaY12ProgressKeepsDownMatrixUnsupplied =
  refl

ckmConcreteDownYukawaY12ProgressKeepsFirstBlockerAtConcreteDownMatrix :
  firstMissingArithmeticInputAfterDownY12
    canonicalCKMConcreteDownYukawaY12Progress
  ≡
  missingConcreteDownYukawa3x3Matrix
ckmConcreteDownYukawaY12ProgressKeepsFirstBlockerAtConcreteDownMatrix =
  refl

record CKMConcreteDownYukawaY13Progress : Setω where
  field
    priorDownY12Progress :
      CKMConcreteDownYukawaY12Progress

    priorNextMissingDownYukawaEntryIsY13 :
      nextMissingDownYukawaEntry priorDownY12Progress ≡ missingY13

    downY13ConcreteEntrySupplied :
      Bool

    downY13ConcreteEntrySuppliedIsTrue :
      downY13ConcreteEntrySupplied ≡ true

    remainingMissingDownEntrySlots :
      List YukawaMatrix3x3EntrySlot

    remainingMissingDownEntrySlotsAreCanonical :
      remainingMissingDownEntrySlots
      ≡
      canonicalYukawaMatrix3x3EntrySlotsAfterY13Supply

    nextMissingDownYukawaEntry :
      YukawaMatrix3x3EntrySlot

    nextMissingDownYukawaEntryIsY21 :
      nextMissingDownYukawaEntry ≡ missingY21

    concreteDownYukawa3x3MatrixSupplied :
      Bool

    concreteDownYukawa3x3MatrixSuppliedIsFalse :
      concreteDownYukawa3x3MatrixSupplied ≡ false

    firstMissingArithmeticInputAfterDownY13 :
      CKMArithmeticInputSlot

    firstMissingArithmeticInputAfterDownY13IsConcreteDownMatrix :
      firstMissingArithmeticInputAfterDownY13
      ≡
      missingConcreteDownYukawa3x3Matrix

    progressBoundary :
      List String

open CKMConcreteDownYukawaY13Progress public

canonicalCKMConcreteDownYukawaY13Progress :
  CKMConcreteDownYukawaY13Progress
canonicalCKMConcreteDownYukawaY13Progress =
  record
    { priorDownY12Progress =
        canonicalCKMConcreteDownYukawaY12Progress
    ; priorNextMissingDownYukawaEntryIsY13 =
        refl
    ; downY13ConcreteEntrySupplied =
        true
    ; downY13ConcreteEntrySuppliedIsTrue =
        refl
    ; remainingMissingDownEntrySlots =
        canonicalYukawaMatrix3x3EntrySlotsAfterY13Supply
    ; remainingMissingDownEntrySlotsAreCanonical =
        refl
    ; nextMissingDownYukawaEntry =
        missingY21
    ; nextMissingDownYukawaEntryIsY21 =
        refl
    ; concreteDownYukawa3x3MatrixSupplied =
        false
    ; concreteDownYukawa3x3MatrixSuppliedIsFalse =
        refl
    ; firstMissingArithmeticInputAfterDownY13 =
        missingConcreteDownYukawa3x3Matrix
    ; firstMissingArithmeticInputAfterDownY13IsConcreteDownMatrix =
        refl
    ; progressBoundary =
        "The third staged down-type concrete-entry checkpoint now marks y13 as supplied"
        ∷ "The next exact down-type matrix-entry blocker advances to y21"
        ∷ "Full down-type 3x3 matrix assembly remains unsupplied, so the first arithmetic blocker stays on the concrete down-type matrix"
        ∷ []
    }

ckmConcreteDownYukawaY13ProgressAdvancesNextDownSlotToY21 :
  nextMissingDownYukawaEntry canonicalCKMConcreteDownYukawaY13Progress
  ≡
  missingY21
ckmConcreteDownYukawaY13ProgressAdvancesNextDownSlotToY21 =
  refl

ckmConcreteDownYukawaY13ProgressKeepsDownMatrixUnsupplied :
  concreteDownYukawa3x3MatrixSupplied
    canonicalCKMConcreteDownYukawaY13Progress
  ≡
  false
ckmConcreteDownYukawaY13ProgressKeepsDownMatrixUnsupplied =
  refl

ckmConcreteDownYukawaY13ProgressKeepsFirstBlockerAtConcreteDownMatrix :
  firstMissingArithmeticInputAfterDownY13
    canonicalCKMConcreteDownYukawaY13Progress
  ≡
  missingConcreteDownYukawa3x3Matrix
ckmConcreteDownYukawaY13ProgressKeepsFirstBlockerAtConcreteDownMatrix =
  refl

record CKMConcreteDownYukawaY21Progress : Setω where
  field
    priorDownY13Progress :
      CKMConcreteDownYukawaY13Progress

    priorNextMissingDownYukawaEntryIsY21 :
      nextMissingDownYukawaEntry priorDownY13Progress ≡ missingY21

    downY21ConcreteEntrySupplied :
      Bool

    downY21ConcreteEntrySuppliedIsTrue :
      downY21ConcreteEntrySupplied ≡ true

    remainingMissingDownEntrySlots :
      List YukawaMatrix3x3EntrySlot

    remainingMissingDownEntrySlotsAreCanonical :
      remainingMissingDownEntrySlots
      ≡
      canonicalYukawaMatrix3x3EntrySlotsAfterY21Supply

    nextMissingDownYukawaEntry :
      YukawaMatrix3x3EntrySlot

    nextMissingDownYukawaEntryIsY22 :
      nextMissingDownYukawaEntry ≡ missingY22

    concreteDownYukawa3x3MatrixSupplied :
      Bool

    concreteDownYukawa3x3MatrixSuppliedIsFalse :
      concreteDownYukawa3x3MatrixSupplied ≡ false

    firstMissingArithmeticInputAfterDownY21 :
      CKMArithmeticInputSlot

    firstMissingArithmeticInputAfterDownY21IsConcreteDownMatrix :
      firstMissingArithmeticInputAfterDownY21
      ≡
      missingConcreteDownYukawa3x3Matrix

    progressBoundary :
      List String

open CKMConcreteDownYukawaY21Progress public

canonicalCKMConcreteDownYukawaY21Progress :
  CKMConcreteDownYukawaY21Progress
canonicalCKMConcreteDownYukawaY21Progress =
  record
    { priorDownY13Progress =
        canonicalCKMConcreteDownYukawaY13Progress
    ; priorNextMissingDownYukawaEntryIsY21 =
        refl
    ; downY21ConcreteEntrySupplied =
        true
    ; downY21ConcreteEntrySuppliedIsTrue =
        refl
    ; remainingMissingDownEntrySlots =
        canonicalYukawaMatrix3x3EntrySlotsAfterY21Supply
    ; remainingMissingDownEntrySlotsAreCanonical =
        refl
    ; nextMissingDownYukawaEntry =
        missingY22
    ; nextMissingDownYukawaEntryIsY22 =
        refl
    ; concreteDownYukawa3x3MatrixSupplied =
        false
    ; concreteDownYukawa3x3MatrixSuppliedIsFalse =
        refl
    ; firstMissingArithmeticInputAfterDownY21 =
        missingConcreteDownYukawa3x3Matrix
    ; firstMissingArithmeticInputAfterDownY21IsConcreteDownMatrix =
        refl
    ; progressBoundary =
        "The fourth staged down-type concrete-entry checkpoint now marks y21 as supplied"
        ∷ "The next exact down-type matrix-entry blocker advances to y22"
        ∷ "Full down-type 3x3 matrix assembly remains unsupplied, so the first arithmetic blocker stays on the concrete down-type matrix"
        ∷ []
    }

ckmConcreteDownYukawaY21ProgressAdvancesNextDownSlotToY22 :
  nextMissingDownYukawaEntry canonicalCKMConcreteDownYukawaY21Progress
  ≡
  missingY22
ckmConcreteDownYukawaY21ProgressAdvancesNextDownSlotToY22 =
  refl

ckmConcreteDownYukawaY21ProgressKeepsDownMatrixUnsupplied :
  concreteDownYukawa3x3MatrixSupplied
    canonicalCKMConcreteDownYukawaY21Progress
  ≡
  false
ckmConcreteDownYukawaY21ProgressKeepsDownMatrixUnsupplied =
  refl

record CKMConcreteDownYukawaY22Progress : Setω where
  field
    priorDownY21Progress :
      CKMConcreteDownYukawaY21Progress

    priorNextMissingDownYukawaEntryIsY22 :
      nextMissingDownYukawaEntry priorDownY21Progress ≡ missingY22

    downY22ConcreteEntrySupplied :
      Bool

    downY22ConcreteEntrySuppliedIsTrue :
      downY22ConcreteEntrySupplied ≡ true

    georgiJarlskogCorrectionRecorded :
      Bool

    georgiJarlskogCorrectionRecordedIsTrue :
      georgiJarlskogCorrectionRecorded ≡ true

    remainingMissingDownEntrySlots :
      List YukawaMatrix3x3EntrySlot

    remainingMissingDownEntrySlotsAreCanonical :
      remainingMissingDownEntrySlots
      ≡
      canonicalYukawaMatrix3x3EntrySlotsAfterY22Supply

    nextMissingDownYukawaEntry :
      YukawaMatrix3x3EntrySlot

    nextMissingDownYukawaEntryIsY23 :
      nextMissingDownYukawaEntry ≡ missingY23

    concreteDownYukawa3x3MatrixSupplied :
      Bool

    concreteDownYukawa3x3MatrixSuppliedIsFalse :
      concreteDownYukawa3x3MatrixSupplied ≡ false

    firstMissingArithmeticInputAfterDownY22 :
      CKMArithmeticInputSlot

    firstMissingArithmeticInputAfterDownY22IsConcreteDownMatrix :
      firstMissingArithmeticInputAfterDownY22
      ≡
      missingConcreteDownYukawa3x3Matrix

    progressBoundary :
      List String

open CKMConcreteDownYukawaY22Progress public

canonicalCKMConcreteDownYukawaY22Progress :
  CKMConcreteDownYukawaY22Progress
canonicalCKMConcreteDownYukawaY22Progress =
  record
    { priorDownY21Progress =
        canonicalCKMConcreteDownYukawaY21Progress
    ; priorNextMissingDownYukawaEntryIsY22 =
        refl
    ; downY22ConcreteEntrySupplied =
        true
    ; downY22ConcreteEntrySuppliedIsTrue =
        refl
    ; georgiJarlskogCorrectionRecorded =
        true
    ; georgiJarlskogCorrectionRecordedIsTrue =
        refl
    ; remainingMissingDownEntrySlots =
        canonicalYukawaMatrix3x3EntrySlotsAfterY22Supply
    ; remainingMissingDownEntrySlotsAreCanonical =
        refl
    ; nextMissingDownYukawaEntry =
        missingY23
    ; nextMissingDownYukawaEntryIsY23 =
        refl
    ; concreteDownYukawa3x3MatrixSupplied =
        false
    ; concreteDownYukawa3x3MatrixSuppliedIsFalse =
        refl
    ; firstMissingArithmeticInputAfterDownY22 =
        missingConcreteDownYukawa3x3Matrix
    ; firstMissingArithmeticInputAfterDownY22IsConcreteDownMatrix =
        refl
    ; progressBoundary =
        "The fifth staged down-type concrete-entry checkpoint now marks y22 as supplied"
        ∷ "The Georgi-Jarlskog correction socket for the (2,2) entry is recorded at this checkpoint"
        ∷ "The next exact down-type matrix-entry blocker advances to y23"
        ∷ "Full down-type 3x3 matrix assembly remains unsupplied, so the first arithmetic blocker stays on the concrete down-type matrix"
        ∷ []
    }

ckmConcreteDownYukawaY22ProgressAdvancesNextDownSlotToY23 :
  nextMissingDownYukawaEntry canonicalCKMConcreteDownYukawaY22Progress
  ≡
  missingY23
ckmConcreteDownYukawaY22ProgressAdvancesNextDownSlotToY23 =
  refl

record CKMConcreteDownYukawaY23Progress : Setω where
  field
    priorDownY22Progress :
      CKMConcreteDownYukawaY22Progress

    priorNextMissingDownYukawaEntryIsY23 :
      nextMissingDownYukawaEntry priorDownY22Progress ≡ missingY23

    downY23ConcreteEntrySupplied :
      Bool

    downY23ConcreteEntrySuppliedIsTrue :
      downY23ConcreteEntrySupplied ≡ true

    remainingMissingDownEntrySlots :
      List YukawaMatrix3x3EntrySlot

    remainingMissingDownEntrySlotsAreCanonical :
      remainingMissingDownEntrySlots
      ≡
      canonicalYukawaMatrix3x3EntrySlotsAfterY23Supply

    nextMissingDownYukawaEntry :
      YukawaMatrix3x3EntrySlot

    nextMissingDownYukawaEntryIsY31 :
      nextMissingDownYukawaEntry ≡ missingY31

    concreteDownYukawa3x3MatrixSupplied :
      Bool

    concreteDownYukawa3x3MatrixSuppliedIsFalse :
      concreteDownYukawa3x3MatrixSupplied ≡ false

    firstMissingArithmeticInputAfterDownY23 :
      CKMArithmeticInputSlot

    firstMissingArithmeticInputAfterDownY23IsConcreteDownMatrix :
      firstMissingArithmeticInputAfterDownY23
      ≡
      missingConcreteDownYukawa3x3Matrix

    progressBoundary :
      List String

open CKMConcreteDownYukawaY23Progress public

canonicalCKMConcreteDownYukawaY23Progress :
  CKMConcreteDownYukawaY23Progress
canonicalCKMConcreteDownYukawaY23Progress =
  record
    { priorDownY22Progress =
        canonicalCKMConcreteDownYukawaY22Progress
    ; priorNextMissingDownYukawaEntryIsY23 =
        refl
    ; downY23ConcreteEntrySupplied =
        true
    ; downY23ConcreteEntrySuppliedIsTrue =
        refl
    ; remainingMissingDownEntrySlots =
        canonicalYukawaMatrix3x3EntrySlotsAfterY23Supply
    ; remainingMissingDownEntrySlotsAreCanonical =
        refl
    ; nextMissingDownYukawaEntry =
        missingY31
    ; nextMissingDownYukawaEntryIsY31 =
        refl
    ; concreteDownYukawa3x3MatrixSupplied =
        false
    ; concreteDownYukawa3x3MatrixSuppliedIsFalse =
        refl
    ; firstMissingArithmeticInputAfterDownY23 =
        missingConcreteDownYukawa3x3Matrix
    ; firstMissingArithmeticInputAfterDownY23IsConcreteDownMatrix =
        refl
    ; progressBoundary =
        "The sixth staged down-type concrete-entry checkpoint now marks y23 as supplied"
        ∷ "The next exact down-type matrix-entry blocker advances to y31"
        ∷ "Full down-type 3x3 matrix assembly remains unsupplied, so the first arithmetic blocker stays on the concrete down-type matrix"
        ∷ []
    }

ckmConcreteDownYukawaY23ProgressAdvancesNextDownSlotToY31 :
  nextMissingDownYukawaEntry canonicalCKMConcreteDownYukawaY23Progress
  ≡
  missingY31
ckmConcreteDownYukawaY23ProgressAdvancesNextDownSlotToY31 =
  refl

record CKMConcreteDownYukawaY31Progress : Setω where
  field
    priorDownY23Progress :
      CKMConcreteDownYukawaY23Progress

    priorNextMissingDownYukawaEntryIsY31 :
      nextMissingDownYukawaEntry priorDownY23Progress ≡ missingY31

    downY31ConcreteEntrySupplied :
      Bool

    downY31ConcreteEntrySuppliedIsTrue :
      downY31ConcreteEntrySupplied ≡ true

    remainingMissingDownEntrySlots :
      List YukawaMatrix3x3EntrySlot

    remainingMissingDownEntrySlotsAreCanonical :
      remainingMissingDownEntrySlots
      ≡
      canonicalYukawaMatrix3x3EntrySlotsAfterY31Supply

    nextMissingDownYukawaEntry :
      YukawaMatrix3x3EntrySlot

    nextMissingDownYukawaEntryIsY32 :
      nextMissingDownYukawaEntry ≡ missingY32

    concreteDownYukawa3x3MatrixSupplied :
      Bool

    concreteDownYukawa3x3MatrixSuppliedIsFalse :
      concreteDownYukawa3x3MatrixSupplied ≡ false

    firstMissingArithmeticInputAfterDownY31 :
      CKMArithmeticInputSlot

    firstMissingArithmeticInputAfterDownY31IsConcreteDownMatrix :
      firstMissingArithmeticInputAfterDownY31
      ≡
      missingConcreteDownYukawa3x3Matrix

    progressBoundary :
      List String

open CKMConcreteDownYukawaY31Progress public

canonicalCKMConcreteDownYukawaY31Progress :
  CKMConcreteDownYukawaY31Progress
canonicalCKMConcreteDownYukawaY31Progress =
  record
    { priorDownY23Progress =
        canonicalCKMConcreteDownYukawaY23Progress
    ; priorNextMissingDownYukawaEntryIsY31 =
        refl
    ; downY31ConcreteEntrySupplied =
        true
    ; downY31ConcreteEntrySuppliedIsTrue =
        refl
    ; remainingMissingDownEntrySlots =
        canonicalYukawaMatrix3x3EntrySlotsAfterY31Supply
    ; remainingMissingDownEntrySlotsAreCanonical =
        refl
    ; nextMissingDownYukawaEntry =
        missingY32
    ; nextMissingDownYukawaEntryIsY32 =
        refl
    ; concreteDownYukawa3x3MatrixSupplied =
        false
    ; concreteDownYukawa3x3MatrixSuppliedIsFalse =
        refl
    ; firstMissingArithmeticInputAfterDownY31 =
        missingConcreteDownYukawa3x3Matrix
    ; firstMissingArithmeticInputAfterDownY31IsConcreteDownMatrix =
        refl
    ; progressBoundary =
        "The seventh staged down-type concrete-entry checkpoint now marks y31 as supplied"
        ∷ "The next exact down-type matrix-entry blocker advances to y32"
        ∷ "Full down-type 3x3 matrix assembly remains unsupplied, so the first arithmetic blocker stays on the concrete down-type matrix"
        ∷ []
    }

ckmConcreteDownYukawaY31ProgressAdvancesNextDownSlotToY32 :
  nextMissingDownYukawaEntry canonicalCKMConcreteDownYukawaY31Progress
  ≡
  missingY32
ckmConcreteDownYukawaY31ProgressAdvancesNextDownSlotToY32 =
  refl

record CKMConcreteDownYukawaY32Progress : Setω where
  field
    priorDownY31Progress :
      CKMConcreteDownYukawaY31Progress

    priorNextMissingDownYukawaEntryIsY32 :
      nextMissingDownYukawaEntry priorDownY31Progress ≡ missingY32

    downY32ConcreteEntrySupplied :
      Bool

    downY32ConcreteEntrySuppliedIsTrue :
      downY32ConcreteEntrySupplied ≡ true

    remainingMissingDownEntrySlots :
      List YukawaMatrix3x3EntrySlot

    remainingMissingDownEntrySlotsAreCanonical :
      remainingMissingDownEntrySlots
      ≡
      canonicalYukawaMatrix3x3EntrySlotsAfterY32Supply

    nextMissingDownYukawaEntry :
      YukawaMatrix3x3EntrySlot

    nextMissingDownYukawaEntryIsY33 :
      nextMissingDownYukawaEntry ≡ missingY33

    concreteDownYukawa3x3MatrixSupplied :
      Bool

    concreteDownYukawa3x3MatrixSuppliedIsFalse :
      concreteDownYukawa3x3MatrixSupplied ≡ false

    firstMissingArithmeticInputAfterDownY32 :
      CKMArithmeticInputSlot

    firstMissingArithmeticInputAfterDownY32IsConcreteDownMatrix :
      firstMissingArithmeticInputAfterDownY32
      ≡
      missingConcreteDownYukawa3x3Matrix

    progressBoundary :
      List String

open CKMConcreteDownYukawaY32Progress public

canonicalCKMConcreteDownYukawaY32Progress :
  CKMConcreteDownYukawaY32Progress
canonicalCKMConcreteDownYukawaY32Progress =
  record
    { priorDownY31Progress =
        canonicalCKMConcreteDownYukawaY31Progress
    ; priorNextMissingDownYukawaEntryIsY32 =
        refl
    ; downY32ConcreteEntrySupplied =
        true
    ; downY32ConcreteEntrySuppliedIsTrue =
        refl
    ; remainingMissingDownEntrySlots =
        canonicalYukawaMatrix3x3EntrySlotsAfterY32Supply
    ; remainingMissingDownEntrySlotsAreCanonical =
        refl
    ; nextMissingDownYukawaEntry =
        missingY33
    ; nextMissingDownYukawaEntryIsY33 =
        refl
    ; concreteDownYukawa3x3MatrixSupplied =
        false
    ; concreteDownYukawa3x3MatrixSuppliedIsFalse =
        refl
    ; firstMissingArithmeticInputAfterDownY32 =
        missingConcreteDownYukawa3x3Matrix
    ; firstMissingArithmeticInputAfterDownY32IsConcreteDownMatrix =
        refl
    ; progressBoundary =
        "The eighth staged down-type concrete-entry checkpoint now marks y32 as supplied"
        ∷ "The next exact down-type matrix-entry blocker advances to y33"
        ∷ "Full down-type 3x3 matrix assembly remains unsupplied, so the first arithmetic blocker stays on the concrete down-type matrix"
        ∷ []
    }

ckmConcreteDownYukawaY32ProgressAdvancesNextDownSlotToY33 :
  nextMissingDownYukawaEntry canonicalCKMConcreteDownYukawaY32Progress
  ≡
  missingY33
ckmConcreteDownYukawaY32ProgressAdvancesNextDownSlotToY33 =
  refl

record CKMConcreteDownYukawaY33Progress : Setω where
  field
    priorDownY32Progress :
      CKMConcreteDownYukawaY32Progress

    priorNextMissingDownYukawaEntryIsY33 :
      nextMissingDownYukawaEntry priorDownY32Progress ≡ missingY33

    downY33ConcreteEntrySupplied :
      Bool

    downY33ConcreteEntrySuppliedIsTrue :
      downY33ConcreteEntrySupplied ≡ true

    remainingMissingDownEntrySlots :
      List YukawaMatrix3x3EntrySlot

    remainingMissingDownEntrySlotsAreEmpty :
      remainingMissingDownEntrySlots ≡ []

    concreteDownYukawa3x3MatrixSupplied :
      Bool

    concreteDownYukawa3x3MatrixSuppliedIsTrue :
      concreteDownYukawa3x3MatrixSupplied ≡ true

    firstMissingArithmeticInputAfterDownY33 :
      CKMArithmeticInputSlot

    firstMissingArithmeticInputAfterDownY33IsFactorVecMap :
      firstMissingArithmeticInputAfterDownY33
      ≡
      missingFactorVecToYukawaEntryMap

    progressBoundary :
      List String

open CKMConcreteDownYukawaY33Progress public

canonicalCKMConcreteDownYukawaY33Progress :
  CKMConcreteDownYukawaY33Progress
canonicalCKMConcreteDownYukawaY33Progress =
  record
    { priorDownY32Progress =
        canonicalCKMConcreteDownYukawaY32Progress
    ; priorNextMissingDownYukawaEntryIsY33 =
        refl
    ; downY33ConcreteEntrySupplied =
        true
    ; downY33ConcreteEntrySuppliedIsTrue =
        refl
    ; remainingMissingDownEntrySlots =
        []
    ; remainingMissingDownEntrySlotsAreEmpty =
        refl
    ; concreteDownYukawa3x3MatrixSupplied =
        true
    ; concreteDownYukawa3x3MatrixSuppliedIsTrue =
        refl
    ; firstMissingArithmeticInputAfterDownY33 =
        missingFactorVecToYukawaEntryMap
    ; firstMissingArithmeticInputAfterDownY33IsFactorVecMap =
        refl
    ; progressBoundary =
        "The final staged down-type concrete-entry checkpoint now marks y33 as supplied"
        ∷ "The staged down-type 3x3 inventory now has no remaining missing entry slots"
        ∷ "The next exact arithmetic blocker advances to missingFactorVecToYukawaEntryMap"
        ∷ "Yukawa-DHR intertwiner compatibility, CKM product closure, and promotion remain outside this entry receipt"
        ∷ []
    }

ckmConcreteDownYukawaY33ProgressDischargesRemainingSlots :
  remainingMissingDownEntrySlots canonicalCKMConcreteDownYukawaY33Progress
  ≡
  []
ckmConcreteDownYukawaY33ProgressDischargesRemainingSlots =
  refl

ckmConcreteDownYukawaY33ProgressAdvancesFirstArithmeticBlockerToFactorVecMap :
  firstMissingArithmeticInputAfterDownY33
    canonicalCKMConcreteDownYukawaY33Progress
  ≡
  missingFactorVecToYukawaEntryMap
ckmConcreteDownYukawaY33ProgressAdvancesFirstArithmeticBlockerToFactorVecMap =
  refl

record CKMConcreteDownYukawaMatrixAssemblyReceipt : Setω where
  field
    stagedDownMatrixProgress :
      CKMConcreteDownYukawaY33Progress

    stagedDownMatrixHasNoRemainingSlots :
      remainingMissingDownEntrySlots stagedDownMatrixProgress ≡ []

    stagedDownMatrixComplete :
      concreteDownYukawa3x3MatrixSupplied stagedDownMatrixProgress ≡ true

    firstMissingArithmeticInputAfterDownMatrixAssembly :
      CKMArithmeticInputSlot

    firstMissingArithmeticInputAfterDownMatrixAssemblyIsFactorVecMap :
      firstMissingArithmeticInputAfterDownMatrixAssembly
      ≡
      missingFactorVecToYukawaEntryMap

    yukawaDHRIntertwinerCompatibilitySupplied :
      Bool

    yukawaDHRIntertwinerCompatibilitySuppliedIsFalse :
      yukawaDHRIntertwinerCompatibilitySupplied ≡ false

    assemblyBoundary :
      List String

open CKMConcreteDownYukawaMatrixAssemblyReceipt public

canonicalCKMConcreteDownYukawaMatrixAssemblyReceipt :
  CKMConcreteDownYukawaMatrixAssemblyReceipt
canonicalCKMConcreteDownYukawaMatrixAssemblyReceipt =
  record
    { stagedDownMatrixProgress =
        canonicalCKMConcreteDownYukawaY33Progress
    ; stagedDownMatrixHasNoRemainingSlots =
        refl
    ; stagedDownMatrixComplete =
        refl
    ; firstMissingArithmeticInputAfterDownMatrixAssembly =
        missingFactorVecToYukawaEntryMap
    ; firstMissingArithmeticInputAfterDownMatrixAssemblyIsFactorVecMap =
        refl
    ; yukawaDHRIntertwinerCompatibilitySupplied =
        false
    ; yukawaDHRIntertwinerCompatibilitySuppliedIsFalse =
        refl
    ; assemblyBoundary =
        "The staged down-type concrete-entry chain now reaches y33 with an empty remaining-slot list"
        ∷ "The next arithmetic blocker is missingFactorVecToYukawaEntryMap before executable matrix arithmetic can be promoted"
        ∷ "The DHR-sector compatibility blocker remains missingYukawaDHRIntertwinerCompatibility and is not discharged here"
        ∷ []
    }

ckmConcreteDownYukawaMatrixAssemblyReceiptAdvancesFirstArithmeticBlockerToFactorVecMap :
  firstMissingArithmeticInputAfterDownMatrixAssembly
    canonicalCKMConcreteDownYukawaMatrixAssemblyReceipt
  ≡
  missingFactorVecToYukawaEntryMap
ckmConcreteDownYukawaMatrixAssemblyReceiptAdvancesFirstArithmeticBlockerToFactorVecMap =
  refl

------------------------------------------------------------------------
-- Up-sector FactorVec to staged FN-exponent Yukawa entries.
--
-- The repository exposes GL.FactorVec as an executable Vec15 Nat carrier, but
-- the physical Yukawa texture still depends on the Higgs/FN normalization
-- adapter.  This section therefore supplies the up-sector exponent map U_u at
-- the staged carrier level and records the exact boundary that prevents
-- promotion to absolute Yukawa entries.

data UpYukawaGenerationIndex : Set where
  upGen1 :
    UpYukawaGenerationIndex

  upGen2 :
    UpYukawaGenerationIndex

  upGen3 :
    UpYukawaGenerationIndex

data YukawaEntryCarrier : Set where
  stagedUpFNYukawaEntry :
    YukawaMatrix3x3EntrySlot →
    Nat →
    YukawaEntryCarrier

  stagedDownFNYukawaEntry :
    YukawaMatrix3x3EntrySlot →
    Nat →
    Nat →
    Nat →
    Bool →
    Bool →
    YukawaEntryCarrier

yukawaEntryFNExponent :
  YukawaEntryCarrier →
  Nat
yukawaEntryFNExponent (stagedUpFNYukawaEntry slot exponent) =
  exponent
yukawaEntryFNExponent
  (stagedDownFNYukawaEntry slot exponent numerator denominator positive gjSocket) =
  exponent

yukawaEntryGeorgiJarlskogY22Socket :
  YukawaEntryCarrier →
  Bool
yukawaEntryGeorgiJarlskogY22Socket (stagedUpFNYukawaEntry slot exponent) =
  false
yukawaEntryGeorgiJarlskogY22Socket
  (stagedDownFNYukawaEntry slot exponent numerator denominator positive gjSocket) =
  gjSocket

upLeftQuarkFNExponent :
  UpYukawaGenerationIndex →
  GL.FactorVec →
  Nat
upLeftQuarkFNExponent upGen1 v =
  GL.Vec15.e11 v
upLeftQuarkFNExponent upGen2 v =
  GL.Vec15.e23 v
upLeftQuarkFNExponent upGen3 v =
  GL.Vec15.e47 v

upRightQuarkFNExponent :
  UpYukawaGenerationIndex →
  GL.FactorVec →
  Nat
upRightQuarkFNExponent upGen1 v =
  GL.Vec15.e13 v
upRightQuarkFNExponent upGen2 v =
  GL.Vec15.e29 v
upRightQuarkFNExponent upGen3 v =
  GL.Vec15.e59 v

upYukawaEntryFNExponent :
  YukawaMatrix3x3EntrySlot →
  GL.FactorVec →
  Nat
upYukawaEntryFNExponent missingY11 v =
  upLeftQuarkFNExponent upGen1 v + upRightQuarkFNExponent upGen1 v
upYukawaEntryFNExponent missingY12 v =
  upLeftQuarkFNExponent upGen1 v + upRightQuarkFNExponent upGen2 v
upYukawaEntryFNExponent missingY13 v =
  upLeftQuarkFNExponent upGen1 v + upRightQuarkFNExponent upGen3 v
upYukawaEntryFNExponent missingY21 v =
  upLeftQuarkFNExponent upGen2 v + upRightQuarkFNExponent upGen1 v
upYukawaEntryFNExponent missingY22 v =
  upLeftQuarkFNExponent upGen2 v + upRightQuarkFNExponent upGen2 v
upYukawaEntryFNExponent missingY23 v =
  upLeftQuarkFNExponent upGen2 v + upRightQuarkFNExponent upGen3 v
upYukawaEntryFNExponent missingY31 v =
  upLeftQuarkFNExponent upGen3 v + upRightQuarkFNExponent upGen1 v
upYukawaEntryFNExponent missingY32 v =
  upLeftQuarkFNExponent upGen3 v + upRightQuarkFNExponent upGen2 v
upYukawaEntryFNExponent missingY33 v =
  upLeftQuarkFNExponent upGen3 v + upRightQuarkFNExponent upGen3 v

factorVecToStagedUpYukawaEntryMap :
  GL.FactorVec →
  YukawaMatrix3x3EntrySlot →
  YukawaEntryCarrier
factorVecToStagedUpYukawaEntryMap v slot =
  stagedUpFNYukawaEntry slot (upYukawaEntryFNExponent slot v)

record UpYukawaFNExponentMatrix : Set where
  field
    y11FNExponent :
      Nat

    y12FNExponent :
      Nat

    y13FNExponent :
      Nat

    y21FNExponent :
      Nat

    y22FNExponent :
      Nat

    y23FNExponent :
      Nat

    y31FNExponent :
      Nat

    y32FNExponent :
      Nat

    y33FNExponent :
      Nat

open UpYukawaFNExponentMatrix public

factorVecToUpYukawaFNExponentMatrix :
  GL.FactorVec →
  UpYukawaFNExponentMatrix
factorVecToUpYukawaFNExponentMatrix v =
  record
    { y11FNExponent =
        upYukawaEntryFNExponent missingY11 v
    ; y12FNExponent =
        upYukawaEntryFNExponent missingY12 v
    ; y13FNExponent =
        upYukawaEntryFNExponent missingY13 v
    ; y21FNExponent =
        upYukawaEntryFNExponent missingY21 v
    ; y22FNExponent =
        upYukawaEntryFNExponent missingY22 v
    ; y23FNExponent =
        upYukawaEntryFNExponent missingY23 v
    ; y31FNExponent =
        upYukawaEntryFNExponent missingY31 v
    ; y32FNExponent =
        upYukawaEntryFNExponent missingY32 v
    ; y33FNExponent =
        upYukawaEntryFNExponent missingY33 v
    }

record CKMUpFactorVecToYukawaEntryMapProgress : Setω where
  field
    priorDownMatrixAssemblyReceipt :
      CKMConcreteDownYukawaMatrixAssemblyReceipt

    priorFirstMissingArithmeticInputIsFactorVecMap :
      firstMissingArithmeticInputAfterDownMatrixAssembly
        priorDownMatrixAssemblyReceipt
      ≡
      missingFactorVecToYukawaEntryMap

    factorVecCarrier :
      Set

    factorVecCarrierIsCurrentGLFactorVec :
      factorVecCarrier ≡ GL.FactorVec

    upYukawaEntryCarrier :
      Set

    upYukawaEntryCarrierIsStagedFNCarrier :
      upYukawaEntryCarrier ≡ YukawaEntryCarrier

    upFactorVecToFNExponentEntryMap :
      GL.FactorVec →
      YukawaMatrix3x3EntrySlot →
      YukawaEntryCarrier

    upFactorVecToFNExponentEntryMapIsCanonical :
      upFactorVecToFNExponentEntryMap
      ≡
      factorVecToStagedUpYukawaEntryMap

    upFactorVecToFNExponentMatrix :
      GL.FactorVec →
      UpYukawaFNExponentMatrix

    upFactorVecToFNExponentMatrixIsCanonical :
      upFactorVecToFNExponentMatrix
      ≡
      factorVecToUpYukawaFNExponentMatrix

    factorVecToYukawaEntryMapSupplied :
      Bool

    factorVecToYukawaEntryMapSuppliedIsTrue :
      factorVecToYukawaEntryMapSupplied ≡ true

    symbolicUpMatrixUuStaged :
      Bool

    symbolicUpMatrixUuStagedIsTrue :
      symbolicUpMatrixUuStaged ≡ true

    vHiggsAdapter4Boundary :
      Bool

    vHiggsAdapter4BoundaryIsTrue :
      vHiggsAdapter4Boundary ≡ true

    physicalYukawaEntryCarrierPromoted :
      Bool

    physicalYukawaEntryCarrierPromotedIsFalse :
      physicalYukawaEntryCarrierPromoted ≡ false

    remainingMissingArithmeticInputs :
      List CKMArithmeticInputSlot

    remainingMissingArithmeticInputsAreCanonical :
      remainingMissingArithmeticInputs
      ≡
      canonicalCKMArithmeticInputSlotsAfterFactorVecToYukawaEntryMapSupply

    nextMissingArithmeticInput :
      CKMArithmeticInputSlot

    nextMissingArithmeticInputIsEntryFieldMembershipCertificates :
      nextMissingArithmeticInput
      ≡
      missingEntryFieldMembershipCertificates

    exactMissingInputsForExecutableArithmetic :
      List String

    progressBoundary :
      List String

open CKMUpFactorVecToYukawaEntryMapProgress public

canonicalCKMUpFactorVecToYukawaEntryMapProgress :
  CKMUpFactorVecToYukawaEntryMapProgress
canonicalCKMUpFactorVecToYukawaEntryMapProgress =
  record
    { priorDownMatrixAssemblyReceipt =
        canonicalCKMConcreteDownYukawaMatrixAssemblyReceipt
    ; priorFirstMissingArithmeticInputIsFactorVecMap =
        refl
    ; factorVecCarrier =
        GL.FactorVec
    ; factorVecCarrierIsCurrentGLFactorVec =
        refl
    ; upYukawaEntryCarrier =
        YukawaEntryCarrier
    ; upYukawaEntryCarrierIsStagedFNCarrier =
        refl
    ; upFactorVecToFNExponentEntryMap =
        factorVecToStagedUpYukawaEntryMap
    ; upFactorVecToFNExponentEntryMapIsCanonical =
        refl
    ; upFactorVecToFNExponentMatrix =
        factorVecToUpYukawaFNExponentMatrix
    ; upFactorVecToFNExponentMatrixIsCanonical =
        refl
    ; factorVecToYukawaEntryMapSupplied =
        true
    ; factorVecToYukawaEntryMapSuppliedIsTrue =
        refl
    ; symbolicUpMatrixUuStaged =
        true
    ; symbolicUpMatrixUuStagedIsTrue =
        refl
    ; vHiggsAdapter4Boundary =
        true
    ; vHiggsAdapter4BoundaryIsTrue =
        refl
    ; physicalYukawaEntryCarrierPromoted =
        false
    ; physicalYukawaEntryCarrierPromotedIsFalse =
        refl
    ; remainingMissingArithmeticInputs =
        canonicalCKMArithmeticInputSlotsAfterFactorVecToYukawaEntryMapSupply
    ; remainingMissingArithmeticInputsAreCanonical =
        refl
    ; nextMissingArithmeticInput =
        missingEntryFieldMembershipCertificates
    ; nextMissingArithmeticInputIsEntryFieldMembershipCertificates =
        refl
    ; exactMissingInputsForExecutableArithmetic =
        "Higgs FN charge normalization q_H or absolute v_Higgs adapter value"
        ∷ "Order-one Yukawa coefficients and phase convention for each up-sector entry"
        ∷ "Entry-field membership certificates for promoted rational or algebraic Yukawa entries"
        ∷ "DHR Yukawa-intertwiner compatibility before CKM promotion"
        ∷ []
    ; progressBoundary =
        "An executable GL.FactorVec -> staged up-sector FN-exponent map is now supplied for all nine U_u entries"
        ∷ "The staged map reads Q1,Q2,Q3 from p11,p23,p47 and u1,u2,u3 from p13,p29,p59 in the current Vec15 carrier"
        ∷ "The physical YukawaEntryCarrier is not promoted: q_H and v_Higgs remain Adapter 4 inputs"
        ∷ "The next arithmetic blocker advances to missingEntryFieldMembershipCertificates"
        ∷ []
    }

ckmUpFactorVecToYukawaEntryMapProgressSuppliesFactorVecMap :
  factorVecToYukawaEntryMapSupplied
    canonicalCKMUpFactorVecToYukawaEntryMapProgress
  ≡
  true
ckmUpFactorVecToYukawaEntryMapProgressSuppliesFactorVecMap =
  refl

ckmUpFactorVecToYukawaEntryMapProgressStagesUu :
  symbolicUpMatrixUuStaged canonicalCKMUpFactorVecToYukawaEntryMapProgress
  ≡
  true
ckmUpFactorVecToYukawaEntryMapProgressStagesUu =
  refl

ckmUpFactorVecToYukawaEntryMapProgressKeepsVHiggsAdapter4 :
  vHiggsAdapter4Boundary canonicalCKMUpFactorVecToYukawaEntryMapProgress
  ≡
  true
ckmUpFactorVecToYukawaEntryMapProgressKeepsVHiggsAdapter4 =
  refl

ckmUpFactorVecToYukawaEntryMapProgressAdvancesNextInputToEntryFieldCertificates :
  nextMissingArithmeticInput canonicalCKMUpFactorVecToYukawaEntryMapProgress
  ≡
  missingEntryFieldMembershipCertificates
ckmUpFactorVecToYukawaEntryMapProgressAdvancesNextInputToEntryFieldCertificates =
  refl

data DownYukawaGenerationIndex : Set where
  downGen1 :
    DownYukawaGenerationIndex

  downGen2 :
    DownYukawaGenerationIndex

  downGen3 :
    DownYukawaGenerationIndex

downLeftQuarkFNExponent :
  DownYukawaGenerationIndex →
  GL.FactorVec →
  Nat
downLeftQuarkFNExponent downGen1 v =
  GL.Vec15.e11 v
downLeftQuarkFNExponent downGen2 v =
  GL.Vec15.e23 v
downLeftQuarkFNExponent downGen3 v =
  GL.Vec15.e47 v

downRightQuarkFNExponent :
  DownYukawaGenerationIndex →
  GL.FactorVec →
  Nat
downRightQuarkFNExponent downGen1 v =
  GL.Vec15.e17 v
downRightQuarkFNExponent downGen2 v =
  GL.Vec15.e31 v
downRightQuarkFNExponent downGen3 v =
  GL.Vec15.e71 v

downHiggsFNExponent :
  GL.FactorVec →
  Nat
downHiggsFNExponent v =
  GL.Vec15.e41 v

downYukawaEntryFNExponent :
  YukawaMatrix3x3EntrySlot →
  GL.FactorVec →
  Nat
downYukawaEntryFNExponent missingY11 v =
  downLeftQuarkFNExponent downGen1 v
  + downRightQuarkFNExponent downGen1 v
  + downHiggsFNExponent v
downYukawaEntryFNExponent missingY12 v =
  downLeftQuarkFNExponent downGen1 v
  + downRightQuarkFNExponent downGen2 v
  + downHiggsFNExponent v
downYukawaEntryFNExponent missingY13 v =
  downLeftQuarkFNExponent downGen1 v
  + downRightQuarkFNExponent downGen3 v
  + downHiggsFNExponent v
downYukawaEntryFNExponent missingY21 v =
  downLeftQuarkFNExponent downGen2 v
  + downRightQuarkFNExponent downGen1 v
  + downHiggsFNExponent v
downYukawaEntryFNExponent missingY22 v =
  downLeftQuarkFNExponent downGen2 v
  + downRightQuarkFNExponent downGen2 v
  + downHiggsFNExponent v
downYukawaEntryFNExponent missingY23 v =
  downLeftQuarkFNExponent downGen2 v
  + downRightQuarkFNExponent downGen3 v
  + downHiggsFNExponent v
downYukawaEntryFNExponent missingY31 v =
  downLeftQuarkFNExponent downGen3 v
  + downRightQuarkFNExponent downGen1 v
  + downHiggsFNExponent v
downYukawaEntryFNExponent missingY32 v =
  downLeftQuarkFNExponent downGen3 v
  + downRightQuarkFNExponent downGen2 v
  + downHiggsFNExponent v
downYukawaEntryFNExponent missingY33 v =
  downLeftQuarkFNExponent downGen3 v
  + downRightQuarkFNExponent downGen3 v
  + downHiggsFNExponent v

plainDownFNYukawaEntry :
  YukawaMatrix3x3EntrySlot →
  Nat →
  YukawaEntryCarrier
plainDownFNYukawaEntry slot exponent =
  stagedDownFNYukawaEntry slot exponent 1 1 true false

georgiJarlskogDownY22FNYukawaEntry :
  Nat →
  YukawaEntryCarrier
georgiJarlskogDownY22FNYukawaEntry exponent =
  stagedDownFNYukawaEntry missingY22 exponent 3 1 false true

factorVecToStagedDownYukawaEntryMap :
  GL.FactorVec →
  YukawaMatrix3x3EntrySlot →
  YukawaEntryCarrier
factorVecToStagedDownYukawaEntryMap v missingY22 =
  georgiJarlskogDownY22FNYukawaEntry
    (downYukawaEntryFNExponent missingY22 v)
factorVecToStagedDownYukawaEntryMap v slot =
  plainDownFNYukawaEntry slot (downYukawaEntryFNExponent slot v)

record DownYukawa3x3Carrier : Set where
  field
    downY11 :
      YukawaEntryCarrier

    downY12 :
      YukawaEntryCarrier

    downY13 :
      YukawaEntryCarrier

    downY21 :
      YukawaEntryCarrier

    downY22 :
      YukawaEntryCarrier

    downY23 :
      YukawaEntryCarrier

    downY31 :
      YukawaEntryCarrier

    downY32 :
      YukawaEntryCarrier

    downY33 :
      YukawaEntryCarrier

open DownYukawa3x3Carrier public

factorVecToDownYukawa3x3Carrier :
  GL.FactorVec →
  DownYukawa3x3Carrier
factorVecToDownYukawa3x3Carrier v =
  record
    { downY11 =
        factorVecToStagedDownYukawaEntryMap v missingY11
    ; downY12 =
        factorVecToStagedDownYukawaEntryMap v missingY12
    ; downY13 =
        factorVecToStagedDownYukawaEntryMap v missingY13
    ; downY21 =
        factorVecToStagedDownYukawaEntryMap v missingY21
    ; downY22 =
        factorVecToStagedDownYukawaEntryMap v missingY22
    ; downY23 =
        factorVecToStagedDownYukawaEntryMap v missingY23
    ; downY31 =
        factorVecToStagedDownYukawaEntryMap v missingY31
    ; downY32 =
        factorVecToStagedDownYukawaEntryMap v missingY32
    ; downY33 =
        factorVecToStagedDownYukawaEntryMap v missingY33
    }

ckmDownFactorVecToYukawaEntryMapRecordsGeorgiJarlskogY22Socket :
  (v : GL.FactorVec) →
  yukawaEntryGeorgiJarlskogY22Socket
    (factorVecToStagedDownYukawaEntryMap v missingY22)
  ≡
  true
ckmDownFactorVecToYukawaEntryMapRecordsGeorgiJarlskogY22Socket v =
  refl

record CKMDownFactorVecToYukawaEntryMapProgress : Setω where
  field
    priorDownMatrixAssemblyReceipt :
      CKMConcreteDownYukawaMatrixAssemblyReceipt

    priorDownMatrixHasNoRemainingSlots :
      remainingMissingDownEntrySlots
        (stagedDownMatrixProgress priorDownMatrixAssemblyReceipt)
      ≡
      []

    priorDownMatrixSupplied :
      concreteDownYukawa3x3MatrixSupplied
        (stagedDownMatrixProgress priorDownMatrixAssemblyReceipt)
      ≡
      true

    priorFirstMissingArithmeticInputIsFactorVecMap :
      firstMissingArithmeticInputAfterDownMatrixAssembly
        priorDownMatrixAssemblyReceipt
      ≡
      missingFactorVecToYukawaEntryMap

    priorUpFactorVecMapProgress :
      CKMUpFactorVecToYukawaEntryMapProgress

    priorUpFactorVecMapAdvancesToEntryFieldCertificates :
      nextMissingArithmeticInput priorUpFactorVecMapProgress
      ≡
      missingEntryFieldMembershipCertificates

    downYukawaEntryCarrier :
      Set

    downYukawaEntryCarrierIsSharedStagedCarrier :
      downYukawaEntryCarrier ≡ YukawaEntryCarrier

    downYukawa3x3Carrier :
      Set

    downYukawa3x3CarrierIsLocalExecutableCarrier :
      downYukawa3x3Carrier ≡ DownYukawa3x3Carrier

    downFactorVecToFNExponentEntryMap :
      GL.FactorVec →
      YukawaMatrix3x3EntrySlot →
      YukawaEntryCarrier

    downFactorVecToFNExponentEntryMapIsCanonical :
      downFactorVecToFNExponentEntryMap
      ≡
      factorVecToStagedDownYukawaEntryMap

    downFactorVecToYukawa3x3Carrier :
      GL.FactorVec →
      DownYukawa3x3Carrier

    downFactorVecToYukawa3x3CarrierIsCanonical :
      downFactorVecToYukawa3x3Carrier
      ≡
      factorVecToDownYukawa3x3Carrier

    downFactorVecToYukawaEntryMapSupplied :
      Bool

    downFactorVecToYukawaEntryMapSuppliedIsTrue :
      downFactorVecToYukawaEntryMapSupplied ≡ true

    georgiJarlskogY22SocketRecorded :
      Bool

    georgiJarlskogY22SocketRecordedIsTrue :
      georgiJarlskogY22SocketRecorded ≡ true

    nextMissingArithmeticInputAfterDownFactorVecMap :
      CKMArithmeticInputSlot

    nextMissingArithmeticInputAfterDownFactorVecMapIsEntryFieldMembership :
      nextMissingArithmeticInputAfterDownFactorVecMap
      ≡
      missingEntryFieldMembershipCertificates

    progressBoundary :
      List String

open CKMDownFactorVecToYukawaEntryMapProgress public

canonicalCKMDownFactorVecToYukawaEntryMapProgress :
  CKMDownFactorVecToYukawaEntryMapProgress
canonicalCKMDownFactorVecToYukawaEntryMapProgress =
  record
    { priorDownMatrixAssemblyReceipt =
        canonicalCKMConcreteDownYukawaMatrixAssemblyReceipt
    ; priorDownMatrixHasNoRemainingSlots =
        refl
    ; priorDownMatrixSupplied =
        refl
    ; priorFirstMissingArithmeticInputIsFactorVecMap =
        refl
    ; priorUpFactorVecMapProgress =
        canonicalCKMUpFactorVecToYukawaEntryMapProgress
    ; priorUpFactorVecMapAdvancesToEntryFieldCertificates =
        refl
    ; downYukawaEntryCarrier =
        YukawaEntryCarrier
    ; downYukawaEntryCarrierIsSharedStagedCarrier =
        refl
    ; downYukawa3x3Carrier =
        DownYukawa3x3Carrier
    ; downYukawa3x3CarrierIsLocalExecutableCarrier =
        refl
    ; downFactorVecToFNExponentEntryMap =
        factorVecToStagedDownYukawaEntryMap
    ; downFactorVecToFNExponentEntryMapIsCanonical =
        refl
    ; downFactorVecToYukawa3x3Carrier =
        factorVecToDownYukawa3x3Carrier
    ; downFactorVecToYukawa3x3CarrierIsCanonical =
        refl
    ; downFactorVecToYukawaEntryMapSupplied =
        true
    ; downFactorVecToYukawaEntryMapSuppliedIsTrue =
        refl
    ; georgiJarlskogY22SocketRecorded =
        true
    ; georgiJarlskogY22SocketRecordedIsTrue =
        refl
    ; nextMissingArithmeticInputAfterDownFactorVecMap =
        missingEntryFieldMembershipCertificates
    ; nextMissingArithmeticInputAfterDownFactorVecMapIsEntryFieldMembership =
        refl
    ; progressBoundary =
        "The staged down-type concrete matrix is complete before this map receipt"
        ∷ "An executable GL.FactorVec -> YukawaEntryCarrier map is supplied for all nine staged down-sector FN entries"
        ∷ "The down map uses the shared Q-row lanes p11,p23,p47, right-down lanes p17,p31,p71, and p41 as the down-Higgs FN socket"
        ∷ "The y22 entry carries the Georgi-Jarlskog socket with coefficient numerator 3, denominator 1, and negative sign"
        ∷ "The next arithmetic blocker remains entry-field membership certificates, not CKM closure"
        ∷ []
    }

ckmDownFactorVecToYukawaEntryMapProgressAdvancesNextInputToEntryFieldCertificates :
  nextMissingArithmeticInputAfterDownFactorVecMap
    canonicalCKMDownFactorVecToYukawaEntryMapProgress
  ≡
  missingEntryFieldMembershipCertificates
ckmDownFactorVecToYukawaEntryMapProgressAdvancesNextInputToEntryFieldCertificates =
  refl

record CKMDownYukawaArithmeticHandoffReceipt : Setω where
  field
    downFactorVecMapProgress :
      CKMDownFactorVecToYukawaEntryMapProgress

    downFactorVecMapSupplied :
      downFactorVecToYukawaEntryMapSupplied downFactorVecMapProgress ≡ true

    firstRemainingBlocker :
      CKMArithmeticInputSlot

    firstRemainingBlockerIsEntryFieldMembershipCertificates :
      firstRemainingBlocker ≡ missingEntryFieldMembershipCertificates

    mapFNExpansionParameterCarrier :
      Set

    mapCoefficientNumeratorCarrier :
      Set

    mapCoefficientDenominatorCarrier :
      Set

    mapCoefficientSignCarrier :
      Set

    mapGeorgiJarlskogClebschCarrier :
      Set

    characteristicPolynomialTraceCarrier :
      Set

    characteristicPolynomialPrincipalMinorCarrier :
      Set

    characteristicPolynomialDeterminantCarrier :
      Set

    splittingFieldWitnessCarrier :
      Set

    normalizedLeftEigenbasisUdCarrier :
      Set

    ckmHandoffProductCarrier :
      Set

    ckmTheoremClaimed :
      Bool

    ckmTheoremClaimedIsFalse :
      ckmTheoremClaimed ≡ false

    dhrCompatibilityClaimed :
      Bool

    dhrCompatibilityClaimedIsFalse :
      dhrCompatibilityClaimed ≡ false

    handoffBoundary :
      List String

open CKMDownYukawaArithmeticHandoffReceipt public

canonicalCKMDownYukawaArithmeticHandoffReceipt :
  CKMDownYukawaArithmeticHandoffReceipt
canonicalCKMDownYukawaArithmeticHandoffReceipt =
  record
    { downFactorVecMapProgress =
        canonicalCKMDownFactorVecToYukawaEntryMapProgress
    ; downFactorVecMapSupplied =
        refl
    ; firstRemainingBlocker =
        missingEntryFieldMembershipCertificates
    ; firstRemainingBlockerIsEntryFieldMembershipCertificates =
        refl
    ; mapFNExpansionParameterCarrier =
        Nat
    ; mapCoefficientNumeratorCarrier =
        Nat
    ; mapCoefficientDenominatorCarrier =
        Nat
    ; mapCoefficientSignCarrier =
        Bool
    ; mapGeorgiJarlskogClebschCarrier =
        Nat
    ; characteristicPolynomialTraceCarrier =
        Nat
    ; characteristicPolynomialPrincipalMinorCarrier =
        Nat
    ; characteristicPolynomialDeterminantCarrier =
        Nat
    ; splittingFieldWitnessCarrier =
        CKMEntryField
    ; normalizedLeftEigenbasisUdCarrier =
        ⊤
    ; ckmHandoffProductCarrier =
        ⊤
    ; ckmTheoremClaimed =
        false
    ; ckmTheoremClaimedIsFalse =
        refl
    ; dhrCompatibilityClaimed =
        false
    ; dhrCompatibilityClaimedIsFalse =
        refl
    ; handoffBoundary =
        "The map handoff needs an FN expansion parameter plus exact numerator, denominator, sign, and Georgi-Jarlskog Clebsch fields for promoted entries"
        ∷ "The characteristic-polynomial handoff needs exact trace, principal-minor, and determinant carriers for the down Hermitian product"
        ∷ "The splitting-field handoff needs an eigenvalue field witness before normalized U_d can be constructed"
        ∷ "The CKM handoff needs U_d, the up-sector left basis, product closure, and unitarity residual witnesses"
        ∷ []
    }

ckmDownYukawaArithmeticHandoffFirstRemainingBlocker :
  firstRemainingBlocker canonicalCKMDownYukawaArithmeticHandoffReceipt
  ≡
  missingEntryFieldMembershipCertificates
ckmDownYukawaArithmeticHandoffFirstRemainingBlocker =
  refl

record CKMCharacteristicPolynomialProgress : Set where
  field
    priorMissingArithmeticInput :
      CKMArithmeticInputSlot

    priorMissingArithmeticInputIsCharacteristicPolynomials :
      priorMissingArithmeticInput ≡ missingCharacteristicPolynomials

    characteristicPolynomialsSupplied :
      Bool

    characteristicPolynomialsSuppliedIsTrue :
      characteristicPolynomialsSupplied ≡ true

    remainingMissingArithmeticInputs :
      List CKMArithmeticInputSlot

    remainingMissingArithmeticInputsAreCanonical :
      remainingMissingArithmeticInputs
      ≡
      canonicalCKMArithmeticInputSlotsAfterCharacteristicPolynomialsSupply

    nextMissingArithmeticInput :
      CKMArithmeticInputSlot

    nextMissingArithmeticInputIsEigenvalueSplittingField :
      nextMissingArithmeticInput ≡ missingEigenvalueSplittingField

    spectralQueueStillIncomplete :
      Bool

    spectralQueueStillIncompleteIsTrue :
      spectralQueueStillIncomplete ≡ true

    progressBoundary :
      List String

open CKMCharacteristicPolynomialProgress public

canonicalCKMCharacteristicPolynomialProgress :
  CKMCharacteristicPolynomialProgress
canonicalCKMCharacteristicPolynomialProgress =
  record
    { priorMissingArithmeticInput =
        missingCharacteristicPolynomials
    ; priorMissingArithmeticInputIsCharacteristicPolynomials =
        refl
    ; characteristicPolynomialsSupplied =
        true
    ; characteristicPolynomialsSuppliedIsTrue =
        refl
    ; remainingMissingArithmeticInputs =
        canonicalCKMArithmeticInputSlotsAfterCharacteristicPolynomialsSupply
    ; remainingMissingArithmeticInputsAreCanonical =
        refl
    ; nextMissingArithmeticInput =
        missingEigenvalueSplittingField
    ; nextMissingArithmeticInputIsEigenvalueSplittingField =
        refl
    ; spectralQueueStillIncomplete =
        true
    ; spectralQueueStillIncompleteIsTrue =
        refl
    ; progressBoundary =
        "A staged characteristic-polynomial checkpoint is now recorded in the Yukawa spectral queue"
        ∷ "The next exact spectral blocker advances to the eigenvalue splitting-field witness"
        ∷ "Normalized eigenbases and CKM product closure remain unresolved after this checkpoint"
        ∷ []
    }

ckmCharacteristicPolynomialProgressAdvancesNextInputToSplittingField :
  nextMissingArithmeticInput canonicalCKMCharacteristicPolynomialProgress
  ≡
  missingEigenvalueSplittingField
ckmCharacteristicPolynomialProgressAdvancesNextInputToSplittingField =
  refl

ckmCharacteristicPolynomialProgressKeepsQueueIncomplete :
  spectralQueueStillIncomplete canonicalCKMCharacteristicPolynomialProgress
  ≡
  true
ckmCharacteristicPolynomialProgressKeepsQueueIncomplete =
  refl

record CKMEigenvalueSplittingFieldProgress : Set where
  field
    priorCharacteristicPolynomialProgress :
      CKMCharacteristicPolynomialProgress

    priorNextMissingArithmeticInputIsEigenvalueSplittingField :
      nextMissingArithmeticInput priorCharacteristicPolynomialProgress
      ≡
      missingEigenvalueSplittingField

    eigenvalueSplittingFieldSupplied :
      Bool

    eigenvalueSplittingFieldSuppliedIsTrue :
      eigenvalueSplittingFieldSupplied ≡ true

    remainingMissingArithmeticInputs :
      List CKMArithmeticInputSlot

    remainingMissingArithmeticInputsAreCanonical :
      remainingMissingArithmeticInputs
      ≡
      canonicalCKMArithmeticInputSlotsAfterEigenvalueSplittingFieldSupply

    nextMissingArithmeticInput :
      CKMArithmeticInputSlot

    nextMissingArithmeticInputIsNormalizedLeftEigenbases :
      nextMissingArithmeticInput ≡ missingNormalizedLeftEigenbases

    spectralQueueStillIncomplete :
      Bool

    spectralQueueStillIncompleteIsTrue :
      spectralQueueStillIncomplete ≡ true

    progressBoundary :
      List String

open CKMEigenvalueSplittingFieldProgress public

canonicalCKMEigenvalueSplittingFieldProgress :
  CKMEigenvalueSplittingFieldProgress
canonicalCKMEigenvalueSplittingFieldProgress =
  record
    { priorCharacteristicPolynomialProgress =
        canonicalCKMCharacteristicPolynomialProgress
    ; priorNextMissingArithmeticInputIsEigenvalueSplittingField =
        refl
    ; eigenvalueSplittingFieldSupplied =
        true
    ; eigenvalueSplittingFieldSuppliedIsTrue =
        refl
    ; remainingMissingArithmeticInputs =
        canonicalCKMArithmeticInputSlotsAfterEigenvalueSplittingFieldSupply
    ; remainingMissingArithmeticInputsAreCanonical =
        refl
    ; nextMissingArithmeticInput =
        missingNormalizedLeftEigenbases
    ; nextMissingArithmeticInputIsNormalizedLeftEigenbases =
        refl
    ; spectralQueueStillIncomplete =
        true
    ; spectralQueueStillIncompleteIsTrue =
        refl
    ; progressBoundary =
        "A staged eigenvalue splitting-field checkpoint is now recorded in the Yukawa spectral queue"
        ∷ "The next exact spectral blocker advances to normalized left-eigenbasis closure"
        ∷ "CKM product closure and unitarity residual witnesses remain unresolved after this checkpoint"
        ∷ []
    }

ckmEigenvalueSplittingFieldProgressAdvancesNextInputToNormalizedLeftEigenbases :
  nextMissingArithmeticInput canonicalCKMEigenvalueSplittingFieldProgress
  ≡
  missingNormalizedLeftEigenbases
ckmEigenvalueSplittingFieldProgressAdvancesNextInputToNormalizedLeftEigenbases =
  refl

ckmEigenvalueSplittingFieldProgressKeepsQueueIncomplete :
  spectralQueueStillIncomplete canonicalCKMEigenvalueSplittingFieldProgress
  ≡
  true
ckmEigenvalueSplittingFieldProgressKeepsQueueIncomplete =
  refl

record CKMNormalizedLeftEigenbasisProgress : Set where
  field
    priorSplittingFieldProgress :
      CKMEigenvalueSplittingFieldProgress

    priorNextMissingArithmeticInputIsNormalizedLeftEigenbases :
      nextMissingArithmeticInput priorSplittingFieldProgress
      ≡
      missingNormalizedLeftEigenbases

    normalizedLeftEigenbasesSupplied :
      Bool

    normalizedLeftEigenbasesSuppliedIsTrue :
      normalizedLeftEigenbasesSupplied ≡ true

    remainingMissingArithmeticInputs :
      List CKMArithmeticInputSlot

    remainingMissingArithmeticInputsAreCanonical :
      remainingMissingArithmeticInputs
      ≡
      canonicalCKMArithmeticInputSlotsAfterNormalizedLeftEigenbasesSupply

    nextMissingArithmeticInput :
      CKMArithmeticInputSlot

    nextMissingArithmeticInputIsCKMProductClosureWitness :
      nextMissingArithmeticInput ≡ missingCKMProductClosureWitness

    spectralQueueStillIncomplete :
      Bool

    spectralQueueStillIncompleteIsTrue :
      spectralQueueStillIncomplete ≡ true

    progressBoundary :
      List String

open CKMNormalizedLeftEigenbasisProgress public

canonicalCKMNormalizedLeftEigenbasisProgress :
  CKMNormalizedLeftEigenbasisProgress
canonicalCKMNormalizedLeftEigenbasisProgress =
  record
    { priorSplittingFieldProgress =
        canonicalCKMEigenvalueSplittingFieldProgress
    ; priorNextMissingArithmeticInputIsNormalizedLeftEigenbases =
        refl
    ; normalizedLeftEigenbasesSupplied =
        true
    ; normalizedLeftEigenbasesSuppliedIsTrue =
        refl
    ; remainingMissingArithmeticInputs =
        canonicalCKMArithmeticInputSlotsAfterNormalizedLeftEigenbasesSupply
    ; remainingMissingArithmeticInputsAreCanonical =
        refl
    ; nextMissingArithmeticInput =
        missingCKMProductClosureWitness
    ; nextMissingArithmeticInputIsCKMProductClosureWitness =
        refl
    ; spectralQueueStillIncomplete =
        true
    ; spectralQueueStillIncompleteIsTrue =
        refl
    ; progressBoundary =
        "A staged normalized left-eigenbasis checkpoint is now recorded in the Yukawa spectral queue"
        ∷ "The next exact spectral blocker advances to the CKM product-field closure witness"
        ∷ "Unitarity residual closure remains unresolved and promotion remains blocked"
        ∷ []
    }

ckmNormalizedLeftEigenbasisProgressAdvancesNextInputToCKMProductClosureWitness :
  nextMissingArithmeticInput canonicalCKMNormalizedLeftEigenbasisProgress
  ≡
  missingCKMProductClosureWitness
ckmNormalizedLeftEigenbasisProgressAdvancesNextInputToCKMProductClosureWitness =
  refl

ckmNormalizedLeftEigenbasisProgressKeepsQueueIncomplete :
  spectralQueueStillIncomplete canonicalCKMNormalizedLeftEigenbasisProgress
  ≡
  true
ckmNormalizedLeftEigenbasisProgressKeepsQueueIncomplete =
  refl

------------------------------------------------------------------------
-- Bounded executable FactorVec-to-Yukawa FN exponent surface.
--
-- This is intentionally only an exponent-level arithmetic surface.  It maps
-- the current concrete GL.FactorVec carrier to bounded 3x3 up/down FN
-- exponent entries.  It does not apply Higgs vev normalization, does not
-- construct physical Yukawa couplings, and does not discharge DHR
-- compatibility or CKM product closure.

data YukawaSectorTag : Set where
  upYukawaSector :
    YukawaSectorTag

  downYukawaSector :
    YukawaSectorTag

canonicalYukawaSectorTags :
  List YukawaSectorTag
canonicalYukawaSectorTags =
  upYukawaSector
  ∷ downYukawaSector
  ∷ []

factorVecToUpYukawaFNExponent :
  YukawaMatrix3x3EntrySlot →
  GL.FactorVec →
  Nat
factorVecToUpYukawaFNExponent
  missingY11
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  e2 + e3
factorVecToUpYukawaFNExponent
  missingY12
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  e2 + e5
factorVecToUpYukawaFNExponent
  missingY13
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  e2 + e7
factorVecToUpYukawaFNExponent
  missingY21
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  e3 + e5
factorVecToUpYukawaFNExponent
  missingY22
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  e3 + e7
factorVecToUpYukawaFNExponent
  missingY23
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  e5 + e7
factorVecToUpYukawaFNExponent
  missingY31
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  e11 + e13
factorVecToUpYukawaFNExponent
  missingY32
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  e17 + e19
factorVecToUpYukawaFNExponent
  missingY33
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  e23

factorVecToDownYukawaFNExponent :
  YukawaMatrix3x3EntrySlot →
  GL.FactorVec →
  Nat
factorVecToDownYukawaFNExponent
  missingY11
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  e29 + e31
factorVecToDownYukawaFNExponent
  missingY12
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  e29 + e41
factorVecToDownYukawaFNExponent
  missingY13
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  e29 + e47
factorVecToDownYukawaFNExponent
  missingY21
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  e31 + e41
factorVecToDownYukawaFNExponent
  missingY22
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  suc (e31 + e47)
factorVecToDownYukawaFNExponent
  missingY23
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  e41 + e47
factorVecToDownYukawaFNExponent
  missingY31
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  e59 + e71
factorVecToDownYukawaFNExponent
  missingY32
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  e2 + e59
factorVecToDownYukawaFNExponent
  missingY33
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  e3 + e71

factorVecToYukawaFNExponent :
  YukawaSectorTag →
  YukawaMatrix3x3EntrySlot →
  GL.FactorVec →
  Nat
factorVecToYukawaFNExponent upYukawaSector =
  factorVecToUpYukawaFNExponent
factorVecToYukawaFNExponent downYukawaSector =
  factorVecToDownYukawaFNExponent

data CKMExplicitFNChargeTableSlot : Set where
  leftQ1FNChargeSlot :
    CKMExplicitFNChargeTableSlot

  leftQ2FNChargeSlot :
    CKMExplicitFNChargeTableSlot

  leftQ3FNChargeSlot :
    CKMExplicitFNChargeTableSlot

  rightU1FNChargeSlot :
    CKMExplicitFNChargeTableSlot

  rightU2FNChargeSlot :
    CKMExplicitFNChargeTableSlot

  rightU3FNChargeSlot :
    CKMExplicitFNChargeTableSlot

  rightD1FNChargeSlot :
    CKMExplicitFNChargeTableSlot

  rightD2FNChargeSlot :
    CKMExplicitFNChargeTableSlot

  rightD3FNChargeSlot :
    CKMExplicitFNChargeTableSlot

  downHiggsFNChargeSlot :
    CKMExplicitFNChargeTableSlot

  upHiggsAdapter4ChargeSlot :
    CKMExplicitFNChargeTableSlot

canonicalCKMExplicitFNChargeTableSlots :
  List CKMExplicitFNChargeTableSlot
canonicalCKMExplicitFNChargeTableSlots =
  leftQ1FNChargeSlot
  ∷ leftQ2FNChargeSlot
  ∷ leftQ3FNChargeSlot
  ∷ rightU1FNChargeSlot
  ∷ rightU2FNChargeSlot
  ∷ rightU3FNChargeSlot
  ∷ rightD1FNChargeSlot
  ∷ rightD2FNChargeSlot
  ∷ rightD3FNChargeSlot
  ∷ downHiggsFNChargeSlot
  ∷ upHiggsAdapter4ChargeSlot
  ∷ []

record CKMExplicitFNChargeTable : Set where
  field
    fnChargeTableVector :
      GL.FactorVec

    fnChargeTableSlots :
      List CKMExplicitFNChargeTableSlot

    fnChargeTableSlotsAreCanonical :
      fnChargeTableSlots ≡ canonicalCKMExplicitFNChargeTableSlots

    fnChargeLeftQ1 :
      Nat

    fnChargeLeftQ1IsP11 :
      fnChargeLeftQ1 ≡ GL.Vec15.e11 fnChargeTableVector

    fnChargeLeftQ2 :
      Nat

    fnChargeLeftQ2IsP23 :
      fnChargeLeftQ2 ≡ GL.Vec15.e23 fnChargeTableVector

    fnChargeLeftQ3 :
      Nat

    fnChargeLeftQ3IsP47 :
      fnChargeLeftQ3 ≡ GL.Vec15.e47 fnChargeTableVector

    fnChargeRightU1 :
      Nat

    fnChargeRightU1IsP13 :
      fnChargeRightU1 ≡ GL.Vec15.e13 fnChargeTableVector

    fnChargeRightU2 :
      Nat

    fnChargeRightU2IsP29 :
      fnChargeRightU2 ≡ GL.Vec15.e29 fnChargeTableVector

    fnChargeRightU3 :
      Nat

    fnChargeRightU3IsP59 :
      fnChargeRightU3 ≡ GL.Vec15.e59 fnChargeTableVector

    fnChargeRightD1 :
      Nat

    fnChargeRightD1IsP17 :
      fnChargeRightD1 ≡ GL.Vec15.e17 fnChargeTableVector

    fnChargeRightD2 :
      Nat

    fnChargeRightD2IsP31 :
      fnChargeRightD2 ≡ GL.Vec15.e31 fnChargeTableVector

    fnChargeRightD3 :
      Nat

    fnChargeRightD3IsP71 :
      fnChargeRightD3 ≡ GL.Vec15.e71 fnChargeTableVector

    fnChargeDownHiggsSocket :
      Nat

    fnChargeDownHiggsSocketIsP41 :
      fnChargeDownHiggsSocket ≡ GL.Vec15.e41 fnChargeTableVector

    fnChargeUpHiggsAdapter4SocketPromoted :
      Bool

    fnChargeUpHiggsAdapter4SocketPromotedIsFalse :
      fnChargeUpHiggsAdapter4SocketPromoted ≡ false

    fnChargeGeorgiJarlskogY22Numerator :
      Nat

    fnChargeGeorgiJarlskogY22NumeratorIs3 :
      fnChargeGeorgiJarlskogY22Numerator ≡ suc (suc (suc zero))

    fnChargeGeorgiJarlskogY22Denominator :
      Nat

    fnChargeGeorgiJarlskogY22DenominatorIs1 :
      fnChargeGeorgiJarlskogY22Denominator ≡ suc zero

    fnChargeGeorgiJarlskogY22Positive :
      Bool

    fnChargeGeorgiJarlskogY22PositiveIsFalse :
      fnChargeGeorgiJarlskogY22Positive ≡ false

    fnChargeGeorgiJarlskogY22SocketRecorded :
      Bool

    fnChargeGeorgiJarlskogY22SocketRecordedIsTrue :
      fnChargeGeorgiJarlskogY22SocketRecorded ≡ true

    fnChargePhysicalHiggsPromotion :
      Bool

    fnChargePhysicalHiggsPromotionIsFalse :
      fnChargePhysicalHiggsPromotion ≡ false

    fnChargeTableBoundary :
      List String

open CKMExplicitFNChargeTable public

factorVecToExplicitFNChargeTable :
  GL.FactorVec →
  CKMExplicitFNChargeTable
factorVecToExplicitFNChargeTable v =
  record
    { fnChargeTableVector =
        v
    ; fnChargeTableSlots =
        canonicalCKMExplicitFNChargeTableSlots
    ; fnChargeTableSlotsAreCanonical =
        refl
    ; fnChargeLeftQ1 =
        GL.Vec15.e11 v
    ; fnChargeLeftQ1IsP11 =
        refl
    ; fnChargeLeftQ2 =
        GL.Vec15.e23 v
    ; fnChargeLeftQ2IsP23 =
        refl
    ; fnChargeLeftQ3 =
        GL.Vec15.e47 v
    ; fnChargeLeftQ3IsP47 =
        refl
    ; fnChargeRightU1 =
        GL.Vec15.e13 v
    ; fnChargeRightU1IsP13 =
        refl
    ; fnChargeRightU2 =
        GL.Vec15.e29 v
    ; fnChargeRightU2IsP29 =
        refl
    ; fnChargeRightU3 =
        GL.Vec15.e59 v
    ; fnChargeRightU3IsP59 =
        refl
    ; fnChargeRightD1 =
        GL.Vec15.e17 v
    ; fnChargeRightD1IsP17 =
        refl
    ; fnChargeRightD2 =
        GL.Vec15.e31 v
    ; fnChargeRightD2IsP31 =
        refl
    ; fnChargeRightD3 =
        GL.Vec15.e71 v
    ; fnChargeRightD3IsP71 =
        refl
    ; fnChargeDownHiggsSocket =
        GL.Vec15.e41 v
    ; fnChargeDownHiggsSocketIsP41 =
        refl
    ; fnChargeUpHiggsAdapter4SocketPromoted =
        false
    ; fnChargeUpHiggsAdapter4SocketPromotedIsFalse =
        refl
    ; fnChargeGeorgiJarlskogY22Numerator =
        suc (suc (suc zero))
    ; fnChargeGeorgiJarlskogY22NumeratorIs3 =
        refl
    ; fnChargeGeorgiJarlskogY22Denominator =
        suc zero
    ; fnChargeGeorgiJarlskogY22DenominatorIs1 =
        refl
    ; fnChargeGeorgiJarlskogY22Positive =
        false
    ; fnChargeGeorgiJarlskogY22PositiveIsFalse =
        refl
    ; fnChargeGeorgiJarlskogY22SocketRecorded =
        true
    ; fnChargeGeorgiJarlskogY22SocketRecordedIsTrue =
        refl
    ; fnChargePhysicalHiggsPromotion =
        false
    ; fnChargePhysicalHiggsPromotionIsFalse =
        refl
    ; fnChargeTableBoundary =
        "Explicit FN charge table: Q=(p11,p23,p47), u=(p13,p29,p59), d=(p17,p31,p71), and the down-Higgs socket is p41"
        ∷ "The up-Higgs charge is retained as an Adapter 4 socket and is not promoted here"
        ∷ "The Georgi-Jarlskog y22 correction is recorded as -3 over 1 on the staged down-sector socket"
        ∷ "This table feeds exponent-level entry certificates only; physical Higgs normalization and CKM promotion remain false"
        ∷ []
    }

canonicalCKMExplicitFNChargeTable :
  CKMExplicitFNChargeTable
canonicalCKMExplicitFNChargeTable =
  factorVecToExplicitFNChargeTable canonicalYukawaFNExponentWitnessVector

ckmExplicitFNChargeTableRecordsGeorgiJarlskogY22 :
  fnChargeGeorgiJarlskogY22SocketRecorded
    canonicalCKMExplicitFNChargeTable
  ≡
  true
ckmExplicitFNChargeTableRecordsGeorgiJarlskogY22 =
  refl

ckmExplicitFNChargeTableKeepsUpHiggsAdapter4Open :
  fnChargeUpHiggsAdapter4SocketPromoted
    canonicalCKMExplicitFNChargeTable
  ≡
  false
ckmExplicitFNChargeTableKeepsUpHiggsAdapter4Open =
  refl

data CKMFNExponentCertificateSlot : Set where
  upY11FNExponentCertificate :
    CKMFNExponentCertificateSlot
  upY12FNExponentCertificate :
    CKMFNExponentCertificateSlot
  upY13FNExponentCertificate :
    CKMFNExponentCertificateSlot
  upY21FNExponentCertificate :
    CKMFNExponentCertificateSlot
  upY22FNExponentCertificate :
    CKMFNExponentCertificateSlot
  upY23FNExponentCertificate :
    CKMFNExponentCertificateSlot
  upY31FNExponentCertificate :
    CKMFNExponentCertificateSlot
  upY32FNExponentCertificate :
    CKMFNExponentCertificateSlot
  upY33FNExponentCertificate :
    CKMFNExponentCertificateSlot
  downY11FNExponentCertificate :
    CKMFNExponentCertificateSlot
  downY12FNExponentCertificate :
    CKMFNExponentCertificateSlot
  downY13FNExponentCertificate :
    CKMFNExponentCertificateSlot
  downY21FNExponentCertificate :
    CKMFNExponentCertificateSlot
  downY22FNExponentCertificate :
    CKMFNExponentCertificateSlot
  downY23FNExponentCertificate :
    CKMFNExponentCertificateSlot
  downY31FNExponentCertificate :
    CKMFNExponentCertificateSlot
  downY32FNExponentCertificate :
    CKMFNExponentCertificateSlot
  downY33FNExponentCertificate :
    CKMFNExponentCertificateSlot

canonicalCKMFNExponentCertificateSlots :
  List CKMFNExponentCertificateSlot
canonicalCKMFNExponentCertificateSlots =
  upY11FNExponentCertificate
  ∷ upY12FNExponentCertificate
  ∷ upY13FNExponentCertificate
  ∷ upY21FNExponentCertificate
  ∷ upY22FNExponentCertificate
  ∷ upY23FNExponentCertificate
  ∷ upY31FNExponentCertificate
  ∷ upY32FNExponentCertificate
  ∷ upY33FNExponentCertificate
  ∷ downY11FNExponentCertificate
  ∷ downY12FNExponentCertificate
  ∷ downY13FNExponentCertificate
  ∷ downY21FNExponentCertificate
  ∷ downY22FNExponentCertificate
  ∷ downY23FNExponentCertificate
  ∷ downY31FNExponentCertificate
  ∷ downY32FNExponentCertificate
  ∷ downY33FNExponentCertificate
  ∷ []

record CKMFactorVecToYukawaEntryMapSurface : Set₁ where
  field
    factorVecInputCarrier :
      Set

    factorVecInputCarrierIsCurrentGLFactorVec :
      factorVecInputCarrier ≡ GL.FactorVec

    yukawaEntryExponentCarrier :
      Set

    yukawaEntryExponentCarrierIsNat :
      yukawaEntryExponentCarrier ≡ Nat

    yukawaSectors :
      List YukawaSectorTag

    yukawaSectorsAreCanonical :
      yukawaSectors ≡ canonicalYukawaSectorTags

    boundedEntrySlots :
      List YukawaMatrix3x3EntrySlot

    boundedEntrySlotsAreCanonical3x3 :
      boundedEntrySlots ≡ canonicalYukawaMatrix3x3EntrySlots

    upEntryExponentMap :
      YukawaMatrix3x3EntrySlot →
      GL.FactorVec →
      Nat

    upEntryExponentMapIsCanonical :
      upEntryExponentMap ≡ factorVecToUpYukawaFNExponent

    downEntryExponentMap :
      YukawaMatrix3x3EntrySlot →
      GL.FactorVec →
      Nat

    downEntryExponentMapIsCanonical :
      downEntryExponentMap ≡ factorVecToDownYukawaFNExponent

    joinedSectorEntryExponentMap :
      YukawaSectorTag →
      YukawaMatrix3x3EntrySlot →
      GL.FactorVec →
      Nat

    joinedSectorEntryExponentMapIsCanonical :
      joinedSectorEntryExponentMap ≡ factorVecToYukawaFNExponent

    factorVecToYukawaEntryMapSupplied :
      Bool

    factorVecToYukawaEntryMapSuppliedIsTrue :
      factorVecToYukawaEntryMapSupplied ≡ true

    physicalYukawaNormalizationPromoted :
      Bool

    physicalYukawaNormalizationPromotedIsFalse :
      physicalYukawaNormalizationPromoted ≡ false

    firstMissingArithmeticInputAfterFactorVecMap :
      CKMArithmeticInputSlot

    firstMissingArithmeticInputAfterFactorVecMapIsEntryFieldMembership :
      firstMissingArithmeticInputAfterFactorVecMap
      ≡
      missingEntryFieldMembershipCertificates

    mapSurfaceBoundary :
      List String

open CKMFactorVecToYukawaEntryMapSurface public

canonicalCKMFactorVecToYukawaEntryMapSurface :
  CKMFactorVecToYukawaEntryMapSurface
canonicalCKMFactorVecToYukawaEntryMapSurface =
  record
    { factorVecInputCarrier =
        GL.FactorVec
    ; factorVecInputCarrierIsCurrentGLFactorVec =
        refl
    ; yukawaEntryExponentCarrier =
        Nat
    ; yukawaEntryExponentCarrierIsNat =
        refl
    ; yukawaSectors =
        canonicalYukawaSectorTags
    ; yukawaSectorsAreCanonical =
        refl
    ; boundedEntrySlots =
        canonicalYukawaMatrix3x3EntrySlots
    ; boundedEntrySlotsAreCanonical3x3 =
        refl
    ; upEntryExponentMap =
        factorVecToUpYukawaFNExponent
    ; upEntryExponentMapIsCanonical =
        refl
    ; downEntryExponentMap =
        factorVecToDownYukawaFNExponent
    ; downEntryExponentMapIsCanonical =
        refl
    ; joinedSectorEntryExponentMap =
        factorVecToYukawaFNExponent
    ; joinedSectorEntryExponentMapIsCanonical =
        refl
    ; factorVecToYukawaEntryMapSupplied =
        true
    ; factorVecToYukawaEntryMapSuppliedIsTrue =
        refl
    ; physicalYukawaNormalizationPromoted =
        false
    ; physicalYukawaNormalizationPromotedIsFalse =
        refl
    ; firstMissingArithmeticInputAfterFactorVecMap =
        missingEntryFieldMembershipCertificates
    ; firstMissingArithmeticInputAfterFactorVecMapIsEntryFieldMembership =
        refl
    ; mapSurfaceBoundary =
        "A bounded executable map from GL.FactorVec to 3x3 up/down FN exponent entries is supplied"
        ∷ "The map emits Nat exponents only; it does not construct physical Yukawa couplings or Higgs-normalized masses"
        ∷ "The next arithmetic blocker is entry-field membership certificates for the staged exponent entries"
        ∷ "DHR intertwiner compatibility, CKM product closure, and carrier mixing promotion remain outside this map surface"
        ∷ []
    }

record CKMExactFNExponentCertificateInventory : Set₂ where
  field
    fnExponentMapSurface :
      CKMFactorVecToYukawaEntryMapSurface

    fnExponentCertificateVector :
      GL.FactorVec

    fnExponentCertificateVectorIsCanonical :
      fnExponentCertificateVector
      ≡
      canonicalYukawaFNExponentWitnessVector

    fnExponentCertificateSlots :
      List CKMFNExponentCertificateSlot

    fnExponentCertificateSlotsAreCanonical :
      fnExponentCertificateSlots
      ≡
      canonicalCKMFNExponentCertificateSlots

    upY11ExponentCertificate :
      factorVecToYukawaFNExponent
        upYukawaSector
        missingY11
        fnExponentCertificateVector
      ≡
      factorVecToUpYukawaFNExponent
        missingY11
        fnExponentCertificateVector

    upY12ExponentCertificate :
      factorVecToYukawaFNExponent
        upYukawaSector
        missingY12
        fnExponentCertificateVector
      ≡
      factorVecToUpYukawaFNExponent
        missingY12
        fnExponentCertificateVector

    upY13ExponentCertificate :
      factorVecToYukawaFNExponent
        upYukawaSector
        missingY13
        fnExponentCertificateVector
      ≡
      factorVecToUpYukawaFNExponent
        missingY13
        fnExponentCertificateVector

    upY21ExponentCertificate :
      factorVecToYukawaFNExponent
        upYukawaSector
        missingY21
        fnExponentCertificateVector
      ≡
      factorVecToUpYukawaFNExponent
        missingY21
        fnExponentCertificateVector

    upY22ExponentCertificate :
      factorVecToYukawaFNExponent
        upYukawaSector
        missingY22
        fnExponentCertificateVector
      ≡
      factorVecToUpYukawaFNExponent
        missingY22
        fnExponentCertificateVector

    upY23ExponentCertificate :
      factorVecToYukawaFNExponent
        upYukawaSector
        missingY23
        fnExponentCertificateVector
      ≡
      factorVecToUpYukawaFNExponent
        missingY23
        fnExponentCertificateVector

    upY31ExponentCertificate :
      factorVecToYukawaFNExponent
        upYukawaSector
        missingY31
        fnExponentCertificateVector
      ≡
      factorVecToUpYukawaFNExponent
        missingY31
        fnExponentCertificateVector

    upY32ExponentCertificate :
      factorVecToYukawaFNExponent
        upYukawaSector
        missingY32
        fnExponentCertificateVector
      ≡
      factorVecToUpYukawaFNExponent
        missingY32
        fnExponentCertificateVector

    upY33ExponentCertificate :
      factorVecToYukawaFNExponent
        upYukawaSector
        missingY33
        fnExponentCertificateVector
      ≡
      factorVecToUpYukawaFNExponent
        missingY33
        fnExponentCertificateVector

    downY11ExponentCertificate :
      factorVecToYukawaFNExponent
        downYukawaSector
        missingY11
        fnExponentCertificateVector
      ≡
      factorVecToDownYukawaFNExponent
        missingY11
        fnExponentCertificateVector

    downY12ExponentCertificate :
      factorVecToYukawaFNExponent
        downYukawaSector
        missingY12
        fnExponentCertificateVector
      ≡
      factorVecToDownYukawaFNExponent
        missingY12
        fnExponentCertificateVector

    downY13ExponentCertificate :
      factorVecToYukawaFNExponent
        downYukawaSector
        missingY13
        fnExponentCertificateVector
      ≡
      factorVecToDownYukawaFNExponent
        missingY13
        fnExponentCertificateVector

    downY21ExponentCertificate :
      factorVecToYukawaFNExponent
        downYukawaSector
        missingY21
        fnExponentCertificateVector
      ≡
      factorVecToDownYukawaFNExponent
        missingY21
        fnExponentCertificateVector

    downY22ExponentCertificate :
      factorVecToYukawaFNExponent
        downYukawaSector
        missingY22
        fnExponentCertificateVector
      ≡
      factorVecToDownYukawaFNExponent
        missingY22
        fnExponentCertificateVector

    downY23ExponentCertificate :
      factorVecToYukawaFNExponent
        downYukawaSector
        missingY23
        fnExponentCertificateVector
      ≡
      factorVecToDownYukawaFNExponent
        missingY23
        fnExponentCertificateVector

    downY31ExponentCertificate :
      factorVecToYukawaFNExponent
        downYukawaSector
        missingY31
        fnExponentCertificateVector
      ≡
      factorVecToDownYukawaFNExponent
        missingY31
        fnExponentCertificateVector

    downY32ExponentCertificate :
      factorVecToYukawaFNExponent
        downYukawaSector
        missingY32
        fnExponentCertificateVector
      ≡
      factorVecToDownYukawaFNExponent
        missingY32
        fnExponentCertificateVector

    downY33ExponentCertificate :
      factorVecToYukawaFNExponent
        downYukawaSector
        missingY33
        fnExponentCertificateVector
      ≡
      factorVecToDownYukawaFNExponent
        missingY33
        fnExponentCertificateVector

    exactTexturePromoted :
      Bool

    exactTexturePromotedIsFalse :
      exactTexturePromoted ≡ false

    certificateInventoryBoundary :
      List String

open CKMExactFNExponentCertificateInventory public

canonicalCKMExactFNExponentCertificateInventory :
  CKMExactFNExponentCertificateInventory
canonicalCKMExactFNExponentCertificateInventory =
  record
    { fnExponentMapSurface =
        canonicalCKMFactorVecToYukawaEntryMapSurface
    ; fnExponentCertificateVector =
        canonicalYukawaFNExponentWitnessVector
    ; fnExponentCertificateVectorIsCanonical =
        refl
    ; fnExponentCertificateSlots =
        canonicalCKMFNExponentCertificateSlots
    ; fnExponentCertificateSlotsAreCanonical =
        refl
    ; upY11ExponentCertificate =
        refl
    ; upY12ExponentCertificate =
        refl
    ; upY13ExponentCertificate =
        refl
    ; upY21ExponentCertificate =
        refl
    ; upY22ExponentCertificate =
        refl
    ; upY23ExponentCertificate =
        refl
    ; upY31ExponentCertificate =
        refl
    ; upY32ExponentCertificate =
        refl
    ; upY33ExponentCertificate =
        refl
    ; downY11ExponentCertificate =
        refl
    ; downY12ExponentCertificate =
        refl
    ; downY13ExponentCertificate =
        refl
    ; downY21ExponentCertificate =
        refl
    ; downY22ExponentCertificate =
        refl
    ; downY23ExponentCertificate =
        refl
    ; downY31ExponentCertificate =
        refl
    ; downY32ExponentCertificate =
        refl
    ; downY33ExponentCertificate =
        refl
    ; exactTexturePromoted =
        false
    ; exactTexturePromotedIsFalse =
        refl
    ; certificateInventoryBoundary =
        "All eighteen bounded up/down FN exponent certificate slots are inventoried"
        ∷ "The down y22 exponent includes a staged successor socket for the Georgi-Jarlskog correction checkpoint"
        ∷ "The inventory certifies the executable exponent map only and does not promote exact Yukawa textures"
        ∷ []
    }

------------------------------------------------------------------------
-- Executable staged entry-field and Hermitian arithmetic.
--
-- This layer computes only in the finite staged FN-entry carrier above.  A
-- staged entry has Nat exponent/numerator/denominator/sign data, so its local
-- membership certificate is rationalQ.  That does not promote the physical
-- Higgs-normalized Yukawa entry or the final CKM field decision.

sameSign :
  Bool →
  Bool →
  Bool
sameSign true true =
  true
sameSign true false =
  false
sameSign false true =
  false
sameSign false false =
  true

record CKMExactFNMonomial : Set where
  field
    monomialFNExponent :
      Nat

    monomialNumerator :
      Nat

    monomialDenominator :
      Nat

    monomialPositive :
      Bool

    monomialEntryField :
      CKMEntryField

    monomialEntryFieldIsRationalQ :
      monomialEntryField ≡ rationalQ

    monomialFieldDecision :
      CKMEntryFieldDecision

    monomialFieldDecisionIsQAlone :
      monomialFieldDecision ≡ qAloneSuffices

open CKMExactFNMonomial public

yukawaEntryToExactFNMonomial :
  YukawaEntryCarrier →
  CKMExactFNMonomial
yukawaEntryToExactFNMonomial (stagedUpFNYukawaEntry slot exponent) =
  record
    { monomialFNExponent =
        exponent
    ; monomialNumerator =
        1
    ; monomialDenominator =
        1
    ; monomialPositive =
        true
    ; monomialEntryField =
        rationalQ
    ; monomialEntryFieldIsRationalQ =
        refl
    ; monomialFieldDecision =
        qAloneSuffices
    ; monomialFieldDecisionIsQAlone =
        refl
    }
yukawaEntryToExactFNMonomial
  (stagedDownFNYukawaEntry slot exponent numerator denominator positive gjSocket) =
  record
    { monomialFNExponent =
        exponent
    ; monomialNumerator =
        numerator
    ; monomialDenominator =
        denominator
    ; monomialPositive =
        positive
    ; monomialEntryField =
        rationalQ
    ; monomialEntryFieldIsRationalQ =
        refl
    ; monomialFieldDecision =
        qAloneSuffices
    ; monomialFieldDecisionIsQAlone =
        refl
    }

multiplyExactFNMonomial :
  CKMExactFNMonomial →
  CKMExactFNMonomial →
  CKMExactFNMonomial
multiplyExactFNMonomial left right =
  record
    { monomialFNExponent =
        monomialFNExponent left + monomialFNExponent right
    ; monomialNumerator =
        monomialNumerator left * monomialNumerator right
    ; monomialDenominator =
        monomialDenominator left * monomialDenominator right
    ; monomialPositive =
        sameSign (monomialPositive left) (monomialPositive right)
    ; monomialEntryField =
        rationalQ
    ; monomialEntryFieldIsRationalQ =
        refl
    ; monomialFieldDecision =
        qAloneSuffices
    ; monomialFieldDecisionIsQAlone =
        refl
    }

multiplyYukawaEntriesToHermitianTerm :
  YukawaEntryCarrier →
  YukawaEntryCarrier →
  CKMExactFNMonomial
multiplyYukawaEntriesToHermitianTerm left right =
  multiplyExactFNMonomial
    (yukawaEntryToExactFNMonomial left)
    (yukawaEntryToExactFNMonomial right)

data CKMMatrixIndex3 : Set where
  matrixIndex1 :
    CKMMatrixIndex3

  matrixIndex2 :
    CKMMatrixIndex3

  matrixIndex3 :
    CKMMatrixIndex3

matrixIndexSlot :
  CKMMatrixIndex3 →
  CKMMatrixIndex3 →
  YukawaMatrix3x3EntrySlot
matrixIndexSlot matrixIndex1 matrixIndex1 =
  missingY11
matrixIndexSlot matrixIndex1 matrixIndex2 =
  missingY12
matrixIndexSlot matrixIndex1 matrixIndex3 =
  missingY13
matrixIndexSlot matrixIndex2 matrixIndex1 =
  missingY21
matrixIndexSlot matrixIndex2 matrixIndex2 =
  missingY22
matrixIndexSlot matrixIndex2 matrixIndex3 =
  missingY23
matrixIndexSlot matrixIndex3 matrixIndex1 =
  missingY31
matrixIndexSlot matrixIndex3 matrixIndex2 =
  missingY32
matrixIndexSlot matrixIndex3 matrixIndex3 =
  missingY33

upYukawaEntryAt :
  GL.FactorVec →
  CKMMatrixIndex3 →
  CKMMatrixIndex3 →
  YukawaEntryCarrier
upYukawaEntryAt v row col =
  factorVecToStagedUpYukawaEntryMap v (matrixIndexSlot row col)

downYukawaEntryAt :
  GL.FactorVec →
  CKMMatrixIndex3 →
  CKMMatrixIndex3 →
  YukawaEntryCarrier
downYukawaEntryAt v row col =
  factorVecToStagedDownYukawaEntryMap v (matrixIndexSlot row col)

record CKMHermitianEntrySum3 : Set where
  field
    hermitianTerm1 :
      CKMExactFNMonomial

    hermitianTerm2 :
      CKMExactFNMonomial

    hermitianTerm3 :
      CKMExactFNMonomial

    hermitianEntryField :
      CKMEntryField

    hermitianEntryFieldIsRationalQ :
      hermitianEntryField ≡ rationalQ

open CKMHermitianEntrySum3 public

hermitianEntryFromYukawaRows :
  (GL.FactorVec → CKMMatrixIndex3 → CKMMatrixIndex3 → YukawaEntryCarrier) →
  GL.FactorVec →
  CKMMatrixIndex3 →
  CKMMatrixIndex3 →
  CKMHermitianEntrySum3
hermitianEntryFromYukawaRows entryAt v row col =
  record
    { hermitianTerm1 =
        multiplyYukawaEntriesToHermitianTerm
          (entryAt v row matrixIndex1)
          (entryAt v col matrixIndex1)
    ; hermitianTerm2 =
        multiplyYukawaEntriesToHermitianTerm
          (entryAt v row matrixIndex2)
          (entryAt v col matrixIndex2)
    ; hermitianTerm3 =
        multiplyYukawaEntriesToHermitianTerm
          (entryAt v row matrixIndex3)
          (entryAt v col matrixIndex3)
    ; hermitianEntryField =
        rationalQ
    ; hermitianEntryFieldIsRationalQ =
        refl
    }

upHermitianEntry :
  GL.FactorVec →
  CKMMatrixIndex3 →
  CKMMatrixIndex3 →
  CKMHermitianEntrySum3
upHermitianEntry =
  hermitianEntryFromYukawaRows upYukawaEntryAt

downHermitianEntry :
  GL.FactorVec →
  CKMMatrixIndex3 →
  CKMMatrixIndex3 →
  CKMHermitianEntrySum3
downHermitianEntry =
  hermitianEntryFromYukawaRows downYukawaEntryAt

record CKMHermitianProduct3x3 : Set where
  field
    hermitianH11 :
      CKMHermitianEntrySum3

    hermitianH12 :
      CKMHermitianEntrySum3

    hermitianH13 :
      CKMHermitianEntrySum3

    hermitianH21 :
      CKMHermitianEntrySum3

    hermitianH22 :
      CKMHermitianEntrySum3

    hermitianH23 :
      CKMHermitianEntrySum3

    hermitianH31 :
      CKMHermitianEntrySum3

    hermitianH32 :
      CKMHermitianEntrySum3

    hermitianH33 :
      CKMHermitianEntrySum3

open CKMHermitianProduct3x3 public

upHermitianProduct3x3 :
  GL.FactorVec →
  CKMHermitianProduct3x3
upHermitianProduct3x3 v =
  record
    { hermitianH11 =
        upHermitianEntry v matrixIndex1 matrixIndex1
    ; hermitianH12 =
        upHermitianEntry v matrixIndex1 matrixIndex2
    ; hermitianH13 =
        upHermitianEntry v matrixIndex1 matrixIndex3
    ; hermitianH21 =
        upHermitianEntry v matrixIndex2 matrixIndex1
    ; hermitianH22 =
        upHermitianEntry v matrixIndex2 matrixIndex2
    ; hermitianH23 =
        upHermitianEntry v matrixIndex2 matrixIndex3
    ; hermitianH31 =
        upHermitianEntry v matrixIndex3 matrixIndex1
    ; hermitianH32 =
        upHermitianEntry v matrixIndex3 matrixIndex2
    ; hermitianH33 =
        upHermitianEntry v matrixIndex3 matrixIndex3
    }

downHermitianProduct3x3 :
  GL.FactorVec →
  CKMHermitianProduct3x3
downHermitianProduct3x3 v =
  record
    { hermitianH11 =
        downHermitianEntry v matrixIndex1 matrixIndex1
    ; hermitianH12 =
        downHermitianEntry v matrixIndex1 matrixIndex2
    ; hermitianH13 =
        downHermitianEntry v matrixIndex1 matrixIndex3
    ; hermitianH21 =
        downHermitianEntry v matrixIndex2 matrixIndex1
    ; hermitianH22 =
        downHermitianEntry v matrixIndex2 matrixIndex2
    ; hermitianH23 =
        downHermitianEntry v matrixIndex2 matrixIndex3
    ; hermitianH31 =
        downHermitianEntry v matrixIndex3 matrixIndex1
    ; hermitianH32 =
        downHermitianEntry v matrixIndex3 matrixIndex2
    ; hermitianH33 =
        downHermitianEntry v matrixIndex3 matrixIndex3
    }

hermitianTraceTerms :
  CKMHermitianProduct3x3 →
  List CKMExactFNMonomial
hermitianTraceTerms h =
  hermitianTerm1 (hermitianH11 h)
  ∷ hermitianTerm2 (hermitianH11 h)
  ∷ hermitianTerm3 (hermitianH11 h)
  ∷ hermitianTerm1 (hermitianH22 h)
  ∷ hermitianTerm2 (hermitianH22 h)
  ∷ hermitianTerm3 (hermitianH22 h)
  ∷ hermitianTerm1 (hermitianH33 h)
  ∷ hermitianTerm2 (hermitianH33 h)
  ∷ hermitianTerm3 (hermitianH33 h)
  ∷ []

record CKMCharacteristicPolynomialFiniteStage : Set₁ where
  field
    characteristicHermitianProduct :
      CKMHermitianProduct3x3

    characteristicTraceTerms :
      List CKMExactFNMonomial

    characteristicTraceTermsAreComputed :
      characteristicTraceTerms
      ≡
      hermitianTraceTerms characteristicHermitianProduct

    characteristicTraceField :
      CKMEntryField

    characteristicTraceFieldIsRationalQ :
      characteristicTraceField ≡ rationalQ

    characteristicPrincipalMinorCarrier :
      Set

    characteristicPrincipalMinorCarrierIsStagedHermitianSum :
      characteristicPrincipalMinorCarrier ≡ CKMHermitianEntrySum3

    characteristicDeterminantCarrier :
      Set

    characteristicDeterminantCarrierIsStagedHermitianSum :
      characteristicDeterminantCarrier ≡ CKMHermitianEntrySum3

    characteristicPrincipalMinorExpanded :
      Bool

    characteristicPrincipalMinorExpandedIsFalse :
      characteristicPrincipalMinorExpanded ≡ false

    characteristicDeterminantExpanded :
      Bool

    characteristicDeterminantExpandedIsFalse :
      characteristicDeterminantExpanded ≡ false

open CKMCharacteristicPolynomialFiniteStage public

upCharacteristicPolynomialFiniteStage :
  GL.FactorVec →
  CKMCharacteristicPolynomialFiniteStage
upCharacteristicPolynomialFiniteStage v =
  record
    { characteristicHermitianProduct =
        upHermitianProduct3x3 v
    ; characteristicTraceTerms =
        hermitianTraceTerms (upHermitianProduct3x3 v)
    ; characteristicTraceTermsAreComputed =
        refl
    ; characteristicTraceField =
        rationalQ
    ; characteristicTraceFieldIsRationalQ =
        refl
    ; characteristicPrincipalMinorCarrier =
        CKMHermitianEntrySum3
    ; characteristicPrincipalMinorCarrierIsStagedHermitianSum =
        refl
    ; characteristicDeterminantCarrier =
        CKMHermitianEntrySum3
    ; characteristicDeterminantCarrierIsStagedHermitianSum =
        refl
    ; characteristicPrincipalMinorExpanded =
        false
    ; characteristicPrincipalMinorExpandedIsFalse =
        refl
    ; characteristicDeterminantExpanded =
        false
    ; characteristicDeterminantExpandedIsFalse =
        refl
    }

downCharacteristicPolynomialFiniteStage :
  GL.FactorVec →
  CKMCharacteristicPolynomialFiniteStage
downCharacteristicPolynomialFiniteStage v =
  record
    { characteristicHermitianProduct =
        downHermitianProduct3x3 v
    ; characteristicTraceTerms =
        hermitianTraceTerms (downHermitianProduct3x3 v)
    ; characteristicTraceTermsAreComputed =
        refl
    ; characteristicTraceField =
        rationalQ
    ; characteristicTraceFieldIsRationalQ =
        refl
    ; characteristicPrincipalMinorCarrier =
        CKMHermitianEntrySum3
    ; characteristicPrincipalMinorCarrierIsStagedHermitianSum =
        refl
    ; characteristicDeterminantCarrier =
        CKMHermitianEntrySum3
    ; characteristicDeterminantCarrierIsStagedHermitianSum =
        refl
    ; characteristicPrincipalMinorExpanded =
        false
    ; characteristicPrincipalMinorExpandedIsFalse =
        refl
    ; characteristicDeterminantExpanded =
        false
    ; characteristicDeterminantExpandedIsFalse =
        refl
    }

record CKMExecutableStagedEntryFieldArithmetic : Set₂ where
  field
    stagedArithmeticWitnessVector :
      GL.FactorVec

    stagedArithmeticWitnessVectorIsCanonical :
      stagedArithmeticWitnessVector
      ≡
      canonicalYukawaFNExponentWitnessVector

    upY11MembershipCertificate :
      monomialFieldDecision
        (yukawaEntryToExactFNMonomial
          (upYukawaEntryAt stagedArithmeticWitnessVector matrixIndex1 matrixIndex1))
      ≡
      qAloneSuffices

    downY22GeorgiJarlskogMembershipCertificate :
      monomialFieldDecision
        (yukawaEntryToExactFNMonomial
          (downYukawaEntryAt stagedArithmeticWitnessVector matrixIndex2 matrixIndex2))
      ≡
      qAloneSuffices

    upHermitianProductFinite :
      CKMHermitianProduct3x3

    upHermitianProductFiniteIsComputed :
      upHermitianProductFinite
      ≡
      upHermitianProduct3x3 stagedArithmeticWitnessVector

    downHermitianProductFinite :
      CKMHermitianProduct3x3

    downHermitianProductFiniteIsComputed :
      downHermitianProductFinite
      ≡
      downHermitianProduct3x3 stagedArithmeticWitnessVector

    upCharacteristicPolynomialFinite :
      CKMCharacteristicPolynomialFiniteStage

    upCharacteristicPolynomialFiniteIsComputed :
      Bool

    downCharacteristicPolynomialFinite :
      CKMCharacteristicPolynomialFiniteStage

    downCharacteristicPolynomialFiniteIsComputed :
      Bool

    stagedEntryFieldMembershipCertificatesSupplied :
      Bool

    stagedEntryFieldMembershipCertificatesSuppliedIsTrue :
      stagedEntryFieldMembershipCertificatesSupplied ≡ true

    stagedHermitianProductsComputed :
      Bool

    stagedHermitianProductsComputedIsTrue :
      stagedHermitianProductsComputed ≡ true

    stagedCharacteristicTraceTermsComputed :
      Bool

    stagedCharacteristicTraceTermsComputedIsTrue :
      stagedCharacteristicTraceTermsComputed ≡ true

    physicalYukawaNormalizationPromotedFromStagedArithmetic :
      Bool

    physicalYukawaNormalizationPromotedFromStagedArithmeticIsFalse :
      physicalYukawaNormalizationPromotedFromStagedArithmetic ≡ false

    determinantAndEigenbasisClosurePromotedFromStagedArithmetic :
      Bool

    determinantAndEigenbasisClosurePromotedFromStagedArithmeticIsFalse :
      determinantAndEigenbasisClosurePromotedFromStagedArithmetic ≡ false

    stagedArithmeticBoundary :
      List String

open CKMExecutableStagedEntryFieldArithmetic public

canonicalCKMExecutableStagedEntryFieldArithmetic :
  CKMExecutableStagedEntryFieldArithmetic
canonicalCKMExecutableStagedEntryFieldArithmetic =
  record
    { stagedArithmeticWitnessVector =
        canonicalYukawaFNExponentWitnessVector
    ; stagedArithmeticWitnessVectorIsCanonical =
        refl
    ; upY11MembershipCertificate =
        refl
    ; downY22GeorgiJarlskogMembershipCertificate =
        refl
    ; upHermitianProductFinite =
        upHermitianProduct3x3 canonicalYukawaFNExponentWitnessVector
    ; upHermitianProductFiniteIsComputed =
        refl
    ; downHermitianProductFinite =
        downHermitianProduct3x3 canonicalYukawaFNExponentWitnessVector
    ; downHermitianProductFiniteIsComputed =
        refl
    ; upCharacteristicPolynomialFinite =
        upCharacteristicPolynomialFiniteStage canonicalYukawaFNExponentWitnessVector
    ; upCharacteristicPolynomialFiniteIsComputed =
        true
    ; downCharacteristicPolynomialFinite =
        downCharacteristicPolynomialFiniteStage canonicalYukawaFNExponentWitnessVector
    ; downCharacteristicPolynomialFiniteIsComputed =
        true
    ; stagedEntryFieldMembershipCertificatesSupplied =
        true
    ; stagedEntryFieldMembershipCertificatesSuppliedIsTrue =
        refl
    ; stagedHermitianProductsComputed =
        true
    ; stagedHermitianProductsComputedIsTrue =
        refl
    ; stagedCharacteristicTraceTermsComputed =
        true
    ; stagedCharacteristicTraceTermsComputedIsTrue =
        refl
    ; physicalYukawaNormalizationPromotedFromStagedArithmetic =
        false
    ; physicalYukawaNormalizationPromotedFromStagedArithmeticIsFalse =
        refl
    ; determinantAndEigenbasisClosurePromotedFromStagedArithmetic =
        false
    ; determinantAndEigenbasisClosurePromotedFromStagedArithmeticIsFalse =
        refl
    ; stagedArithmeticBoundary =
        "Staged up/down FN entries have executable rationalQ membership certificates"
        ∷ "Up/down Hermitian products are computed as finite triples of exact FN monomials over the canonical witness vector"
        ∷ "Characteristic trace terms are computed; principal-minor, determinant, splitting-field, and normalized-eigenbasis closure remain staged blockers"
        ∷ "No Higgs-normalized physical Yukawa value, DHR compatibility theorem, or CKM product closure is promoted"
        ∷ []
    }

ckmStagedEntryFieldMembershipCertificatesSupplied :
  stagedEntryFieldMembershipCertificatesSupplied
    canonicalCKMExecutableStagedEntryFieldArithmetic
  ≡
  true
ckmStagedEntryFieldMembershipCertificatesSupplied =
  refl

ckmStagedHermitianProductsComputed :
  stagedHermitianProductsComputed canonicalCKMExecutableStagedEntryFieldArithmetic
  ≡
  true
ckmStagedHermitianProductsComputed =
  refl

ckmStagedArithmeticDoesNotPromotePhysicalYukawa :
  physicalYukawaNormalizationPromotedFromStagedArithmetic
    canonicalCKMExecutableStagedEntryFieldArithmetic
  ≡
  false
ckmStagedArithmeticDoesNotPromotePhysicalYukawa =
  refl

data CKMYukawaSpectralStagingComponent : Set where
  upHermitianProductStageComponent :
    CKMYukawaSpectralStagingComponent
  downHermitianProductStageComponent :
    CKMYukawaSpectralStagingComponent
  upCharacteristicPolynomialStageComponent :
    CKMYukawaSpectralStagingComponent
  downCharacteristicPolynomialStageComponent :
    CKMYukawaSpectralStagingComponent
  upEigenvalueSplittingFieldStageComponent :
    CKMYukawaSpectralStagingComponent
  downEigenvalueSplittingFieldStageComponent :
    CKMYukawaSpectralStagingComponent
  upNormalizedLeftEigenbasisStageComponent :
    CKMYukawaSpectralStagingComponent
  downNormalizedLeftEigenbasisStageComponent :
    CKMYukawaSpectralStagingComponent

canonicalCKMYukawaSpectralStagingComponents :
  List CKMYukawaSpectralStagingComponent
canonicalCKMYukawaSpectralStagingComponents =
  upHermitianProductStageComponent
  ∷ downHermitianProductStageComponent
  ∷ upCharacteristicPolynomialStageComponent
  ∷ downCharacteristicPolynomialStageComponent
  ∷ upEigenvalueSplittingFieldStageComponent
  ∷ downEigenvalueSplittingFieldStageComponent
  ∷ upNormalizedLeftEigenbasisStageComponent
  ∷ downNormalizedLeftEigenbasisStageComponent
  ∷ []

record CKMUpDownHermitianCharacteristicEigenbasisStaging :
  Set₃ where
  field
    stagedFNExponentInventory :
      CKMExactFNExponentCertificateInventory

    executableStagedEntryFieldArithmetic :
      CKMExecutableStagedEntryFieldArithmetic

    spectralStagingComponents :
      List CKMYukawaSpectralStagingComponent

    spectralStagingComponentsAreCanonical :
      spectralStagingComponents
      ≡
      canonicalCKMYukawaSpectralStagingComponents

    upHermitianProductTarget :
      Set

    upHermitianProductTargetIsSelectedFieldSurface :
      upHermitianProductTarget ≡ ⊤

    downHermitianProductTarget :
      Set

    downHermitianProductTargetIsSelectedFieldSurface :
      downHermitianProductTarget ≡ ⊤

    upCharacteristicPolynomialProgress :
      CKMCharacteristicPolynomialProgress

    downCharacteristicPolynomialProgress :
      CKMCharacteristicPolynomialProgress

    upEigenvalueSplittingFieldProgress :
      CKMEigenvalueSplittingFieldProgress

    downEigenvalueSplittingFieldProgress :
      CKMEigenvalueSplittingFieldProgress

    upNormalizedLeftEigenbasisProgress :
      CKMNormalizedLeftEigenbasisProgress

    downNormalizedLeftEigenbasisProgress :
      CKMNormalizedLeftEigenbasisProgress

    hermitianProductsExecutableStaged :
      Bool

    hermitianProductsExecutableStagedIsTrue :
      hermitianProductsExecutableStaged ≡ true

    entryFieldMembershipCertificatesExecutableStaged :
      Bool

    entryFieldMembershipCertificatesExecutableStagedIsTrue :
      entryFieldMembershipCertificatesExecutableStaged ≡ true

    characteristicPolynomialsStaged :
      Bool

    characteristicPolynomialsStagedIsTrue :
      characteristicPolynomialsStaged ≡ true

    normalizedEigenbasisClosurePromoted :
      Bool

    normalizedEigenbasisClosurePromotedIsFalse :
      normalizedEigenbasisClosurePromoted ≡ false

    ckmProductClosureStillMissing :
      CKMArithmeticInputSlot

    ckmProductClosureStillMissingIsCKMProductClosureWitness :
      ckmProductClosureStillMissing
      ≡
      missingCKMProductClosureWitness

    spectralStagingBoundary :
      List String

open CKMUpDownHermitianCharacteristicEigenbasisStaging public

canonicalCKMUpDownHermitianCharacteristicEigenbasisStaging :
  CKMUpDownHermitianCharacteristicEigenbasisStaging
canonicalCKMUpDownHermitianCharacteristicEigenbasisStaging =
  record
    { stagedFNExponentInventory =
        canonicalCKMExactFNExponentCertificateInventory
    ; executableStagedEntryFieldArithmetic =
        canonicalCKMExecutableStagedEntryFieldArithmetic
    ; spectralStagingComponents =
        canonicalCKMYukawaSpectralStagingComponents
    ; spectralStagingComponentsAreCanonical =
        refl
    ; upHermitianProductTarget =
        ⊤
    ; upHermitianProductTargetIsSelectedFieldSurface =
        refl
    ; downHermitianProductTarget =
        ⊤
    ; downHermitianProductTargetIsSelectedFieldSurface =
        refl
    ; upCharacteristicPolynomialProgress =
        canonicalCKMCharacteristicPolynomialProgress
    ; downCharacteristicPolynomialProgress =
        canonicalCKMCharacteristicPolynomialProgress
    ; upEigenvalueSplittingFieldProgress =
        canonicalCKMEigenvalueSplittingFieldProgress
    ; downEigenvalueSplittingFieldProgress =
        canonicalCKMEigenvalueSplittingFieldProgress
    ; upNormalizedLeftEigenbasisProgress =
        canonicalCKMNormalizedLeftEigenbasisProgress
    ; downNormalizedLeftEigenbasisProgress =
        canonicalCKMNormalizedLeftEigenbasisProgress
    ; hermitianProductsExecutableStaged =
        true
    ; hermitianProductsExecutableStagedIsTrue =
        refl
    ; entryFieldMembershipCertificatesExecutableStaged =
        true
    ; entryFieldMembershipCertificatesExecutableStagedIsTrue =
        refl
    ; characteristicPolynomialsStaged =
        true
    ; characteristicPolynomialsStagedIsTrue =
        refl
    ; normalizedEigenbasisClosurePromoted =
        false
    ; normalizedEigenbasisClosurePromotedIsFalse =
        refl
    ; ckmProductClosureStillMissing =
        missingCKMProductClosureWitness
    ; ckmProductClosureStillMissingIsCKMProductClosureWitness =
        refl
    ; spectralStagingBoundary =
        "Staged entry-field membership certificates and up/down Hermitian product terms are executable over the finite FN carrier"
        ∷ "Up/down characteristic, splitting-field, and normalized-left-eigenbasis queues are recorded symmetrically"
        ∷ "The characteristic trace terms are computed, while principal-minor/determinant expansion does not prove normalized eigenbasis field closure or CKM product closure"
        ∷ "The next exact l1 handoff blocker remains missingCKMProductClosureWitness"
        ∷ []
    }

ckmFactorVecToYukawaMapSurfaceIsSupplied :
  factorVecToYukawaEntryMapSupplied
    canonicalCKMFactorVecToYukawaEntryMapSurface
  ≡
  true
ckmFactorVecToYukawaMapSurfaceIsSupplied =
  refl

ckmFactorVecToYukawaMapDoesNotPromoteNormalization :
  physicalYukawaNormalizationPromoted
    canonicalCKMFactorVecToYukawaEntryMapSurface
  ≡
  false
ckmFactorVecToYukawaMapDoesNotPromoteNormalization =
  refl

ckmExactFNExponentInventoryDoesNotPromoteTexture :
  exactTexturePromoted canonicalCKMExactFNExponentCertificateInventory
  ≡
  false
ckmExactFNExponentInventoryDoesNotPromoteTexture =
  refl

ckmUpDownSpectralStagingKeepsCKMProductClosureMissing :
  ckmProductClosureStillMissing
    canonicalCKMUpDownHermitianCharacteristicEigenbasisStaging
  ≡
  missingCKMProductClosureWitness
ckmUpDownSpectralStagingKeepsCKMProductClosureMissing =
  refl

------------------------------------------------------------------------
-- Exact staged entry-field membership and Hermitian product arithmetic.

yukawaEntryCoefficientNumerator :
  YukawaEntryCarrier →
  Nat
yukawaEntryCoefficientNumerator (stagedUpFNYukawaEntry slot exponent) =
  1
yukawaEntryCoefficientNumerator
  (stagedDownFNYukawaEntry slot exponent numerator denominator positive gjSocket) =
  numerator

yukawaEntryCoefficientDenominator :
  YukawaEntryCarrier →
  Nat
yukawaEntryCoefficientDenominator (stagedUpFNYukawaEntry slot exponent) =
  1
yukawaEntryCoefficientDenominator
  (stagedDownFNYukawaEntry slot exponent numerator denominator positive gjSocket) =
  denominator

yukawaEntryCoefficientPositive :
  YukawaEntryCarrier →
  Bool
yukawaEntryCoefficientPositive (stagedUpFNYukawaEntry slot exponent) =
  true
yukawaEntryCoefficientPositive
  (stagedDownFNYukawaEntry slot exponent numerator denominator positive gjSocket) =
  positive

upEntryFieldMembershipExponentCertificate :
  (v : GL.FactorVec) →
  (slot : YukawaMatrix3x3EntrySlot) →
  yukawaEntryFNExponent (factorVecToStagedUpYukawaEntryMap v slot)
  ≡
  upYukawaEntryFNExponent slot v
upEntryFieldMembershipExponentCertificate v slot =
  refl

downEntryFieldMembershipExponentCertificate :
  (v : GL.FactorVec) →
  (slot : YukawaMatrix3x3EntrySlot) →
  yukawaEntryFNExponent (factorVecToStagedDownYukawaEntryMap v slot)
  ≡
  downYukawaEntryFNExponent slot v
downEntryFieldMembershipExponentCertificate v missingY11 =
  refl
downEntryFieldMembershipExponentCertificate v missingY12 =
  refl
downEntryFieldMembershipExponentCertificate v missingY13 =
  refl
downEntryFieldMembershipExponentCertificate v missingY21 =
  refl
downEntryFieldMembershipExponentCertificate v missingY22 =
  refl
downEntryFieldMembershipExponentCertificate v missingY23 =
  refl
downEntryFieldMembershipExponentCertificate v missingY31 =
  refl
downEntryFieldMembershipExponentCertificate v missingY32 =
  refl
downEntryFieldMembershipExponentCertificate v missingY33 =
  refl

downY22EntryFieldMembershipRecordsGeorgiJarlskog :
  (v : GL.FactorVec) →
  yukawaEntryCoefficientNumerator
    (factorVecToStagedDownYukawaEntryMap v missingY22)
  ≡
  3
downY22EntryFieldMembershipRecordsGeorgiJarlskog v =
  refl

downY22EntryFieldMembershipRecordsNegativeSign :
  (v : GL.FactorVec) →
  yukawaEntryCoefficientPositive
    (factorVecToStagedDownYukawaEntryMap v missingY22)
  ≡
  false
downY22EntryFieldMembershipRecordsNegativeSign v =
  refl

record CKMEntryFieldMembershipCertificateReceipt : Setω where
  field
    priorDownFactorVecMapProgress :
      CKMDownFactorVecToYukawaEntryMapProgress

    priorDownMapNextInputIsEntryFieldMembership :
      nextMissingArithmeticInputAfterDownFactorVecMap priorDownFactorVecMapProgress
      ≡
      missingEntryFieldMembershipCertificates

    upEntryMembershipCertificate :
      (v : GL.FactorVec) →
      (slot : YukawaMatrix3x3EntrySlot) →
      yukawaEntryFNExponent (factorVecToStagedUpYukawaEntryMap v slot)
      ≡
      upYukawaEntryFNExponent slot v

    downEntryMembershipCertificate :
      (v : GL.FactorVec) →
      (slot : YukawaMatrix3x3EntrySlot) →
      yukawaEntryFNExponent (factorVecToStagedDownYukawaEntryMap v slot)
      ≡
      downYukawaEntryFNExponent slot v

    downY22GeorgiJarlskogNumeratorCertificate :
      (v : GL.FactorVec) →
      yukawaEntryCoefficientNumerator
        (factorVecToStagedDownYukawaEntryMap v missingY22)
      ≡
      3

    downY22GeorgiJarlskogNegativeSignCertificate :
      (v : GL.FactorVec) →
      yukawaEntryCoefficientPositive
        (factorVecToStagedDownYukawaEntryMap v missingY22)
      ≡
      false

    entryFieldMembershipCertificatesSupplied :
      Bool

    entryFieldMembershipCertificatesSuppliedIsTrue :
      entryFieldMembershipCertificatesSupplied ≡ true

    physicalYukawaNormalizationPromoted :
      Bool

    physicalYukawaNormalizationPromotedIsFalse :
      physicalYukawaNormalizationPromoted ≡ false

    remainingMissingArithmeticInputsAfterEntryMembership :
      List CKMArithmeticInputSlot

    remainingMissingArithmeticInputsAfterEntryMembershipAreCanonical :
      remainingMissingArithmeticInputsAfterEntryMembership
      ≡
      canonicalCKMArithmeticInputSlotsAfterEntryFieldMembershipSupply

    nextMissingArithmeticInputAfterEntryMembership :
      CKMArithmeticInputSlot

    nextMissingArithmeticInputAfterEntryMembershipIsHermitianProductMatrices :
      nextMissingArithmeticInputAfterEntryMembership
      ≡
      missingHermitianProductMatrices

    certificateReceiptBoundary :
      List String

open CKMEntryFieldMembershipCertificateReceipt public

canonicalCKMEntryFieldMembershipCertificateReceipt :
  CKMEntryFieldMembershipCertificateReceipt
canonicalCKMEntryFieldMembershipCertificateReceipt =
  record
    { priorDownFactorVecMapProgress =
        canonicalCKMDownFactorVecToYukawaEntryMapProgress
    ; priorDownMapNextInputIsEntryFieldMembership =
        refl
    ; upEntryMembershipCertificate =
        upEntryFieldMembershipExponentCertificate
    ; downEntryMembershipCertificate =
        downEntryFieldMembershipExponentCertificate
    ; downY22GeorgiJarlskogNumeratorCertificate =
        downY22EntryFieldMembershipRecordsGeorgiJarlskog
    ; downY22GeorgiJarlskogNegativeSignCertificate =
        downY22EntryFieldMembershipRecordsNegativeSign
    ; entryFieldMembershipCertificatesSupplied =
        true
    ; entryFieldMembershipCertificatesSuppliedIsTrue =
        refl
    ; physicalYukawaNormalizationPromoted =
        false
    ; physicalYukawaNormalizationPromotedIsFalse =
        refl
    ; remainingMissingArithmeticInputsAfterEntryMembership =
        canonicalCKMArithmeticInputSlotsAfterEntryFieldMembershipSupply
    ; remainingMissingArithmeticInputsAfterEntryMembershipAreCanonical =
        refl
    ; nextMissingArithmeticInputAfterEntryMembership =
        missingHermitianProductMatrices
    ; nextMissingArithmeticInputAfterEntryMembershipIsHermitianProductMatrices =
        refl
    ; certificateReceiptBoundary =
        "All up/down staged FN entries have executable exponent-membership certificates over the staged Nat entry field"
        ∷ "The down y22 certificate records the Georgi-Jarlskog coefficient 3 and negative sign"
        ∷ "This discharges the local staged-entry membership blocker and advances the arithmetic queue to Hermitian products"
        ∷ "Physical Higgs normalization remains blocked by vHiggsAdapter4Boundary"
        ∷ []
    }

data YukawaHermitianSector : Set where
  upHermitianSector :
    YukawaHermitianSector

  downHermitianSector :
    YukawaHermitianSector

upYukawaSlot :
  UpYukawaGenerationIndex →
  UpYukawaGenerationIndex →
  YukawaMatrix3x3EntrySlot
upYukawaSlot upGen1 upGen1 =
  missingY11
upYukawaSlot upGen1 upGen2 =
  missingY12
upYukawaSlot upGen1 upGen3 =
  missingY13
upYukawaSlot upGen2 upGen1 =
  missingY21
upYukawaSlot upGen2 upGen2 =
  missingY22
upYukawaSlot upGen2 upGen3 =
  missingY23
upYukawaSlot upGen3 upGen1 =
  missingY31
upYukawaSlot upGen3 upGen2 =
  missingY32
upYukawaSlot upGen3 upGen3 =
  missingY33

downYukawaSlot :
  DownYukawaGenerationIndex →
  DownYukawaGenerationIndex →
  YukawaMatrix3x3EntrySlot
downYukawaSlot downGen1 downGen1 =
  missingY11
downYukawaSlot downGen1 downGen2 =
  missingY12
downYukawaSlot downGen1 downGen3 =
  missingY13
downYukawaSlot downGen2 downGen1 =
  missingY21
downYukawaSlot downGen2 downGen2 =
  missingY22
downYukawaSlot downGen2 downGen3 =
  missingY23
downYukawaSlot downGen3 downGen1 =
  missingY31
downYukawaSlot downGen3 downGen2 =
  missingY32
downYukawaSlot downGen3 downGen3 =
  missingY33

record YukawaHermitianProductEntry : Set where
  field
    column1ExponentProduct :
      Nat

    column2ExponentProduct :
      Nat

    column3ExponentProduct :
      Nat

    summandCount :
      Nat

    summandCountIsThree :
      summandCount ≡ threeGenerations

open YukawaHermitianProductEntry public

upHermitianProductEntry :
  UpYukawaGenerationIndex →
  UpYukawaGenerationIndex →
  GL.FactorVec →
  YukawaHermitianProductEntry
upHermitianProductEntry row column v =
  record
    { column1ExponentProduct =
        upYukawaEntryFNExponent (upYukawaSlot row upGen1) v
        +
        upYukawaEntryFNExponent (upYukawaSlot column upGen1) v
    ; column2ExponentProduct =
        upYukawaEntryFNExponent (upYukawaSlot row upGen2) v
        +
        upYukawaEntryFNExponent (upYukawaSlot column upGen2) v
    ; column3ExponentProduct =
        upYukawaEntryFNExponent (upYukawaSlot row upGen3) v
        +
        upYukawaEntryFNExponent (upYukawaSlot column upGen3) v
    ; summandCount =
        threeGenerations
    ; summandCountIsThree =
        refl
    }

downHermitianProductEntry :
  DownYukawaGenerationIndex →
  DownYukawaGenerationIndex →
  GL.FactorVec →
  YukawaHermitianProductEntry
downHermitianProductEntry row column v =
  record
    { column1ExponentProduct =
        downYukawaEntryFNExponent (downYukawaSlot row downGen1) v
        +
        downYukawaEntryFNExponent (downYukawaSlot column downGen1) v
    ; column2ExponentProduct =
        downYukawaEntryFNExponent (downYukawaSlot row downGen2) v
        +
        downYukawaEntryFNExponent (downYukawaSlot column downGen2) v
    ; column3ExponentProduct =
        downYukawaEntryFNExponent (downYukawaSlot row downGen3) v
        +
        downYukawaEntryFNExponent (downYukawaSlot column downGen3) v
    ; summandCount =
        threeGenerations
    ; summandCountIsThree =
        refl
    }

record YukawaHermitianProduct3x3Matrix : Set where
  field
    hermitianSector :
      YukawaHermitianSector

    h11 :
      YukawaHermitianProductEntry

    h12 :
      YukawaHermitianProductEntry

    h13 :
      YukawaHermitianProductEntry

    h21 :
      YukawaHermitianProductEntry

    h22 :
      YukawaHermitianProductEntry

    h23 :
      YukawaHermitianProductEntry

    h31 :
      YukawaHermitianProductEntry

    h32 :
      YukawaHermitianProductEntry

    h33 :
      YukawaHermitianProductEntry

open YukawaHermitianProduct3x3Matrix public

factorVecToUpHermitianProduct3x3Matrix :
  GL.FactorVec →
  YukawaHermitianProduct3x3Matrix
factorVecToUpHermitianProduct3x3Matrix v =
  record
    { hermitianSector =
        upHermitianSector
    ; h11 =
        upHermitianProductEntry upGen1 upGen1 v
    ; h12 =
        upHermitianProductEntry upGen1 upGen2 v
    ; h13 =
        upHermitianProductEntry upGen1 upGen3 v
    ; h21 =
        upHermitianProductEntry upGen2 upGen1 v
    ; h22 =
        upHermitianProductEntry upGen2 upGen2 v
    ; h23 =
        upHermitianProductEntry upGen2 upGen3 v
    ; h31 =
        upHermitianProductEntry upGen3 upGen1 v
    ; h32 =
        upHermitianProductEntry upGen3 upGen2 v
    ; h33 =
        upHermitianProductEntry upGen3 upGen3 v
    }

factorVecToDownHermitianProduct3x3Matrix :
  GL.FactorVec →
  YukawaHermitianProduct3x3Matrix
factorVecToDownHermitianProduct3x3Matrix v =
  record
    { hermitianSector =
        downHermitianSector
    ; h11 =
        downHermitianProductEntry downGen1 downGen1 v
    ; h12 =
        downHermitianProductEntry downGen1 downGen2 v
    ; h13 =
        downHermitianProductEntry downGen1 downGen3 v
    ; h21 =
        downHermitianProductEntry downGen2 downGen1 v
    ; h22 =
        downHermitianProductEntry downGen2 downGen2 v
    ; h23 =
        downHermitianProductEntry downGen2 downGen3 v
    ; h31 =
        downHermitianProductEntry downGen3 downGen1 v
    ; h32 =
        downHermitianProductEntry downGen3 downGen2 v
    ; h33 =
        downHermitianProductEntry downGen3 downGen3 v
    }

record CKMHermitianProductMatrixReceipt : Setω where
  field
    priorEntryMembershipReceipt :
      CKMEntryFieldMembershipCertificateReceipt

    priorEntryMembershipAdvancesToHermitianProducts :
      nextMissingArithmeticInputAfterEntryMembership priorEntryMembershipReceipt
      ≡
      missingHermitianProductMatrices

    upHermitianProductMatrix :
      GL.FactorVec →
      YukawaHermitianProduct3x3Matrix

    upHermitianProductMatrixIsCanonical :
      upHermitianProductMatrix
      ≡
      factorVecToUpHermitianProduct3x3Matrix

    downHermitianProductMatrix :
      GL.FactorVec →
      YukawaHermitianProduct3x3Matrix

    downHermitianProductMatrixIsCanonical :
      downHermitianProductMatrix
      ≡
      factorVecToDownHermitianProduct3x3Matrix

    hermitianProductMatricesSupplied :
      Bool

    hermitianProductMatricesSuppliedIsTrue :
      hermitianProductMatricesSupplied ≡ true

    remainingMissingArithmeticInputsAfterHermitianProducts :
      List CKMArithmeticInputSlot

    remainingMissingArithmeticInputsAfterHermitianProductsAreCanonical :
      remainingMissingArithmeticInputsAfterHermitianProducts
      ≡
      canonicalCKMArithmeticInputSlotsAfterHermitianProductSupply

    nextMissingArithmeticInputAfterHermitianProducts :
      CKMArithmeticInputSlot

    nextMissingArithmeticInputAfterHermitianProductsIsCharacteristicPolynomials :
      nextMissingArithmeticInputAfterHermitianProducts
      ≡
      missingCharacteristicPolynomials

    hermitianProductBoundary :
      List String

open CKMHermitianProductMatrixReceipt public

canonicalCKMHermitianProductMatrixReceipt :
  CKMHermitianProductMatrixReceipt
canonicalCKMHermitianProductMatrixReceipt =
  record
    { priorEntryMembershipReceipt =
        canonicalCKMEntryFieldMembershipCertificateReceipt
    ; priorEntryMembershipAdvancesToHermitianProducts =
        refl
    ; upHermitianProductMatrix =
        factorVecToUpHermitianProduct3x3Matrix
    ; upHermitianProductMatrixIsCanonical =
        refl
    ; downHermitianProductMatrix =
        factorVecToDownHermitianProduct3x3Matrix
    ; downHermitianProductMatrixIsCanonical =
        refl
    ; hermitianProductMatricesSupplied =
        true
    ; hermitianProductMatricesSuppliedIsTrue =
        refl
    ; remainingMissingArithmeticInputsAfterHermitianProducts =
        canonicalCKMArithmeticInputSlotsAfterHermitianProductSupply
    ; remainingMissingArithmeticInputsAfterHermitianProductsAreCanonical =
        refl
    ; nextMissingArithmeticInputAfterHermitianProducts =
        missingCharacteristicPolynomials
    ; nextMissingArithmeticInputAfterHermitianProductsIsCharacteristicPolynomials =
        refl
    ; hermitianProductBoundary =
        "The staged Hermitian products Yu Yu^dagger and Yd Yd^dagger are executable as three-summand FN-exponent matrices"
        ∷ "Each product term uses epsilon exponent addition, recording the exact exponent arithmetic available in the repo carrier"
        ∷ "The next arithmetic blocker is concrete characteristic-polynomial coefficients over the selected field"
        ∷ []
    }

record CKMSymbolicYukawaSpectralArithmeticReceipt : Setω where
  field
    hermitianProductReceipt :
      CKMHermitianProductMatrixReceipt

    priorHermitianProductsAdvanceToCharacteristicPolynomials :
      nextMissingArithmeticInputAfterHermitianProducts hermitianProductReceipt
      ≡
      missingCharacteristicPolynomials

    upCharacteristicPolynomialProgressReceipt :
      CKMCharacteristicPolynomialProgress

    downCharacteristicPolynomialProgressReceipt :
      CKMCharacteristicPolynomialProgress

    upSplittingFieldProgressReceipt :
      CKMEigenvalueSplittingFieldProgress

    downSplittingFieldProgressReceipt :
      CKMEigenvalueSplittingFieldProgress

    upNormalizedLeftEigenbasisProgressReceipt :
      CKMNormalizedLeftEigenbasisProgress

    downNormalizedLeftEigenbasisProgressReceipt :
      CKMNormalizedLeftEigenbasisProgress

    symbolicUuCarrier :
      Set

    symbolicUuCarrierIsMatterMixingMatrix :
      symbolicUuCarrier ≡ Matter.MixingMatrix

    symbolicUdCarrier :
      Set

    symbolicUdCarrierIsMatterMixingMatrix :
      symbolicUdCarrier ≡ Matter.MixingMatrix

    ckmProductCarrier :
      Set

    ckmProductCarrierIsMatterMixingMatrix :
      ckmProductCarrier ≡ Matter.MixingMatrix

    ckmProductFormula :
      String

    ckmProductFormula-v :
      ckmProductFormula ≡ "V_CKM = U_u^dagger * U_d"

    ckmProductClosureWitnessSupplied :
      Bool

    ckmProductClosureWitnessSuppliedIsFalse :
      ckmProductClosureWitnessSupplied ≡ false

    firstRemainingArithmeticBlocker :
      CKMArithmeticInputSlot

    firstRemainingArithmeticBlockerIsCKMProductClosureWitness :
      firstRemainingArithmeticBlocker ≡ missingCKMProductClosureWitness

    spectralArithmeticBoundary :
      List String

open CKMSymbolicYukawaSpectralArithmeticReceipt public

canonicalCKMSymbolicYukawaSpectralArithmeticReceipt :
  CKMSymbolicYukawaSpectralArithmeticReceipt
canonicalCKMSymbolicYukawaSpectralArithmeticReceipt =
  record
    { hermitianProductReceipt =
        canonicalCKMHermitianProductMatrixReceipt
    ; priorHermitianProductsAdvanceToCharacteristicPolynomials =
        refl
    ; upCharacteristicPolynomialProgressReceipt =
        canonicalCKMCharacteristicPolynomialProgress
    ; downCharacteristicPolynomialProgressReceipt =
        canonicalCKMCharacteristicPolynomialProgress
    ; upSplittingFieldProgressReceipt =
        canonicalCKMEigenvalueSplittingFieldProgress
    ; downSplittingFieldProgressReceipt =
        canonicalCKMEigenvalueSplittingFieldProgress
    ; upNormalizedLeftEigenbasisProgressReceipt =
        canonicalCKMNormalizedLeftEigenbasisProgress
    ; downNormalizedLeftEigenbasisProgressReceipt =
        canonicalCKMNormalizedLeftEigenbasisProgress
    ; symbolicUuCarrier =
        Matter.MixingMatrix
    ; symbolicUuCarrierIsMatterMixingMatrix =
        refl
    ; symbolicUdCarrier =
        Matter.MixingMatrix
    ; symbolicUdCarrierIsMatterMixingMatrix =
        refl
    ; ckmProductCarrier =
        Matter.MixingMatrix
    ; ckmProductCarrierIsMatterMixingMatrix =
        refl
    ; ckmProductFormula =
        "V_CKM = U_u^dagger * U_d"
    ; ckmProductFormula-v =
        refl
    ; ckmProductClosureWitnessSupplied =
        false
    ; ckmProductClosureWitnessSuppliedIsFalse =
        refl
    ; firstRemainingArithmeticBlocker =
        missingCKMProductClosureWitness
    ; firstRemainingArithmeticBlockerIsCKMProductClosureWitness =
        refl
    ; spectralArithmeticBoundary =
        "Hermitian products, characteristic-polynomial queue, splitting-field queue, and normalized U_u/U_d target surfaces are staged symmetrically"
        ∷ "The CKM product is typed through Matter.MixingMatrix using V_CKM = U_u^dagger * U_d"
        ∷ "The product-closure witness and unitarity residual are still not inhabited"
        ∷ []
    }

ckmEntryFieldMembershipCertificatesNowSupplied :
  entryFieldMembershipCertificatesSupplied
    canonicalCKMEntryFieldMembershipCertificateReceipt
  ≡
  true
ckmEntryFieldMembershipCertificatesNowSupplied =
  refl

ckmHermitianProductsNowSupplied :
  hermitianProductMatricesSupplied canonicalCKMHermitianProductMatrixReceipt
  ≡
  true
ckmHermitianProductsNowSupplied =
  refl

ckmSymbolicSpectralArithmeticStillBlockedAtProductClosure :
  firstRemainingArithmeticBlocker
    canonicalCKMSymbolicYukawaSpectralArithmeticReceipt
  ≡
  missingCKMProductClosureWitness
ckmSymbolicSpectralArithmeticStillBlockedAtProductClosure =
  refl

canonicalCKMArithmeticInputSlotsAfterMatterMixingMatrixProductAttempt :
  List CKMArithmeticInputSlot
canonicalCKMArithmeticInputSlotsAfterMatterMixingMatrixProductAttempt =
  missingUnitarityResidualWitness
  ∷ []

data CKMMatterMixingMatrixProductAttemptComponent : Set where
  matterMixingMatrixCarrierForUuComponent :
    CKMMatterMixingMatrixProductAttemptComponent

  matterMixingMatrixCarrierForUdComponent :
    CKMMatterMixingMatrixProductAttemptComponent

  matterMixingMatrixCarrierForUuDaggerUdComponent :
    CKMMatterMixingMatrixProductAttemptComponent

  noConcreteNormalizedUuMatrixTermComponent :
    CKMMatterMixingMatrixProductAttemptComponent

  noConcreteNormalizedUdMatrixTermComponent :
    CKMMatterMixingMatrixProductAttemptComponent

  unitarityResidualStillRequiresEntrywiseMatrixLawComponent :
    CKMMatterMixingMatrixProductAttemptComponent

canonicalCKMMatterMixingMatrixProductAttemptComponents :
  List CKMMatterMixingMatrixProductAttemptComponent
canonicalCKMMatterMixingMatrixProductAttemptComponents =
  matterMixingMatrixCarrierForUuComponent
  ∷ matterMixingMatrixCarrierForUdComponent
  ∷ matterMixingMatrixCarrierForUuDaggerUdComponent
  ∷ noConcreteNormalizedUuMatrixTermComponent
  ∷ noConcreteNormalizedUdMatrixTermComponent
  ∷ unitarityResidualStillRequiresEntrywiseMatrixLawComponent
  ∷ []

record CKMMatterMixingMatrixProductClosureAttemptReceipt : Setω where
  field
    priorSymbolicSpectralArithmetic :
      CKMSymbolicYukawaSpectralArithmeticReceipt

    priorSymbolicSpectralArithmeticBlocksAtProductClosure :
      firstRemainingArithmeticBlocker priorSymbolicSpectralArithmetic
      ≡
      missingCKMProductClosureWitness

    productAttemptComponents :
      List CKMMatterMixingMatrixProductAttemptComponent

    productAttemptComponentsAreCanonical :
      productAttemptComponents
      ≡
      canonicalCKMMatterMixingMatrixProductAttemptComponents

    normalizedUuCarrier :
      Set

    normalizedUuCarrierIsMatterMixingMatrix :
      normalizedUuCarrier ≡ Matter.MixingMatrix

    normalizedUdCarrier :
      Set

    normalizedUdCarrierIsMatterMixingMatrix :
      normalizedUdCarrier ≡ Matter.MixingMatrix

    ckmProductCarrier :
      Set

    ckmProductCarrierIsMatterMixingMatrix :
      ckmProductCarrier ≡ Matter.MixingMatrix

    ckmProductFormula :
      String

    ckmProductFormula-v :
      ckmProductFormula ≡ "V_CKM = U_u^dagger * U_d"

    concreteNormalizedUuMatrixTermSupplied :
      Bool

    concreteNormalizedUuMatrixTermSuppliedIsFalse :
      concreteNormalizedUuMatrixTermSupplied ≡ false

    concreteNormalizedUdMatrixTermSupplied :
      Bool

    concreteNormalizedUdMatrixTermSuppliedIsFalse :
      concreteNormalizedUdMatrixTermSupplied ≡ false

    ckmProductClosureWitnessSupplied :
      Bool

    ckmProductClosureWitnessSuppliedIsFalse :
      ckmProductClosureWitnessSupplied ≡ false

    ckmProductClosureAttemptFailClosed :
      Bool

    ckmProductClosureAttemptFailClosedIsTrue :
      ckmProductClosureAttemptFailClosed ≡ true

    remainingArithmeticInputsAfterProductAttempt :
      List CKMArithmeticInputSlot

    remainingArithmeticInputsAfterProductAttemptAreCanonical :
      remainingArithmeticInputsAfterProductAttempt
      ≡
      canonicalCKMArithmeticInputSlotsAfterMatterMixingMatrixProductAttempt

    nextArithmeticBlockerAfterProductAttempt :
      CKMArithmeticInputSlot

    nextArithmeticBlockerAfterProductAttemptIsUnitarityResidual :
      nextArithmeticBlockerAfterProductAttempt
      ≡
      missingUnitarityResidualWitness

    unitarityResidualWitnessSupplied :
      Bool

    unitarityResidualWitnessSuppliedIsFalse :
      unitarityResidualWitnessSupplied ≡ false

    productAttemptBoundary :
      List String

open CKMMatterMixingMatrixProductClosureAttemptReceipt public

canonicalCKMMatterMixingMatrixProductClosureAttemptReceipt :
  CKMMatterMixingMatrixProductClosureAttemptReceipt
canonicalCKMMatterMixingMatrixProductClosureAttemptReceipt =
  record
    { priorSymbolicSpectralArithmetic =
        canonicalCKMSymbolicYukawaSpectralArithmeticReceipt
    ; priorSymbolicSpectralArithmeticBlocksAtProductClosure =
        refl
    ; productAttemptComponents =
        canonicalCKMMatterMixingMatrixProductAttemptComponents
    ; productAttemptComponentsAreCanonical =
        refl
    ; normalizedUuCarrier =
        Matter.MixingMatrix
    ; normalizedUuCarrierIsMatterMixingMatrix =
        refl
    ; normalizedUdCarrier =
        Matter.MixingMatrix
    ; normalizedUdCarrierIsMatterMixingMatrix =
        refl
    ; ckmProductCarrier =
        Matter.MixingMatrix
    ; ckmProductCarrierIsMatterMixingMatrix =
        refl
    ; ckmProductFormula =
        "V_CKM = U_u^dagger * U_d"
    ; ckmProductFormula-v =
        refl
    ; concreteNormalizedUuMatrixTermSupplied =
        false
    ; concreteNormalizedUuMatrixTermSuppliedIsFalse =
        refl
    ; concreteNormalizedUdMatrixTermSupplied =
        false
    ; concreteNormalizedUdMatrixTermSuppliedIsFalse =
        refl
    ; ckmProductClosureWitnessSupplied =
        false
    ; ckmProductClosureWitnessSuppliedIsFalse =
        refl
    ; ckmProductClosureAttemptFailClosed =
        true
    ; ckmProductClosureAttemptFailClosedIsTrue =
        refl
    ; remainingArithmeticInputsAfterProductAttempt =
        canonicalCKMArithmeticInputSlotsAfterMatterMixingMatrixProductAttempt
    ; remainingArithmeticInputsAfterProductAttemptAreCanonical =
        refl
    ; nextArithmeticBlockerAfterProductAttempt =
        missingUnitarityResidualWitness
    ; nextArithmeticBlockerAfterProductAttemptIsUnitarityResidual =
        refl
    ; unitarityResidualWitnessSupplied =
        false
    ; unitarityResidualWitnessSuppliedIsFalse =
        refl
    ; productAttemptBoundary =
        "The CKM product attempt uses the repo-native Matter.MixingMatrix carrier for U_u, U_d, and V_CKM"
        ∷ "No separate CKMProductMatrix carrier is introduced"
        ∷ "No concrete normalized U_u or U_d matrix term is available behind the opaque Matter.MixingMatrix target"
        ∷ "The product closure attempt is therefore fail-closed and does not inhabit missingCKMProductClosureWitness"
        ∷ "The next arithmetic proof obligation is the unitarity residual witness V V^dagger = I, which is still not supplied"
        ∷ []
    }

ckmMatterMixingMatrixProductAttemptUsesMatterMixingMatrix :
  ckmProductCarrier
    canonicalCKMMatterMixingMatrixProductClosureAttemptReceipt
  ≡
  Matter.MixingMatrix
ckmMatterMixingMatrixProductAttemptUsesMatterMixingMatrix =
  refl

ckmMatterMixingMatrixProductAttemptIsFailClosed :
  ckmProductClosureAttemptFailClosed
    canonicalCKMMatterMixingMatrixProductClosureAttemptReceipt
  ≡
  true
ckmMatterMixingMatrixProductAttemptIsFailClosed =
  refl

ckmMatterMixingMatrixProductAttemptAdvancesToUnitarityResidual :
  nextArithmeticBlockerAfterProductAttempt
    canonicalCKMMatterMixingMatrixProductClosureAttemptReceipt
  ≡
  missingUnitarityResidualWitness
ckmMatterMixingMatrixProductAttemptAdvancesToUnitarityResidual =
  refl

ckmMatterMixingMatrixProductAttemptKeepsUnitarityResidualMissing :
  unitarityResidualWitnessSupplied
    canonicalCKMMatterMixingMatrixProductClosureAttemptReceipt
  ≡
  false
ckmMatterMixingMatrixProductAttemptKeepsUnitarityResidualMissing =
  refl

------------------------------------------------------------------------
-- Concrete Matter.MixingMatrix product closure witness.
--
-- Matter.MixingMatrix now exposes a concrete 3x3 Gaussian-rational entry
-- record.  The finite product closed here is exactly the available staged
-- product: the leading up-sector diagonalizer is the identity, so
-- U_u^dagger * U_d computes to the concrete Wolfenstein datum by definitional
-- equality.  This is not a proof of the exact CKM unitarity residual
-- V * V^dagger = I.

data CKMMatterMixingMatrixConcreteProductClosureStatus : Set where
  concreteLeftIdentityWolfensteinProductClosed :
    CKMMatterMixingMatrixConcreteProductClosureStatus

data CKMMatterMixingMatrixConcreteProductClosureComponent : Set where
  matterMixingMatrixEntryRecordAvailableComponent :
    CKMMatterMixingMatrixConcreteProductClosureComponent

  matterMixingMatrixGaussianRationalEntriesAvailableComponent :
    CKMMatterMixingMatrixConcreteProductClosureComponent

  uuDaggerIdentityMatrixAvailableComponent :
    CKMMatterMixingMatrixConcreteProductClosureComponent

  udWolfensteinMatrixAvailableComponent :
    CKMMatterMixingMatrixConcreteProductClosureComponent

  finiteLeftIdentityProductWitnessComponent :
    CKMMatterMixingMatrixConcreteProductClosureComponent

  exactUnitarityResidualStillOpenComponent :
    CKMMatterMixingMatrixConcreteProductClosureComponent

canonicalCKMMatterMixingMatrixConcreteProductClosureComponents :
  List CKMMatterMixingMatrixConcreteProductClosureComponent
canonicalCKMMatterMixingMatrixConcreteProductClosureComponents =
  matterMixingMatrixEntryRecordAvailableComponent
  ∷ matterMixingMatrixGaussianRationalEntriesAvailableComponent
  ∷ uuDaggerIdentityMatrixAvailableComponent
  ∷ udWolfensteinMatrixAvailableComponent
  ∷ finiteLeftIdentityProductWitnessComponent
  ∷ exactUnitarityResidualStillOpenComponent
  ∷ []

record CKMMatterMixingMatrixConcreteProductClosureWitness : Setω where
  field
    status :
      CKMMatterMixingMatrixConcreteProductClosureStatus

    components :
      List CKMMatterMixingMatrixConcreteProductClosureComponent

    componentsAreCanonical :
      components
      ≡
      canonicalCKMMatterMixingMatrixConcreteProductClosureComponents

    uuDaggerMatrix :
      Matter.MixingMatrix

    uuDaggerMatrixIsIdentity :
      uuDaggerMatrix
      ≡
      Matter.identityMixingMatrix

    udMatrix :
      Matter.MixingMatrix

    udMatrixIsCanonicalWolfenstein :
      udMatrix
      ≡
      Matter.canonicalWolfensteinMixingMatrix

    productMatrix :
      Matter.MixingMatrix

    productMatrixIsLeftIdentityProduct :
      productMatrix
      ≡
      Matter.leftIdentityMixingProduct udMatrix

    finiteProductClosureWitness :
      productMatrix
      ≡
      udMatrix

    vudEntry :
      Matter.v11 productMatrix
      ≡
      Matter.mixingGaussianRationalDatum
        Matter.fortyNineFiftiethsMixingSignedRationalDatum
        Matter.zeroMixingSignedRationalDatum

    vcdEntry :
      Matter.v21 productMatrix
      ≡
      Matter.mixingGaussianRationalDatum
        Matter.minusOneFifthMixingSignedRationalDatum
        Matter.zeroMixingSignedRationalDatum

    vcsEntry :
      Matter.v22 productMatrix
      ≡
      Matter.mixingGaussianRationalDatum
        Matter.fortyNineFiftiethsMixingSignedRationalDatum
        Matter.zeroMixingSignedRationalDatum

    vtdEntry :
      Matter.v31 productMatrix
      ≡
      Matter.vtdWolfensteinMixingGaussianDatum

    vtsEntry :
      Matter.v32 productMatrix
      ≡
      Matter.mixingGaussianRationalDatum
        Matter.minusOneTwentyFifthMixingSignedRationalDatum
        Matter.zeroMixingSignedRationalDatum

    matterMixingMatrixEntryProjectionSupplied :
      Bool

    matterMixingMatrixEntryProjectionSuppliedIsTrue :
      matterMixingMatrixEntryProjectionSupplied ≡ true

    matterMixingMatrixProductClosureWitnessSupplied :
      Bool

    matterMixingMatrixProductClosureWitnessSuppliedIsTrue :
      matterMixingMatrixProductClosureWitnessSupplied ≡ true

    exactUnitarityResidualWitnessSupplied :
      Bool

    exactUnitarityResidualWitnessSuppliedIsFalse :
      exactUnitarityResidualWitnessSupplied ≡ false

    exactJarlskogTheoremPromoted :
      Bool

    exactJarlskogTheoremPromotedIsFalse :
      exactJarlskogTheoremPromoted ≡ false

    nextArithmeticBlockerAfterConcreteProduct :
      CKMArithmeticInputSlot

    nextArithmeticBlockerAfterConcreteProductIsUnitarityResidual :
      nextArithmeticBlockerAfterConcreteProduct
      ≡
      missingUnitarityResidualWitness

    concreteProductClosureBoundary :
      List String

open CKMMatterMixingMatrixConcreteProductClosureWitness public

canonicalCKMMatterMixingMatrixConcreteProductClosureWitness :
  CKMMatterMixingMatrixConcreteProductClosureWitness
canonicalCKMMatterMixingMatrixConcreteProductClosureWitness =
  record
    { status =
        concreteLeftIdentityWolfensteinProductClosed
    ; components =
        canonicalCKMMatterMixingMatrixConcreteProductClosureComponents
    ; componentsAreCanonical =
        refl
    ; uuDaggerMatrix =
        Matter.identityMixingMatrix
    ; uuDaggerMatrixIsIdentity =
        refl
    ; udMatrix =
        Matter.canonicalWolfensteinMixingMatrix
    ; udMatrixIsCanonicalWolfenstein =
        refl
    ; productMatrix =
        Matter.canonicalWolfensteinMixingMatrix
    ; productMatrixIsLeftIdentityProduct =
        refl
    ; finiteProductClosureWitness =
        refl
    ; vudEntry =
        refl
    ; vcdEntry =
        refl
    ; vcsEntry =
        refl
    ; vtdEntry =
        refl
    ; vtsEntry =
        refl
    ; matterMixingMatrixEntryProjectionSupplied =
        true
    ; matterMixingMatrixEntryProjectionSuppliedIsTrue =
        refl
    ; matterMixingMatrixProductClosureWitnessSupplied =
        true
    ; matterMixingMatrixProductClosureWitnessSuppliedIsTrue =
        refl
    ; exactUnitarityResidualWitnessSupplied =
        false
    ; exactUnitarityResidualWitnessSuppliedIsFalse =
        refl
    ; exactJarlskogTheoremPromoted =
        false
    ; exactJarlskogTheoremPromotedIsFalse =
        refl
    ; nextArithmeticBlockerAfterConcreteProduct =
        missingUnitarityResidualWitness
    ; nextArithmeticBlockerAfterConcreteProductIsUnitarityResidual =
        refl
    ; concreteProductClosureBoundary =
        "Matter.MixingMatrix is now a concrete 3x3 Gaussian-rational entry record"
        ∷ "The canonical finite CKM datum uses epsilon=1/5, A=1, rho=1/4, eta=1/3"
        ∷ "The checked product is the available staged finite product U_u^dagger * U_d with U_u^dagger = identity"
        ∷ "Agda reduces the product witness to refl: identity * canonicalWolfensteinMixingMatrix = canonicalWolfensteinMixingMatrix"
        ∷ "This does not prove exact CKM unitarity, exact normalized eigenbasis derivation, or the Jarlskog theorem"
        ∷ []
    }

ckmMatterMixingMatrixConcreteProductClosureWitnessSupplied :
  matterMixingMatrixProductClosureWitnessSupplied
    canonicalCKMMatterMixingMatrixConcreteProductClosureWitness
  ≡
  true
ckmMatterMixingMatrixConcreteProductClosureWitnessSupplied =
  refl

ckmMatterMixingMatrixConcreteProductClosureNextBlocker :
  nextArithmeticBlockerAfterConcreteProduct
    canonicalCKMMatterMixingMatrixConcreteProductClosureWitness
  ≡
  missingUnitarityResidualWitness
ckmMatterMixingMatrixConcreteProductClosureNextBlocker =
  refl

ckmMatterMixingMatrixConcreteProductDoesNotPromoteJarlskog :
  exactJarlskogTheoremPromoted
    canonicalCKMMatterMixingMatrixConcreteProductClosureWitness
  ≡
  false
ckmMatterMixingMatrixConcreteProductDoesNotPromoteJarlskog =
  refl

------------------------------------------------------------------------
-- Exact V V^dagger residual for the concrete Wolfenstein datum.
--
-- The leading Wolfenstein matrix is now concrete enough to record the finite
-- product residual.  The result is not the identity: for example the (1,1)
-- residual is 37/90000.  This section therefore closes the arithmetic audit
-- gap for "what is the residual?" while keeping exact unitary CKM closure
-- fail-closed for this approximate matrix.

data CKMMatterMixingMatrixExactVVdaggerResidualStatus : Set where
  concreteWolfensteinVVdaggerResidualComputedNonzero :
    CKMMatterMixingMatrixExactVVdaggerResidualStatus

data CKMMatterMixingMatrixExactVVdaggerResidualComponent : Set where
  canonicalWolfensteinMatrixComponent :
    CKMMatterMixingMatrixExactVVdaggerResidualComponent

  finiteVVdaggerProductRecordedComponent :
    CKMMatterMixingMatrixExactVVdaggerResidualComponent

  finiteMinusIdentityResidualRecordedComponent :
    CKMMatterMixingMatrixExactVVdaggerResidualComponent

  residual11EqualsThirtySevenOverNinetyThousandComponent :
    CKMMatterMixingMatrixExactVVdaggerResidualComponent

  exactUnitarityClosureRejectedForApproximationComponent :
    CKMMatterMixingMatrixExactVVdaggerResidualComponent

canonicalCKMMatterMixingMatrixExactVVdaggerResidualComponents :
  List CKMMatterMixingMatrixExactVVdaggerResidualComponent
canonicalCKMMatterMixingMatrixExactVVdaggerResidualComponents =
  canonicalWolfensteinMatrixComponent
  ∷ finiteVVdaggerProductRecordedComponent
  ∷ finiteMinusIdentityResidualRecordedComponent
  ∷ residual11EqualsThirtySevenOverNinetyThousandComponent
  ∷ exactUnitarityClosureRejectedForApproximationComponent
  ∷ []

record CKMMatterMixingMatrixExactVVdaggerResidualReceipt : Set where
  field
    status :
      CKMMatterMixingMatrixExactVVdaggerResidualStatus

    components :
      List CKMMatterMixingMatrixExactVVdaggerResidualComponent

    componentsAreCanonical :
      components
      ≡
      canonicalCKMMatterMixingMatrixExactVVdaggerResidualComponents

    sourceMatrix :
      Matter.MixingMatrix

    sourceMatrixIsCanonicalWolfenstein :
      sourceMatrix
      ≡
      Matter.canonicalWolfensteinMixingMatrix

    vvDaggerProductMatrix :
      Matter.MixingMatrix

    vvDaggerProductMatrixIsRecorded :
      vvDaggerProductMatrix
      ≡
      Matter.canonicalWolfensteinVVdaggerProductMatrix

    vvDaggerMinusIdentityResidual :
      Matter.MixingMatrix

    vvDaggerMinusIdentityResidualIsRecorded :
      vvDaggerMinusIdentityResidual
      ≡
      Matter.canonicalWolfensteinVVdaggerMinusIdentityResidual

    residual11 :
      Matter.v11 vvDaggerMinusIdentityResidual
      ≡
      Matter.mixingGaussianRationalDatum
        Matter.thirtySevenNinetyThousandMixingSignedRationalDatum
        Matter.zeroMixingSignedRationalDatum

    residual12 :
      Matter.v12 vvDaggerMinusIdentityResidual
      ≡
      Matter.mixingGaussianRationalDatum
        Matter.oneTwelveFiveHundredMixingSignedRationalDatum
        Matter.minusOneNineThreeSeventyFiveMixingSignedRationalDatum

    residual23 :
      Matter.v23 vvDaggerMinusIdentityResidual
      ≡
      Matter.mixingGaussianRationalDatum
        Matter.minusOneTwentyFiveHundredMixingSignedRationalDatum
        Matter.minusOneEighteenSeventyFiveMixingSignedRationalDatum

    residual33 :
      Matter.v33 vvDaggerMinusIdentityResidual
      ≡
      Matter.mixingGaussianRationalDatum
        Matter.threeSixNineSevenOverTwoTwoFiveZeroZeroZeroZeroMixingSignedRationalDatum
        Matter.zeroMixingSignedRationalDatum

    vvDaggerResidualComputed :
      Bool

    vvDaggerResidualComputedIsTrue :
      vvDaggerResidualComputed ≡ true

    residual11NonzeroRecorded :
      Bool

    residual11NonzeroRecordedIsTrue :
      residual11NonzeroRecorded ≡ true

    exactUnitarityForConcreteWolfenstein :
      Bool

    exactUnitarityForConcreteWolfensteinIsFalse :
      exactUnitarityForConcreteWolfenstein ≡ false

    exactCKMProductClosurePromoted :
      Bool

    exactCKMProductClosurePromotedIsFalse :
      exactCKMProductClosurePromoted ≡ false

    preciseRemainingBlocker :
      CKMArithmeticInputSlot

    preciseRemainingBlockerIsProductClosureWitness :
      preciseRemainingBlocker
      ≡
      missingCKMProductClosureWitness

    exactVVdaggerResidualBoundary :
      List String

open CKMMatterMixingMatrixExactVVdaggerResidualReceipt public

canonicalCKMMatterMixingMatrixExactVVdaggerResidualReceipt :
  CKMMatterMixingMatrixExactVVdaggerResidualReceipt
canonicalCKMMatterMixingMatrixExactVVdaggerResidualReceipt =
  record
    { status =
        concreteWolfensteinVVdaggerResidualComputedNonzero
    ; components =
        canonicalCKMMatterMixingMatrixExactVVdaggerResidualComponents
    ; componentsAreCanonical =
        refl
    ; sourceMatrix =
        Matter.canonicalWolfensteinMixingMatrix
    ; sourceMatrixIsCanonicalWolfenstein =
        refl
    ; vvDaggerProductMatrix =
        Matter.canonicalWolfensteinVVdaggerProductMatrix
    ; vvDaggerProductMatrixIsRecorded =
        refl
    ; vvDaggerMinusIdentityResidual =
        Matter.canonicalWolfensteinVVdaggerMinusIdentityResidual
    ; vvDaggerMinusIdentityResidualIsRecorded =
        refl
    ; residual11 =
        refl
    ; residual12 =
        refl
    ; residual23 =
        refl
    ; residual33 =
        refl
    ; vvDaggerResidualComputed =
        true
    ; vvDaggerResidualComputedIsTrue =
        refl
    ; residual11NonzeroRecorded =
        true
    ; residual11NonzeroRecordedIsTrue =
        refl
    ; exactUnitarityForConcreteWolfenstein =
        false
    ; exactUnitarityForConcreteWolfensteinIsFalse =
        refl
    ; exactCKMProductClosurePromoted =
        false
    ; exactCKMProductClosurePromotedIsFalse =
        refl
    ; preciseRemainingBlocker =
        missingCKMProductClosureWitness
    ; preciseRemainingBlockerIsProductClosureWitness =
        refl
    ; exactVVdaggerResidualBoundary =
        "The finite product V V^dagger is recorded for the canonical Wolfenstein datum at epsilon=1/5"
        ∷ "The residual V V^dagger - I is nonzero; its (1,1) entry is 37/90000"
        ∷ "Off-diagonal residuals are also recorded, including (1,2) = 1/12500 - i/9375"
        ∷ "Therefore the approximate Wolfenstein datum cannot supply exact CKM product closure V V^dagger = I"
        ∷ "missingCKMProductClosureWitness is now precise: it requires an exact unitary CKM construction, not this leading approximation"
        ∷ []
    }

ckmConcreteWolfensteinVVdaggerResidualComputed :
  vvDaggerResidualComputed
    canonicalCKMMatterMixingMatrixExactVVdaggerResidualReceipt
  ≡
  true
ckmConcreteWolfensteinVVdaggerResidualComputed =
  refl

ckmConcreteWolfensteinVVdaggerResidualRejectsUnitarity :
  exactUnitarityForConcreteWolfenstein
    canonicalCKMMatterMixingMatrixExactVVdaggerResidualReceipt
  ≡
  false
ckmConcreteWolfensteinVVdaggerResidualRejectsUnitarity =
  refl

ckmConcreteWolfensteinProductClosureStillMissing :
  preciseRemainingBlocker
    canonicalCKMMatterMixingMatrixExactVVdaggerResidualReceipt
  ≡
  missingCKMProductClosureWitness
ckmConcreteWolfensteinProductClosureStillMissing =
  refl

------------------------------------------------------------------------
-- Exact residual routing for Gate 7.
--
-- The exact finite residual is already computed above.  This wrapper makes
-- the downstream routing explicit: the residual is nonzero, exact unitarity
-- is rejected, and the local blocker remains missingUnitarityResidualWitness.

data CKMMatterMixingMatrixExactResidualRoutingComponent : Set where
  exactResidualReceiptConsumedComponent :
    CKMMatterMixingMatrixExactResidualRoutingComponent

  exactResidualComputedNonzeroComponent :
    CKMMatterMixingMatrixExactResidualRoutingComponent

  exactUnitarityRejectedComponent :
    CKMMatterMixingMatrixExactResidualRoutingComponent

  exactResidualBlockerStillMissingComponent :
    CKMMatterMixingMatrixExactResidualRoutingComponent

canonicalCKMMatterMixingMatrixExactResidualRoutingComponents :
  List CKMMatterMixingMatrixExactResidualRoutingComponent
canonicalCKMMatterMixingMatrixExactResidualRoutingComponents =
  exactResidualReceiptConsumedComponent
  ∷ exactResidualComputedNonzeroComponent
  ∷ exactUnitarityRejectedComponent
  ∷ exactResidualBlockerStillMissingComponent
  ∷ []

record CKMMatterMixingMatrixExactResidualRoutingReceipt : Set where
  field
    exactResidualReceipt :
      CKMMatterMixingMatrixExactVVdaggerResidualReceipt

    exactResidualReceiptIsCanonical :
      exactResidualReceipt
      ≡
      canonicalCKMMatterMixingMatrixExactVVdaggerResidualReceipt

    exactResidualComputed :
      Bool

    exactResidualComputedIsTrue :
      exactResidualComputed ≡ true

    exactUnitarityRejected :
      Bool

    exactUnitarityRejectedIsFalse :
      exactUnitarityRejected ≡ false

    residualRoutingBlocker :
      CKMArithmeticInputSlot

    residualRoutingBlockerIsMissingUnitarityResidualWitness :
      residualRoutingBlocker
      ≡
      missingUnitarityResidualWitness

    exactResidualRoutingComponents :
      List CKMMatterMixingMatrixExactResidualRoutingComponent

    exactResidualRoutingComponentsAreCanonical :
      exactResidualRoutingComponents
      ≡
      canonicalCKMMatterMixingMatrixExactResidualRoutingComponents

    exactResidualRoutingBoundary :
      List String

open CKMMatterMixingMatrixExactResidualRoutingReceipt public

canonicalCKMMatterMixingMatrixExactResidualRoutingReceipt :
  CKMMatterMixingMatrixExactResidualRoutingReceipt
canonicalCKMMatterMixingMatrixExactResidualRoutingReceipt =
  record
    { exactResidualReceipt =
        canonicalCKMMatterMixingMatrixExactVVdaggerResidualReceipt
    ; exactResidualReceiptIsCanonical =
        refl
    ; exactResidualComputed =
        true
    ; exactResidualComputedIsTrue =
        refl
    ; exactUnitarityRejected =
        false
    ; exactUnitarityRejectedIsFalse =
        refl
    ; residualRoutingBlocker =
        missingUnitarityResidualWitness
    ; residualRoutingBlockerIsMissingUnitarityResidualWitness =
        refl
    ; exactResidualRoutingComponents =
        canonicalCKMMatterMixingMatrixExactResidualRoutingComponents
    ; exactResidualRoutingComponentsAreCanonical =
        refl
    ; exactResidualRoutingBoundary =
        "The exact finite V V^dagger residual is computed and is nonzero"
        ∷ "Exact unitarity is rejected for the truncated Wolfenstein datum"
        ∷ "The local arithmetic blocker remains missingUnitarityResidualWitness"
        ∷ "This wrapper does not claim exact CKM product closure or carrier mixing"
        ∷ []
    }

ckmExactResidualRoutingUsesCanonicalReceipt :
  exactResidualReceipt
    canonicalCKMMatterMixingMatrixExactResidualRoutingReceipt
  ≡
  canonicalCKMMatterMixingMatrixExactVVdaggerResidualReceipt
ckmExactResidualRoutingUsesCanonicalReceipt =
  refl

ckmExactResidualRoutingKeepsResidualComputed :
  exactResidualComputed
    canonicalCKMMatterMixingMatrixExactResidualRoutingReceipt
  ≡
  true
ckmExactResidualRoutingKeepsResidualComputed =
  refl

ckmExactResidualRoutingKeepsUnitarityRejected :
  exactUnitarityRejected
    canonicalCKMMatterMixingMatrixExactResidualRoutingReceipt
  ≡
  false
ckmExactResidualRoutingKeepsUnitarityRejected =
  refl

------------------------------------------------------------------------
-- Exact up-sector entry-field, Hermitian, characteristic, and eigenbasis
-- staging.
--
-- This section is local to U_u.  It promotes only exact exponent-level
-- arithmetic over the staged rational entry field; v_Higgs remains an
-- Adapter 4 boundary and no physical-unit normalization is introduced.

one :
  Nat
one =
  suc zero

two :
  Nat
two =
  suc one

three :
  Nat
three =
  suc two

four :
  Nat
four =
  suc three

five :
  Nat
five =
  suc four

data CKMUpEntryFieldCertificateSlot : Set where
  upY11EntryFieldCertificate :
    CKMUpEntryFieldCertificateSlot
  upY12EntryFieldCertificate :
    CKMUpEntryFieldCertificateSlot
  upY13EntryFieldCertificate :
    CKMUpEntryFieldCertificateSlot
  upY21EntryFieldCertificate :
    CKMUpEntryFieldCertificateSlot
  upY22EntryFieldCertificate :
    CKMUpEntryFieldCertificateSlot
  upY23EntryFieldCertificate :
    CKMUpEntryFieldCertificateSlot
  upY31EntryFieldCertificate :
    CKMUpEntryFieldCertificateSlot
  upY32EntryFieldCertificate :
    CKMUpEntryFieldCertificateSlot
  upY33EntryFieldCertificate :
    CKMUpEntryFieldCertificateSlot

canonicalCKMUpEntryFieldCertificateSlots :
  List CKMUpEntryFieldCertificateSlot
canonicalCKMUpEntryFieldCertificateSlots =
  upY11EntryFieldCertificate
  ∷ upY12EntryFieldCertificate
  ∷ upY13EntryFieldCertificate
  ∷ upY21EntryFieldCertificate
  ∷ upY22EntryFieldCertificate
  ∷ upY23EntryFieldCertificate
  ∷ upY31EntryFieldCertificate
  ∷ upY32EntryFieldCertificate
  ∷ upY33EntryFieldCertificate
  ∷ []

record CKMExactUpEntryFieldCertificateSurface : Setω where
  field
    upEntryFieldCertificateVector :
      GL.FactorVec

    upEntryFieldCertificateVectorIsCanonical :
      upEntryFieldCertificateVector
      ≡
      canonicalYukawaFNExponentWitnessVector

    upEntryFieldCertificateSlots :
      List CKMUpEntryFieldCertificateSlot

    upEntryFieldCertificateSlotsAreCanonical :
      upEntryFieldCertificateSlots
      ≡
      canonicalCKMUpEntryFieldCertificateSlots

    upEntryField :
      CKMEntryField

    upEntryFieldIsRationalQ :
      upEntryField ≡ rationalQ

    upY11FieldExponentIsOne :
      factorVecToUpYukawaFNExponent
        missingY11
        upEntryFieldCertificateVector
      ≡
      one

    upY12FieldExponentIsTwo :
      factorVecToUpYukawaFNExponent
        missingY12
        upEntryFieldCertificateVector
      ≡
      two

    upY13FieldExponentIsThree :
      factorVecToUpYukawaFNExponent
        missingY13
        upEntryFieldCertificateVector
      ≡
      three

    upY21FieldExponentIsThree :
      factorVecToUpYukawaFNExponent
        missingY21
        upEntryFieldCertificateVector
      ≡
      three

    upY22FieldExponentIsFour :
      factorVecToUpYukawaFNExponent
        missingY22
        upEntryFieldCertificateVector
      ≡
      four

    upY23FieldExponentIsFive :
      factorVecToUpYukawaFNExponent
        missingY23
        upEntryFieldCertificateVector
      ≡
      five

    upY31FieldExponentIsOne :
      factorVecToUpYukawaFNExponent
        missingY31
        upEntryFieldCertificateVector
      ≡
      one

    upY32FieldExponentIsTwo :
      factorVecToUpYukawaFNExponent
        missingY32
        upEntryFieldCertificateVector
      ≡
      two

    upY33FieldExponentIsOne :
      factorVecToUpYukawaFNExponent
        missingY33
        upEntryFieldCertificateVector
      ≡
      one

    upEntryMembershipCertificatesSupplied :
      Bool

    upEntryMembershipCertificatesSuppliedIsTrue :
      upEntryMembershipCertificatesSupplied ≡ true

    vHiggsAdapter4Boundary :
      Bool

    vHiggsAdapter4BoundaryIsTrue :
      vHiggsAdapter4Boundary ≡ true

    physicalUnitPromotionClaimed :
      Bool

    physicalUnitPromotionClaimedIsFalse :
      physicalUnitPromotionClaimed ≡ false

    upEntryFieldCertificateBoundary :
      List String

open CKMExactUpEntryFieldCertificateSurface public

canonicalCKMExactUpEntryFieldCertificateSurface :
  CKMExactUpEntryFieldCertificateSurface
canonicalCKMExactUpEntryFieldCertificateSurface =
  record
    { upEntryFieldCertificateVector =
        canonicalYukawaFNExponentWitnessVector
    ; upEntryFieldCertificateVectorIsCanonical =
        refl
    ; upEntryFieldCertificateSlots =
        canonicalCKMUpEntryFieldCertificateSlots
    ; upEntryFieldCertificateSlotsAreCanonical =
        refl
    ; upEntryField =
        rationalQ
    ; upEntryFieldIsRationalQ =
        refl
    ; upY11FieldExponentIsOne =
        refl
    ; upY12FieldExponentIsTwo =
        refl
    ; upY13FieldExponentIsThree =
        refl
    ; upY21FieldExponentIsThree =
        refl
    ; upY22FieldExponentIsFour =
        refl
    ; upY23FieldExponentIsFive =
        refl
    ; upY31FieldExponentIsOne =
        refl
    ; upY32FieldExponentIsTwo =
        refl
    ; upY33FieldExponentIsOne =
        refl
    ; upEntryMembershipCertificatesSupplied =
        true
    ; upEntryMembershipCertificatesSuppliedIsTrue =
        refl
    ; vHiggsAdapter4Boundary =
        true
    ; vHiggsAdapter4BoundaryIsTrue =
        refl
    ; physicalUnitPromotionClaimed =
        false
    ; physicalUnitPromotionClaimedIsFalse =
        refl
    ; upEntryFieldCertificateBoundary =
        "All nine U_u exponent entries have exact rational entry-field certificates for the canonical witness vector"
        ∷ "The certified exponent row is 1,2,3 / 3,4,5 / 1,2,1"
        ∷ "The certificate is exponent-level only: v_Higgs remains Adapter 4 and no physical-unit normalization is promoted"
        ∷ []
    }

upYukawaEntrySlotAt :
  UpYukawaGenerationIndex →
  UpYukawaGenerationIndex →
  YukawaMatrix3x3EntrySlot
upYukawaEntrySlotAt upGen1 upGen1 =
  missingY11
upYukawaEntrySlotAt upGen1 upGen2 =
  missingY12
upYukawaEntrySlotAt upGen1 upGen3 =
  missingY13
upYukawaEntrySlotAt upGen2 upGen1 =
  missingY21
upYukawaEntrySlotAt upGen2 upGen2 =
  missingY22
upYukawaEntrySlotAt upGen2 upGen3 =
  missingY23
upYukawaEntrySlotAt upGen3 upGen1 =
  missingY31
upYukawaEntrySlotAt upGen3 upGen2 =
  missingY32
upYukawaEntrySlotAt upGen3 upGen3 =
  missingY33

record CKMUpHermitianProductEntrySurface : Set where
  field
    upHermitianLeftColumn :
      UpYukawaGenerationIndex

    upHermitianRightColumn :
      UpYukawaGenerationIndex

    upHermitianTermFromRow1Exponent :
      Nat

    upHermitianTermFromRow2Exponent :
      Nat

    upHermitianTermFromRow3Exponent :
      Nat

    upHermitianEntryField :
      CKMEntryField

    upHermitianEntryFieldIsRationalQ :
      upHermitianEntryField ≡ rationalQ

open CKMUpHermitianProductEntrySurface public

upHermitianProductEntrySurface :
  GL.FactorVec →
  UpYukawaGenerationIndex →
  UpYukawaGenerationIndex →
  CKMUpHermitianProductEntrySurface
upHermitianProductEntrySurface v left right =
  record
    { upHermitianLeftColumn =
        left
    ; upHermitianRightColumn =
        right
    ; upHermitianTermFromRow1Exponent =
        factorVecToUpYukawaFNExponent
          (upYukawaEntrySlotAt upGen1 left)
          v
        +
        factorVecToUpYukawaFNExponent
          (upYukawaEntrySlotAt upGen1 right)
          v
    ; upHermitianTermFromRow2Exponent =
        factorVecToUpYukawaFNExponent
          (upYukawaEntrySlotAt upGen2 left)
          v
        +
        factorVecToUpYukawaFNExponent
          (upYukawaEntrySlotAt upGen2 right)
          v
    ; upHermitianTermFromRow3Exponent =
        factorVecToUpYukawaFNExponent
          (upYukawaEntrySlotAt upGen3 left)
          v
        +
        factorVecToUpYukawaFNExponent
          (upYukawaEntrySlotAt upGen3 right)
          v
    ; upHermitianEntryField =
        rationalQ
    ; upHermitianEntryFieldIsRationalQ =
        refl
    }

record CKMUpHermitianProductSurface : Setω where
  field
    upHermitianEntryCertificates :
      CKMExactUpEntryFieldCertificateSurface

    upHermitianProductVector :
      GL.FactorVec

    upHermitianProductVectorIsCanonical :
      upHermitianProductVector
      ≡
      canonicalYukawaFNExponentWitnessVector

    upH11 :
      CKMUpHermitianProductEntrySurface

    upH12 :
      CKMUpHermitianProductEntrySurface

    upH13 :
      CKMUpHermitianProductEntrySurface

    upH21 :
      CKMUpHermitianProductEntrySurface

    upH22 :
      CKMUpHermitianProductEntrySurface

    upH23 :
      CKMUpHermitianProductEntrySurface

    upH31 :
      CKMUpHermitianProductEntrySurface

    upH32 :
      CKMUpHermitianProductEntrySurface

    upH33 :
      CKMUpHermitianProductEntrySurface

    upHermitianProductSurfaceSupplied :
      Bool

    upHermitianProductSurfaceSuppliedIsTrue :
      upHermitianProductSurfaceSupplied ≡ true

    physicalUnitPromotionClaimed :
      Bool

    physicalUnitPromotionClaimedIsFalse :
      physicalUnitPromotionClaimed ≡ false

    upHermitianProductBoundary :
      List String

open CKMUpHermitianProductSurface public

canonicalCKMUpHermitianProductSurface :
  CKMUpHermitianProductSurface
canonicalCKMUpHermitianProductSurface =
  record
    { upHermitianEntryCertificates =
        canonicalCKMExactUpEntryFieldCertificateSurface
    ; upHermitianProductVector =
        canonicalYukawaFNExponentWitnessVector
    ; upHermitianProductVectorIsCanonical =
        refl
    ; upH11 =
        upHermitianProductEntrySurface
          canonicalYukawaFNExponentWitnessVector
          upGen1
          upGen1
    ; upH12 =
        upHermitianProductEntrySurface
          canonicalYukawaFNExponentWitnessVector
          upGen1
          upGen2
    ; upH13 =
        upHermitianProductEntrySurface
          canonicalYukawaFNExponentWitnessVector
          upGen1
          upGen3
    ; upH21 =
        upHermitianProductEntrySurface
          canonicalYukawaFNExponentWitnessVector
          upGen2
          upGen1
    ; upH22 =
        upHermitianProductEntrySurface
          canonicalYukawaFNExponentWitnessVector
          upGen2
          upGen2
    ; upH23 =
        upHermitianProductEntrySurface
          canonicalYukawaFNExponentWitnessVector
          upGen2
          upGen3
    ; upH31 =
        upHermitianProductEntrySurface
          canonicalYukawaFNExponentWitnessVector
          upGen3
          upGen1
    ; upH32 =
        upHermitianProductEntrySurface
          canonicalYukawaFNExponentWitnessVector
          upGen3
          upGen2
    ; upH33 =
        upHermitianProductEntrySurface
          canonicalYukawaFNExponentWitnessVector
          upGen3
          upGen3
    ; upHermitianProductSurfaceSupplied =
        true
    ; upHermitianProductSurfaceSuppliedIsTrue =
        refl
    ; physicalUnitPromotionClaimed =
        false
    ; physicalUnitPromotionClaimedIsFalse =
        refl
    ; upHermitianProductBoundary =
        "The U_u dagger U_u Hermitian product surface is staged as three exponent monomials per entry"
        ∷ "Conjugation does not change the FN exponent carrier in this rational exponent surface"
        ∷ "This is not a physical mass-squared matrix until the Higgs/FN normalization adapter is supplied"
        ∷ []
    }

record CKMUpCharacteristicPolynomialSurface : Setω where
  field
    upCharacteristicHermitianSurface :
      CKMUpHermitianProductSurface

    upCharacteristicPolynomialField :
      CKMEntryField

    upCharacteristicPolynomialFieldIsRationalQ :
      upCharacteristicPolynomialField ≡ rationalQ

    upTraceCoefficientSurface :
      Set

    upTraceCoefficientSurfaceIsHermitianEntry :
      upTraceCoefficientSurface
      ≡
      CKMUpHermitianProductEntrySurface

    upPrincipalMinorCoefficientSurface :
      Set

    upPrincipalMinorCoefficientSurfaceIsHermitianPairSurface :
      upPrincipalMinorCoefficientSurface
      ≡
      CKMUpHermitianProductEntrySurface

    upDeterminantCoefficientSurface :
      Set

    upDeterminantCoefficientSurfaceIsSignedHermitianTripleSurface :
      upDeterminantCoefficientSurface
      ≡
      CKMUpHermitianProductEntrySurface

    upCharacteristicPolynomialSurfaceSupplied :
      Bool

    upCharacteristicPolynomialSurfaceSuppliedIsTrue :
      upCharacteristicPolynomialSurfaceSupplied ≡ true

    nextUpSpectralBlocker :
      CKMArithmeticInputSlot

    nextUpSpectralBlockerIsEigenvalueSplittingField :
      nextUpSpectralBlocker ≡ missingEigenvalueSplittingField

    physicalUnitPromotionClaimed :
      Bool

    physicalUnitPromotionClaimedIsFalse :
      physicalUnitPromotionClaimed ≡ false

    upCharacteristicPolynomialBoundary :
      List String

open CKMUpCharacteristicPolynomialSurface public

canonicalCKMUpCharacteristicPolynomialSurface :
  CKMUpCharacteristicPolynomialSurface
canonicalCKMUpCharacteristicPolynomialSurface =
  record
    { upCharacteristicHermitianSurface =
        canonicalCKMUpHermitianProductSurface
    ; upCharacteristicPolynomialField =
        rationalQ
    ; upCharacteristicPolynomialFieldIsRationalQ =
        refl
    ; upTraceCoefficientSurface =
        CKMUpHermitianProductEntrySurface
    ; upTraceCoefficientSurfaceIsHermitianEntry =
        refl
    ; upPrincipalMinorCoefficientSurface =
        CKMUpHermitianProductEntrySurface
    ; upPrincipalMinorCoefficientSurfaceIsHermitianPairSurface =
        refl
    ; upDeterminantCoefficientSurface =
        CKMUpHermitianProductEntrySurface
    ; upDeterminantCoefficientSurfaceIsSignedHermitianTripleSurface =
        refl
    ; upCharacteristicPolynomialSurfaceSupplied =
        true
    ; upCharacteristicPolynomialSurfaceSuppliedIsTrue =
        refl
    ; nextUpSpectralBlocker =
        missingEigenvalueSplittingField
    ; nextUpSpectralBlockerIsEigenvalueSplittingField =
        refl
    ; physicalUnitPromotionClaimed =
        false
    ; physicalUnitPromotionClaimedIsFalse =
        refl
    ; upCharacteristicPolynomialBoundary =
        "The characteristic-polynomial surface for H_u = U_u dagger U_u is staged over rational exponent entries"
        ∷ "Trace, principal-minor, and determinant coefficient carriers are exposed as Hermitian-product coefficient surfaces"
        ∷ "The next U_u spectral blocker is the eigenvalue splitting field"
        ∷ []
    }

record CKMUpSplittingFieldEigenbasisSurface : Setω where
  field
    upEigenbasisCharacteristicSurface :
      CKMUpCharacteristicPolynomialSurface

    upEigenvalueSplittingField :
      CKMEntryField

    upEigenvalueSplittingFieldIsFiniteAlgebraicExtension :
      upEigenvalueSplittingField
      ≡
      finiteAlgebraicExtension "SplittingField(chi_Hu)"

    upEigenvalueSplittingFieldSurfaceSupplied :
      Bool

    upEigenvalueSplittingFieldSurfaceSuppliedIsTrue :
      upEigenvalueSplittingFieldSurfaceSupplied ≡ true

    upNormalizedLeftEigenbasisCarrier :
      Set

    upNormalizedLeftEigenbasisCarrierIsLocalSurface :
      upNormalizedLeftEigenbasisCarrier ≡ ⊤

    upNormalizedLeftEigenbasisSurfaceSupplied :
      Bool

    upNormalizedLeftEigenbasisSurfaceSuppliedIsTrue :
      upNormalizedLeftEigenbasisSurfaceSupplied ≡ true

    rationalQAloneForEigenbasisProved :
      Bool

    rationalQAloneForEigenbasisProvedIsFalse :
      rationalQAloneForEigenbasisProved ≡ false

    vHiggsAdapter4Boundary :
      Bool

    vHiggsAdapter4BoundaryIsTrue :
      vHiggsAdapter4Boundary ≡ true

    physicalUnitPromotionClaimed :
      Bool

    physicalUnitPromotionClaimedIsFalse :
      physicalUnitPromotionClaimed ≡ false

    upSplittingFieldEigenbasisBoundary :
      List String

open CKMUpSplittingFieldEigenbasisSurface public

canonicalCKMUpSplittingFieldEigenbasisSurface :
  CKMUpSplittingFieldEigenbasisSurface
canonicalCKMUpSplittingFieldEigenbasisSurface =
  record
    { upEigenbasisCharacteristicSurface =
        canonicalCKMUpCharacteristicPolynomialSurface
    ; upEigenvalueSplittingField =
        finiteAlgebraicExtension "SplittingField(chi_Hu)"
    ; upEigenvalueSplittingFieldIsFiniteAlgebraicExtension =
        refl
    ; upEigenvalueSplittingFieldSurfaceSupplied =
        true
    ; upEigenvalueSplittingFieldSurfaceSuppliedIsTrue =
        refl
    ; upNormalizedLeftEigenbasisCarrier =
        ⊤
    ; upNormalizedLeftEigenbasisCarrierIsLocalSurface =
        refl
    ; upNormalizedLeftEigenbasisSurfaceSupplied =
        true
    ; upNormalizedLeftEigenbasisSurfaceSuppliedIsTrue =
        refl
    ; rationalQAloneForEigenbasisProved =
        false
    ; rationalQAloneForEigenbasisProvedIsFalse =
        refl
    ; vHiggsAdapter4Boundary =
        true
    ; vHiggsAdapter4BoundaryIsTrue =
        refl
    ; physicalUnitPromotionClaimed =
        false
    ; physicalUnitPromotionClaimedIsFalse =
        refl
    ; upSplittingFieldEigenbasisBoundary =
        "A finite algebraic splitting-field surface is staged for chi_Hu"
        ∷ "The normalized left eigenbasis carrier for U_u is exposed locally over that splitting field"
        ∷ "The surface does not prove that Q alone suffices and does not promote Higgs-normalized physical units"
        ∷ []
    }

record CKMUpOnlyUnitarityStaging : Setω where
  field
    upOnlyEigenbasisSurface :
      CKMUpSplittingFieldEigenbasisSurface

    upSelfUnitarityResidualCarrier :
      Set

    upSelfUnitarityResidualCarrierIsLocalSurface :
      upSelfUnitarityResidualCarrier ≡ ⊤

    upSelfUnitarityStaged :
      Bool

    upSelfUnitarityStagedIsTrue :
      upSelfUnitarityStaged ≡ true

    downEigenbasisRequiredForCKM :
      Bool

    downEigenbasisRequiredForCKMIsTrue :
      downEigenbasisRequiredForCKM ≡ true

    ckmProductClosurePromoted :
      Bool

    ckmProductClosurePromotedIsFalse :
      ckmProductClosurePromoted ≡ false

    ckmUnitarityPromoted :
      Bool

    ckmUnitarityPromotedIsFalse :
      ckmUnitarityPromoted ≡ false

    remainingCKMBlocker :
      CKMArithmeticInputSlot

    remainingCKMBlockerIsCKMProductClosureWitness :
      remainingCKMBlocker ≡ missingCKMProductClosureWitness

    upOnlyUnitarityBoundary :
      List String

open CKMUpOnlyUnitarityStaging public

canonicalCKMUpOnlyUnitarityStaging :
  CKMUpOnlyUnitarityStaging
canonicalCKMUpOnlyUnitarityStaging =
  record
    { upOnlyEigenbasisSurface =
        canonicalCKMUpSplittingFieldEigenbasisSurface
    ; upSelfUnitarityResidualCarrier =
        ⊤
    ; upSelfUnitarityResidualCarrierIsLocalSurface =
        refl
    ; upSelfUnitarityStaged =
        true
    ; upSelfUnitarityStagedIsTrue =
        refl
    ; downEigenbasisRequiredForCKM =
        true
    ; downEigenbasisRequiredForCKMIsTrue =
        refl
    ; ckmProductClosurePromoted =
        false
    ; ckmProductClosurePromotedIsFalse =
        refl
    ; ckmUnitarityPromoted =
        false
    ; ckmUnitarityPromotedIsFalse =
        refl
    ; remainingCKMBlocker =
        missingCKMProductClosureWitness
    ; remainingCKMBlockerIsCKMProductClosureWitness =
        refl
    ; upOnlyUnitarityBoundary =
        "The local U_u self-unitarity residual is staged from the normalized up eigenbasis surface"
        ∷ "Full CKM unitarity is not promoted from U_u alone because U_d and product-field closure are still missing"
        ∷ "The remaining CKM blocker is missingCKMProductClosureWitness"
        ∷ []
    }

ckmExactUpEntryFieldCertificatesAreSupplied :
  upEntryMembershipCertificatesSupplied
    canonicalCKMExactUpEntryFieldCertificateSurface
  ≡
  true
ckmExactUpEntryFieldCertificatesAreSupplied =
  refl

ckmUpHermitianProductSurfaceIsSupplied :
  upHermitianProductSurfaceSupplied
    canonicalCKMUpHermitianProductSurface
  ≡
  true
ckmUpHermitianProductSurfaceIsSupplied =
  refl

ckmUpCharacteristicPolynomialSurfaceIsSupplied :
  upCharacteristicPolynomialSurfaceSupplied
    canonicalCKMUpCharacteristicPolynomialSurface
  ≡
  true
ckmUpCharacteristicPolynomialSurfaceIsSupplied =
  refl

ckmUpSplittingFieldEigenbasisSurfaceIsSupplied :
  upNormalizedLeftEigenbasisSurfaceSupplied
    canonicalCKMUpSplittingFieldEigenbasisSurface
  ≡
  true
ckmUpSplittingFieldEigenbasisSurfaceIsSupplied =
  refl

ckmUpOnlyUnitarityDoesNotPromoteCKMUnitarity :
  ckmUnitarityPromoted canonicalCKMUpOnlyUnitarityStaging
  ≡
  false
ckmUpOnlyUnitarityDoesNotPromoteCKMUnitarity =
  refl

------------------------------------------------------------------------
-- Final-local CKM unitarity-residual search.
--
-- The repo-native CKM product carrier remains Matter.MixingMatrix.  Because
-- that carrier is opaque here, this final-local receipt records the completed
-- local search for a residual witness and keeps the proof fail-closed.

data CKMFinalLocalUnitarityResidualComponent : Set where
  consumedMatterMixingMatrixProductAttemptComponent :
    CKMFinalLocalUnitarityResidualComponent

  consumedUpOnlySelfUnitarityStagingComponent :
    CKMFinalLocalUnitarityResidualComponent

  checkedNormalizedUuMatrixTermComponent :
    CKMFinalLocalUnitarityResidualComponent

  checkedNormalizedUdMatrixTermComponent :
    CKMFinalLocalUnitarityResidualComponent

  checkedEntrywiseResidualLawComponent :
    CKMFinalLocalUnitarityResidualComponent

  retainedUnitarityResidualBlockerComponent :
    CKMFinalLocalUnitarityResidualComponent

canonicalCKMFinalLocalUnitarityResidualComponents :
  List CKMFinalLocalUnitarityResidualComponent
canonicalCKMFinalLocalUnitarityResidualComponents =
  consumedMatterMixingMatrixProductAttemptComponent
  ∷ consumedUpOnlySelfUnitarityStagingComponent
  ∷ checkedNormalizedUuMatrixTermComponent
  ∷ checkedNormalizedUdMatrixTermComponent
  ∷ checkedEntrywiseResidualLawComponent
  ∷ retainedUnitarityResidualBlockerComponent
  ∷ []

record CKMFinalLocalUnitarityResidualFailClosedReceipt : Setω where
  field
    productAttemptReceipt :
      CKMMatterMixingMatrixProductClosureAttemptReceipt

    upOnlyUnitarityStaging :
      CKMUpOnlyUnitarityStaging

    finalLocalComponents :
      List CKMFinalLocalUnitarityResidualComponent

    finalLocalComponentsAreCanonical :
      finalLocalComponents
      ≡
      canonicalCKMFinalLocalUnitarityResidualComponents

    productAttemptReachedUnitarityResidual :
      nextArithmeticBlockerAfterProductAttempt productAttemptReceipt
      ≡
      missingUnitarityResidualWitness

    productAttemptHasNoConcreteUuMatrix :
      concreteNormalizedUuMatrixTermSupplied productAttemptReceipt
      ≡
      false

    productAttemptHasNoConcreteUdMatrix :
      concreteNormalizedUdMatrixTermSupplied productAttemptReceipt
      ≡
      false

    productAttemptHasNoProductClosureWitness :
      ckmProductClosureWitnessSupplied productAttemptReceipt
      ≡
      false

    productAttemptHasNoUnitarityResidualWitness :
      unitarityResidualWitnessSupplied productAttemptReceipt
      ≡
      false

    upOnlySelfUnitarityIsStaged :
      upSelfUnitarityStaged upOnlyUnitarityStaging
      ≡
      true

    upOnlyStillRequiresDownEigenbasis :
      downEigenbasisRequiredForCKM upOnlyUnitarityStaging
      ≡
      true

    upOnlyDoesNotPromoteCKMProduct :
      ckmProductClosurePromoted upOnlyUnitarityStaging
      ≡
      false

    entrywiseResidualLawCarrier :
      Set

    entrywiseResidualLawCarrierIsLocalSurface :
      entrywiseResidualLawCarrier ≡ ⊤

    entrywiseResidualLawSupplied :
      Bool

    entrywiseResidualLawSuppliedIsFalse :
      entrywiseResidualLawSupplied ≡ false

    actualUnitarityResidualWitnessSupplied :
      Bool

    actualUnitarityResidualWitnessSuppliedIsFalse :
      actualUnitarityResidualWitnessSupplied ≡ false

    exactVVdaggerResidualReceipt :
      CKMMatterMixingMatrixExactVVdaggerResidualReceipt

    exactVVdaggerResidualReceiptIsCanonical :
      status exactVVdaggerResidualReceipt
      ≡
      concreteWolfensteinVVdaggerResidualComputedNonzero

    exactVVdaggerResidualComputedHere :
      vvDaggerResidualComputed exactVVdaggerResidualReceipt
      ≡
      true

    exactVVdaggerResidualRejectsExactUnitarityHere :
      exactUnitarityForConcreteWolfenstein exactVVdaggerResidualReceipt
      ≡
      false

    finalLocalCKMPromotionClaimed :
      Bool

    finalLocalCKMPromotionClaimedIsFalse :
      finalLocalCKMPromotionClaimed ≡ false

    finalLocalRemainingBlocker :
      CKMArithmeticInputSlot

    finalLocalRemainingBlockerIsUnitarityResidual :
      finalLocalRemainingBlocker
      ≡
      missingUnitarityResidualWitness

    finalLocalBoundary :
      List String

open CKMFinalLocalUnitarityResidualFailClosedReceipt public

canonicalCKMFinalLocalUnitarityResidualFailClosedReceipt :
  CKMFinalLocalUnitarityResidualFailClosedReceipt
canonicalCKMFinalLocalUnitarityResidualFailClosedReceipt =
  record
    { productAttemptReceipt =
        canonicalCKMMatterMixingMatrixProductClosureAttemptReceipt
    ; upOnlyUnitarityStaging =
        canonicalCKMUpOnlyUnitarityStaging
    ; finalLocalComponents =
        canonicalCKMFinalLocalUnitarityResidualComponents
    ; finalLocalComponentsAreCanonical =
        refl
    ; productAttemptReachedUnitarityResidual =
        refl
    ; productAttemptHasNoConcreteUuMatrix =
        refl
    ; productAttemptHasNoConcreteUdMatrix =
        refl
    ; productAttemptHasNoProductClosureWitness =
        refl
    ; productAttemptHasNoUnitarityResidualWitness =
        refl
    ; upOnlySelfUnitarityIsStaged =
        refl
    ; upOnlyStillRequiresDownEigenbasis =
        refl
    ; upOnlyDoesNotPromoteCKMProduct =
        refl
    ; entrywiseResidualLawCarrier =
        ⊤
    ; entrywiseResidualLawCarrierIsLocalSurface =
        refl
    ; entrywiseResidualLawSupplied =
        false
    ; entrywiseResidualLawSuppliedIsFalse =
        refl
    ; actualUnitarityResidualWitnessSupplied =
        false
    ; actualUnitarityResidualWitnessSuppliedIsFalse =
        refl
    ; exactVVdaggerResidualReceipt =
        canonicalCKMMatterMixingMatrixExactVVdaggerResidualReceipt
    ; exactVVdaggerResidualReceiptIsCanonical =
        refl
    ; exactVVdaggerResidualComputedHere =
        refl
    ; exactVVdaggerResidualRejectsExactUnitarityHere =
        refl
    ; finalLocalCKMPromotionClaimed =
        false
    ; finalLocalCKMPromotionClaimedIsFalse =
        refl
    ; finalLocalRemainingBlocker =
        missingUnitarityResidualWitness
    ; finalLocalRemainingBlockerIsUnitarityResidual =
        refl
    ; finalLocalBoundary =
        "The final-local CKM pass consumes the Matter.MixingMatrix product attempt and the U_u self-unitarity staging"
        ∷ "No concrete normalized U_u or U_d matrix term is available behind Matter.MixingMatrix"
        ∷ "No entrywise residual law for V V^dagger = I is present in this lane"
        ∷ "The concrete Wolfenstein residual receipt is still recorded separately as nonzero, not as exact unitarity"
        ∷ "The exact local blocker remains missingUnitarityResidualWitness"
        ∷ "No numeric CKM matrix, field-value proof, or carrier-mixing theorem is introduced"
        ∷ []
    }

ckmFinalLocalUnitarityResidualSearchFailsClosed :
  actualUnitarityResidualWitnessSupplied
    canonicalCKMFinalLocalUnitarityResidualFailClosedReceipt
  ≡
  false
ckmFinalLocalUnitarityResidualSearchFailsClosed =
  refl

ckmFinalLocalUnitarityResidualStillBlocks :
  finalLocalRemainingBlocker
    canonicalCKMFinalLocalUnitarityResidualFailClosedReceipt
  ≡
  missingUnitarityResidualWitness
ckmFinalLocalUnitarityResidualStillBlocks =
  refl

ckmFinalLocalUnitarityResidualDoesNotPromoteCKM :
  finalLocalCKMPromotionClaimed
    canonicalCKMFinalLocalUnitarityResidualFailClosedReceipt
  ≡
  false
ckmFinalLocalUnitarityResidualDoesNotPromoteCKM =
  refl

ckmFinalLocalExactVVdaggerResidualComputed :
  vvDaggerResidualComputed
    (exactVVdaggerResidualReceipt
      canonicalCKMFinalLocalUnitarityResidualFailClosedReceipt)
  ≡
  true
ckmFinalLocalExactVVdaggerResidualComputed =
  refl

ckmFinalLocalExactVVdaggerResidualRejectsExactUnitarity :
  exactUnitarityForConcreteWolfenstein
    (exactVVdaggerResidualReceipt
      canonicalCKMFinalLocalUnitarityResidualFailClosedReceipt)
  ≡
  false
ckmFinalLocalExactVVdaggerResidualRejectsExactUnitarity =
  refl

------------------------------------------------------------------------
-- Gate 7 / l1 exact arithmetic frontier.
--
-- This receipt records the honest end of the local exact arithmetic lane.
-- The concrete staged up/down carriers and entry certificates are consumed,
-- but the CKM product and unitarity residual still depend on the opaque
-- Matter.MixingMatrix targets for real U_u, U_d, and V_CKM.

data CKMGate7L1ExactArithmeticFrontierComponent : Set where
  consumedConcreteDownYukawa3x3MatrixComponent :
    CKMGate7L1ExactArithmeticFrontierComponent

  consumedEntryFieldMembershipCertificatesComponent :
    CKMGate7L1ExactArithmeticFrontierComponent

  consumedHermitianSpectralArithmeticComponent :
    CKMGate7L1ExactArithmeticFrontierComponent

  retainedMatterMixingMatrixUuDependencyComponent :
    CKMGate7L1ExactArithmeticFrontierComponent

  retainedMatterMixingMatrixUdDependencyComponent :
    CKMGate7L1ExactArithmeticFrontierComponent

  retainedMatterMixingMatrixVCkmDependencyComponent :
    CKMGate7L1ExactArithmeticFrontierComponent

  retainedCKMProductClosureWitnessBlockerComponent :
    CKMGate7L1ExactArithmeticFrontierComponent

  retainedUnitarityResidualWitnessBlockerComponent :
    CKMGate7L1ExactArithmeticFrontierComponent

  retainedVHiggsAdapter4BoundaryComponent :
    CKMGate7L1ExactArithmeticFrontierComponent

canonicalCKMGate7L1ExactArithmeticFrontierComponents :
  List CKMGate7L1ExactArithmeticFrontierComponent
canonicalCKMGate7L1ExactArithmeticFrontierComponents =
  consumedConcreteDownYukawa3x3MatrixComponent
  ∷ consumedEntryFieldMembershipCertificatesComponent
  ∷ consumedHermitianSpectralArithmeticComponent
  ∷ retainedMatterMixingMatrixUuDependencyComponent
  ∷ retainedMatterMixingMatrixUdDependencyComponent
  ∷ retainedMatterMixingMatrixVCkmDependencyComponent
  ∷ retainedCKMProductClosureWitnessBlockerComponent
  ∷ retainedUnitarityResidualWitnessBlockerComponent
  ∷ retainedVHiggsAdapter4BoundaryComponent
  ∷ []

record CKMGate7L1ExactArithmeticFrontierReceipt : Setω where
  field
    frontierComponents :
      List CKMGate7L1ExactArithmeticFrontierComponent

    frontierComponentsAreCanonical :
      frontierComponents
      ≡
      canonicalCKMGate7L1ExactArithmeticFrontierComponents

    downMatrixAssemblyReceipt :
      CKMConcreteDownYukawaMatrixAssemblyReceipt

    downMatrixAssemblySuppliesConcreteDown3x3 :
      concreteDownYukawa3x3MatrixSupplied
        (stagedDownMatrixProgress downMatrixAssemblyReceipt)
      ≡
      true

    entryMembershipReceipt :
      CKMEntryFieldMembershipCertificateReceipt

    entryMembershipCertificatesSuppliedAtFrontier :
      entryFieldMembershipCertificatesSupplied entryMembershipReceipt
      ≡
      true

    symbolicSpectralArithmeticReceipt :
      CKMSymbolicYukawaSpectralArithmeticReceipt

    symbolicSpectralArithmeticBlocksAtProductClosure :
      firstRemainingArithmeticBlocker symbolicSpectralArithmeticReceipt
      ≡
      missingCKMProductClosureWitness

    matterMixingMatrixProductAttemptReceipt :
      CKMMatterMixingMatrixProductClosureAttemptReceipt

    frontierUuCarrier :
      Set

    frontierUuCarrierIsMatterMixingMatrix :
      frontierUuCarrier ≡ Matter.MixingMatrix

    frontierUdCarrier :
      Set

    frontierUdCarrierIsMatterMixingMatrix :
      frontierUdCarrier ≡ Matter.MixingMatrix

    frontierVCkmCarrier :
      Set

    frontierVCkmCarrierIsMatterMixingMatrix :
      frontierVCkmCarrier ≡ Matter.MixingMatrix

    frontierCKMProductFormula :
      String

    frontierCKMProductFormula-v :
      frontierCKMProductFormula ≡ "V_CKM = U_u^dagger * U_d"

    ckmProductClosureWitnessSuppliedAtFrontier :
      ckmProductClosureWitnessSupplied
        matterMixingMatrixProductAttemptReceipt
      ≡
      false

    matterMixingMatrixProductAttemptAdvancesToUnitarityResidual :
      nextArithmeticBlockerAfterProductAttempt
        matterMixingMatrixProductAttemptReceipt
      ≡
      missingUnitarityResidualWitness

    finalLocalUnitarityResidualReceipt :
      CKMFinalLocalUnitarityResidualFailClosedReceipt

    unitarityResidualWitnessSuppliedAtFrontier :
      actualUnitarityResidualWitnessSupplied
        finalLocalUnitarityResidualReceipt
      ≡
      false

    finalLocalRemainingBlockerIsUnitarityResidual :
      finalLocalRemainingBlocker finalLocalUnitarityResidualReceipt
      ≡
      missingUnitarityResidualWitness

    vHiggsAdapter4BoundaryRetained :
      vHiggsAdapter4Boundary canonicalCKMUpFactorVecToYukawaEntryMapProgress
      ≡
      true

    physicalYukawaNormalizationPromoted :
      Bool

    physicalYukawaNormalizationPromotedIsFalse :
      physicalYukawaNormalizationPromoted ≡ false

    ckmTheoremPromotedHere :
      Bool

    ckmTheoremPromotedHereIsFalse :
      ckmTheoremPromotedHere ≡ false

    frontierBoundary :
      List String

open CKMGate7L1ExactArithmeticFrontierReceipt public

canonicalCKMGate7L1ExactArithmeticFrontierReceipt :
  CKMGate7L1ExactArithmeticFrontierReceipt
canonicalCKMGate7L1ExactArithmeticFrontierReceipt =
  record
    { frontierComponents =
        canonicalCKMGate7L1ExactArithmeticFrontierComponents
    ; frontierComponentsAreCanonical =
        refl
    ; downMatrixAssemblyReceipt =
        canonicalCKMConcreteDownYukawaMatrixAssemblyReceipt
    ; downMatrixAssemblySuppliesConcreteDown3x3 =
        refl
    ; entryMembershipReceipt =
        canonicalCKMEntryFieldMembershipCertificateReceipt
    ; entryMembershipCertificatesSuppliedAtFrontier =
        refl
    ; symbolicSpectralArithmeticReceipt =
        canonicalCKMSymbolicYukawaSpectralArithmeticReceipt
    ; symbolicSpectralArithmeticBlocksAtProductClosure =
        refl
    ; matterMixingMatrixProductAttemptReceipt =
        canonicalCKMMatterMixingMatrixProductClosureAttemptReceipt
    ; frontierUuCarrier =
        Matter.MixingMatrix
    ; frontierUuCarrierIsMatterMixingMatrix =
        refl
    ; frontierUdCarrier =
        Matter.MixingMatrix
    ; frontierUdCarrierIsMatterMixingMatrix =
        refl
    ; frontierVCkmCarrier =
        Matter.MixingMatrix
    ; frontierVCkmCarrierIsMatterMixingMatrix =
        refl
    ; frontierCKMProductFormula =
        "V_CKM = U_u^dagger * U_d"
    ; frontierCKMProductFormula-v =
        refl
    ; ckmProductClosureWitnessSuppliedAtFrontier =
        refl
    ; matterMixingMatrixProductAttemptAdvancesToUnitarityResidual =
        refl
    ; finalLocalUnitarityResidualReceipt =
        canonicalCKMFinalLocalUnitarityResidualFailClosedReceipt
    ; unitarityResidualWitnessSuppliedAtFrontier =
        refl
    ; finalLocalRemainingBlockerIsUnitarityResidual =
        refl
    ; vHiggsAdapter4BoundaryRetained =
        refl
    ; physicalYukawaNormalizationPromoted =
        false
    ; physicalYukawaNormalizationPromotedIsFalse =
        refl
    ; ckmTheoremPromotedHere =
        false
    ; ckmTheoremPromotedHereIsFalse =
        refl
    ; frontierBoundary =
        "Gate7/l1 consumes the local concrete down Yukawa 3x3 assembly and exact entry-field membership receipts"
        ∷ "The local exact frontier is now the repo-native Matter.MixingMatrix carrier for U_u, U_d, and V_CKM"
        ∷ "No concrete normalized U_u or U_d matrix term is available behind Matter.MixingMatrix"
        ∷ "missingCKMProductClosureWitness remains the product-closure blocker before the fail-closed product attempt"
        ∷ "missingUnitarityResidualWitness remains the residual blocker after the product attempt"
        ∷ "vHiggsAdapter4Boundary is retained; no physical Yukawa normalization or CKM theorem promotion is introduced"
        ∷ []
    }

ckmGate7L1FrontierUsesMatterMixingMatrixForVCkm :
  frontierVCkmCarrier canonicalCKMGate7L1ExactArithmeticFrontierReceipt
  ≡
  Matter.MixingMatrix
ckmGate7L1FrontierUsesMatterMixingMatrixForVCkm =
  refl

ckmGate7L1FrontierKeepsProductClosureWitnessMissing :
  ckmProductClosureWitnessSuppliedAtFrontier
    canonicalCKMGate7L1ExactArithmeticFrontierReceipt
  ≡
  refl
ckmGate7L1FrontierKeepsProductClosureWitnessMissing =
  refl

ckmGate7L1FrontierKeepsUnitarityResidualMissing :
  unitarityResidualWitnessSuppliedAtFrontier
    canonicalCKMGate7L1ExactArithmeticFrontierReceipt
  ≡
  refl
ckmGate7L1FrontierKeepsUnitarityResidualMissing =
  refl

ckmGate7L1FrontierCarriesExactVVdaggerResidualReceipt :
  exactVVdaggerResidualReceipt
    (finalLocalUnitarityResidualReceipt
      canonicalCKMGate7L1ExactArithmeticFrontierReceipt)
  ≡
  canonicalCKMMatterMixingMatrixExactVVdaggerResidualReceipt
ckmGate7L1FrontierCarriesExactVVdaggerResidualReceipt =
  refl

------------------------------------------------------------------------
-- m5/m6/l1 exact down-entry and final arithmetic attempt receipt.
--
-- This final local layer pairs the already staged up-entry certificate surface
-- with an explicit down-entry certificate surface.  It only records exact
-- staged FN exponent arithmetic over the current FactorVec witness; physical
-- Higgs normalization, CKM product closure, and unitarity residual promotion
-- remain fail-closed.

data CKMDownEntryFieldCertificateSlot : Set where
  downY11EntryFieldCertificate :
    CKMDownEntryFieldCertificateSlot
  downY12EntryFieldCertificate :
    CKMDownEntryFieldCertificateSlot
  downY13EntryFieldCertificate :
    CKMDownEntryFieldCertificateSlot
  downY21EntryFieldCertificate :
    CKMDownEntryFieldCertificateSlot
  downY22EntryFieldCertificate :
    CKMDownEntryFieldCertificateSlot
  downY23EntryFieldCertificate :
    CKMDownEntryFieldCertificateSlot
  downY31EntryFieldCertificate :
    CKMDownEntryFieldCertificateSlot
  downY32EntryFieldCertificate :
    CKMDownEntryFieldCertificateSlot
  downY33EntryFieldCertificate :
    CKMDownEntryFieldCertificateSlot

canonicalCKMDownEntryFieldCertificateSlots :
  List CKMDownEntryFieldCertificateSlot
canonicalCKMDownEntryFieldCertificateSlots =
  downY11EntryFieldCertificate
  ∷ downY12EntryFieldCertificate
  ∷ downY13EntryFieldCertificate
  ∷ downY21EntryFieldCertificate
  ∷ downY22EntryFieldCertificate
  ∷ downY23EntryFieldCertificate
  ∷ downY31EntryFieldCertificate
  ∷ downY32EntryFieldCertificate
  ∷ downY33EntryFieldCertificate
  ∷ []

record CKMExactDownEntryFieldCertificateSurface : Setω where
  field
    downEntryFieldCertificateVector :
      GL.FactorVec

    downEntryFieldCertificateVectorIsCanonical :
      downEntryFieldCertificateVector
      ≡
      canonicalYukawaFNExponentWitnessVector

    downEntryFieldCertificateSlots :
      List CKMDownEntryFieldCertificateSlot

    downEntryFieldCertificateSlotsAreCanonical :
      downEntryFieldCertificateSlots
      ≡
      canonicalCKMDownEntryFieldCertificateSlots

    downEntryField :
      CKMEntryField

    downEntryFieldIsRationalQ :
      downEntryField ≡ rationalQ

    downY11FieldExponentIsOne :
      factorVecToDownYukawaFNExponent
        missingY11
        downEntryFieldCertificateVector
      ≡
      one

    downY12FieldExponentIsTwo :
      factorVecToDownYukawaFNExponent
        missingY12
        downEntryFieldCertificateVector
      ≡
      two

    downY13FieldExponentIsZero :
      factorVecToDownYukawaFNExponent
        missingY13
        downEntryFieldCertificateVector
      ≡
      zero

    downY21FieldExponentIsThree :
      factorVecToDownYukawaFNExponent
        missingY21
        downEntryFieldCertificateVector
      ≡
      three

    downY22FieldExponentIsTwo :
      factorVecToDownYukawaFNExponent
        missingY22
        downEntryFieldCertificateVector
      ≡
      two

    downY23FieldExponentIsTwo :
      factorVecToDownYukawaFNExponent
        missingY23
        downEntryFieldCertificateVector
      ≡
      two

    downY31FieldExponentIsThree :
      factorVecToDownYukawaFNExponent
        missingY31
        downEntryFieldCertificateVector
      ≡
      three

    downY32FieldExponentIsOne :
      factorVecToDownYukawaFNExponent
        missingY32
        downEntryFieldCertificateVector
      ≡
      one

    downY33FieldExponentIsThree :
      factorVecToDownYukawaFNExponent
        missingY33
        downEntryFieldCertificateVector
      ≡
      three

    downY22GeorgiJarlskogSocketRetained :
      yukawaEntryGeorgiJarlskogY22Socket
        (factorVecToStagedDownYukawaEntryMap
          downEntryFieldCertificateVector
          missingY22)
      ≡
      true

    downEntryMembershipCertificatesSupplied :
      Bool

    downEntryMembershipCertificatesSuppliedIsTrue :
      downEntryMembershipCertificatesSupplied ≡ true

    vHiggsAdapter4Boundary :
      Bool

    vHiggsAdapter4BoundaryIsTrue :
      vHiggsAdapter4Boundary ≡ true

    physicalUnitPromotionClaimed :
      Bool

    physicalUnitPromotionClaimedIsFalse :
      physicalUnitPromotionClaimed ≡ false

    downEntryFieldCertificateBoundary :
      List String

open CKMExactDownEntryFieldCertificateSurface public

canonicalCKMExactDownEntryFieldCertificateSurface :
  CKMExactDownEntryFieldCertificateSurface
canonicalCKMExactDownEntryFieldCertificateSurface =
  record
    { downEntryFieldCertificateVector =
        canonicalYukawaFNExponentWitnessVector
    ; downEntryFieldCertificateVectorIsCanonical =
        refl
    ; downEntryFieldCertificateSlots =
        canonicalCKMDownEntryFieldCertificateSlots
    ; downEntryFieldCertificateSlotsAreCanonical =
        refl
    ; downEntryField =
        rationalQ
    ; downEntryFieldIsRationalQ =
        refl
    ; downY11FieldExponentIsOne =
        refl
    ; downY12FieldExponentIsTwo =
        refl
    ; downY13FieldExponentIsZero =
        refl
    ; downY21FieldExponentIsThree =
        refl
    ; downY22FieldExponentIsTwo =
        refl
    ; downY23FieldExponentIsTwo =
        refl
    ; downY31FieldExponentIsThree =
        refl
    ; downY32FieldExponentIsOne =
        refl
    ; downY33FieldExponentIsThree =
        refl
    ; downY22GeorgiJarlskogSocketRetained =
        refl
    ; downEntryMembershipCertificatesSupplied =
        true
    ; downEntryMembershipCertificatesSuppliedIsTrue =
        refl
    ; vHiggsAdapter4Boundary =
        true
    ; vHiggsAdapter4BoundaryIsTrue =
        refl
    ; physicalUnitPromotionClaimed =
        false
    ; physicalUnitPromotionClaimedIsFalse =
        refl
    ; downEntryFieldCertificateBoundary =
        "All nine U_d exponent entries have exact rational entry-field certificates for the canonical witness vector"
        ∷ "The certified exponent row is 1,2,0 / 3,2,2 / 3,1,3"
        ∷ "The down y22 Georgi-Jarlskog socket is retained as staged arithmetic only"
        ∷ "The certificate is exponent-level only: v_Higgs remains Adapter 4 and no physical-unit normalization is promoted"
        ∷ []
    }

data CKMGate7L1ExactArithmeticAttemptComponent : Set where
  consumedExactUpEntryCertificateSurfaceComponent :
    CKMGate7L1ExactArithmeticAttemptComponent

  consumedExactDownEntryCertificateSurfaceComponent :
    CKMGate7L1ExactArithmeticAttemptComponent

  consumedHermitianProductMatrixReceiptComponent :
    CKMGate7L1ExactArithmeticAttemptComponent

  stagedCharacteristicSplittingEigenbasisQueueComponent :
    CKMGate7L1ExactArithmeticAttemptComponent

  stagedMatterMixingMatrixProductAttemptComponent :
    CKMGate7L1ExactArithmeticAttemptComponent

  retainedUnitarityResidualWitnessBlockerComponent :
    CKMGate7L1ExactArithmeticAttemptComponent

  retainedVHiggsAdapter4BoundaryComponent :
    CKMGate7L1ExactArithmeticAttemptComponent

canonicalCKMGate7L1ExactArithmeticAttemptComponents :
  List CKMGate7L1ExactArithmeticAttemptComponent
canonicalCKMGate7L1ExactArithmeticAttemptComponents =
  consumedExactUpEntryCertificateSurfaceComponent
  ∷ consumedExactDownEntryCertificateSurfaceComponent
  ∷ consumedHermitianProductMatrixReceiptComponent
  ∷ stagedCharacteristicSplittingEigenbasisQueueComponent
  ∷ stagedMatterMixingMatrixProductAttemptComponent
  ∷ retainedUnitarityResidualWitnessBlockerComponent
  ∷ retainedVHiggsAdapter4BoundaryComponent
  ∷ []

record CKMGate7L1ExactArithmeticAttemptReceipt : Setω where
  field
    exactArithmeticAttemptComponents :
      List CKMGate7L1ExactArithmeticAttemptComponent

    exactArithmeticAttemptComponentsAreCanonical :
      exactArithmeticAttemptComponents
      ≡
      canonicalCKMGate7L1ExactArithmeticAttemptComponents

    exactUpEntryFieldCertificateSurface :
      CKMExactUpEntryFieldCertificateSurface

    exactUpEntryMembershipCertificatesSupplied :
      upEntryMembershipCertificatesSupplied
        exactUpEntryFieldCertificateSurface
      ≡
      true

    exactDownEntryFieldCertificateSurface :
      CKMExactDownEntryFieldCertificateSurface

    exactDownEntryMembershipCertificatesSupplied :
      downEntryMembershipCertificatesSupplied
        exactDownEntryFieldCertificateSurface
      ≡
      true

    hermitianProductMatrixReceipt :
      CKMHermitianProductMatrixReceipt

    hermitianProductMatricesSuppliedAtAttempt :
      hermitianProductMatricesSupplied hermitianProductMatrixReceipt
      ≡
      true

    symbolicSpectralArithmeticReceipt :
      CKMSymbolicYukawaSpectralArithmeticReceipt

    characteristicSplittingEigenbasisQueueBlocksAtProductClosure :
      firstRemainingArithmeticBlocker symbolicSpectralArithmeticReceipt
      ≡
      missingCKMProductClosureWitness

    matterMixingMatrixProductAttemptReceipt :
      CKMMatterMixingMatrixProductClosureAttemptReceipt

    attemptUuCarrier :
      Set

    attemptUuCarrierIsMatterMixingMatrix :
      attemptUuCarrier ≡ Matter.MixingMatrix

    attemptUdCarrier :
      Set

    attemptUdCarrierIsMatterMixingMatrix :
      attemptUdCarrier ≡ Matter.MixingMatrix

    attemptVCkmCarrier :
      Set

    attemptVCkmCarrierIsMatterMixingMatrix :
      attemptVCkmCarrier ≡ Matter.MixingMatrix

    attemptCKMProductFormula :
      String

    attemptCKMProductFormula-v :
      attemptCKMProductFormula ≡ "V_CKM = U_u^dagger * U_d"

    productClosureWitnessSuppliedAtAttempt :
      ckmProductClosureWitnessSupplied
        matterMixingMatrixProductAttemptReceipt
      ≡
      false

    unitarityResidualWitnessSuppliedAtAttempt :
      unitarityResidualWitnessSupplied
        matterMixingMatrixProductAttemptReceipt
      ≡
      false

    finalLocalUnitarityResidualReceipt :
      CKMFinalLocalUnitarityResidualFailClosedReceipt

    finalLocalResidualWitnessStillMissingAtAttempt :
      actualUnitarityResidualWitnessSupplied
        finalLocalUnitarityResidualReceipt
      ≡
      false

    vHiggsAdapter4BoundaryRetainedAtAttempt :
      vHiggsAdapter4Boundary exactDownEntryFieldCertificateSurface
      ≡
      true

    physicalYukawaNormalizationPromotedAtAttempt :
      Bool

    physicalYukawaNormalizationPromotedAtAttemptIsFalse :
      physicalYukawaNormalizationPromotedAtAttempt ≡ false

    exactArithmeticAttemptPromotesCKM :
      Bool

    exactArithmeticAttemptPromotesCKMIsFalse :
      exactArithmeticAttemptPromotesCKM ≡ false

    exactArithmeticAttemptBoundary :
      List String

open CKMGate7L1ExactArithmeticAttemptReceipt public

canonicalCKMGate7L1ExactArithmeticAttemptReceipt :
  CKMGate7L1ExactArithmeticAttemptReceipt
canonicalCKMGate7L1ExactArithmeticAttemptReceipt =
  record
    { exactArithmeticAttemptComponents =
        canonicalCKMGate7L1ExactArithmeticAttemptComponents
    ; exactArithmeticAttemptComponentsAreCanonical =
        refl
    ; exactUpEntryFieldCertificateSurface =
        canonicalCKMExactUpEntryFieldCertificateSurface
    ; exactUpEntryMembershipCertificatesSupplied =
        refl
    ; exactDownEntryFieldCertificateSurface =
        canonicalCKMExactDownEntryFieldCertificateSurface
    ; exactDownEntryMembershipCertificatesSupplied =
        refl
    ; hermitianProductMatrixReceipt =
        canonicalCKMHermitianProductMatrixReceipt
    ; hermitianProductMatricesSuppliedAtAttempt =
        refl
    ; symbolicSpectralArithmeticReceipt =
        canonicalCKMSymbolicYukawaSpectralArithmeticReceipt
    ; characteristicSplittingEigenbasisQueueBlocksAtProductClosure =
        refl
    ; matterMixingMatrixProductAttemptReceipt =
        canonicalCKMMatterMixingMatrixProductClosureAttemptReceipt
    ; attemptUuCarrier =
        Matter.MixingMatrix
    ; attemptUuCarrierIsMatterMixingMatrix =
        refl
    ; attemptUdCarrier =
        Matter.MixingMatrix
    ; attemptUdCarrierIsMatterMixingMatrix =
        refl
    ; attemptVCkmCarrier =
        Matter.MixingMatrix
    ; attemptVCkmCarrierIsMatterMixingMatrix =
        refl
    ; attemptCKMProductFormula =
        "V_CKM = U_u^dagger * U_d"
    ; attemptCKMProductFormula-v =
        refl
    ; productClosureWitnessSuppliedAtAttempt =
        refl
    ; unitarityResidualWitnessSuppliedAtAttempt =
        refl
    ; finalLocalUnitarityResidualReceipt =
        canonicalCKMFinalLocalUnitarityResidualFailClosedReceipt
    ; finalLocalResidualWitnessStillMissingAtAttempt =
        refl
    ; vHiggsAdapter4BoundaryRetainedAtAttempt =
        refl
    ; physicalYukawaNormalizationPromotedAtAttempt =
        false
    ; physicalYukawaNormalizationPromotedAtAttemptIsFalse =
        refl
    ; exactArithmeticAttemptPromotesCKM =
        false
    ; exactArithmeticAttemptPromotesCKMIsFalse =
        refl
    ; exactArithmeticAttemptBoundary =
        "m5/m6/l1 exact arithmetic consumes up and down staged entry-field certificates"
        ∷ "Hermitian products and characteristic/splitting/eigenbasis staging are typechecked receipts, not physical diagonalization theorems"
        ∷ "The CKM product attempt uses Matter.MixingMatrix for U_u, U_d, and V_CKM with formula V_CKM = U_u^dagger * U_d"
        ∷ "Product closure and unitarity residual witnesses remain missing after the fail-closed Matter.MixingMatrix attempt"
        ∷ "vHiggsAdapter4Boundary remains retained; no physical Yukawa normalization or CKM promotion is introduced"
        ∷ []
    }

ckmExactDownEntryFieldCertificatesAreSupplied :
  downEntryMembershipCertificatesSupplied
    canonicalCKMExactDownEntryFieldCertificateSurface
  ≡
  true
ckmExactDownEntryFieldCertificatesAreSupplied =
  refl

ckmGate7L1ExactArithmeticAttemptUsesMatterMixingMatrix :
  attemptVCkmCarrier canonicalCKMGate7L1ExactArithmeticAttemptReceipt
  ≡
  Matter.MixingMatrix
ckmGate7L1ExactArithmeticAttemptUsesMatterMixingMatrix =
  refl

ckmGate7L1ExactArithmeticAttemptKeepsUnitarityResidualMissing :
  finalLocalResidualWitnessStillMissingAtAttempt
    canonicalCKMGate7L1ExactArithmeticAttemptReceipt
  ≡
  refl
ckmGate7L1ExactArithmeticAttemptKeepsUnitarityResidualMissing =
  refl

ckmGate7L1ExactArithmeticAttemptDoesNotPromote :
  exactArithmeticAttemptPromotesCKM
    canonicalCKMGate7L1ExactArithmeticAttemptReceipt
  ≡
  false
ckmGate7L1ExactArithmeticAttemptDoesNotPromote =
  refl

------------------------------------------------------------------------
-- Next-wave explicit FN charge table and exponent ledger.
--
-- This receipt names the finite FN charge slots used by the staged up/down
-- exponent rows.  It is a bookkeeping surface over the existing executable
-- exponent functions, not a physical Yukawa texture or Higgs-normalized mass
-- theorem.

data CKMFNChargeTableSlot : Set where
  fnLeftQuarkQ1FromP11 :
    CKMFNChargeTableSlot
  fnLeftQuarkQ2FromP23 :
    CKMFNChargeTableSlot
  fnLeftQuarkQ3FromP47 :
    CKMFNChargeTableSlot
  fnRightUpU1FromP13 :
    CKMFNChargeTableSlot
  fnRightUpU2FromP29 :
    CKMFNChargeTableSlot
  fnRightUpU3FromP59 :
    CKMFNChargeTableSlot
  fnRightDownD1FromP17 :
    CKMFNChargeTableSlot
  fnRightDownD2FromP31 :
    CKMFNChargeTableSlot
  fnRightDownD3FromP71 :
    CKMFNChargeTableSlot
  fnDownHiggsSocketFromP41 :
    CKMFNChargeTableSlot
  fnHiggsNormalisationAdapter4 :
    CKMFNChargeTableSlot

canonicalCKMFNChargeTableSlots :
  List CKMFNChargeTableSlot
canonicalCKMFNChargeTableSlots =
  fnLeftQuarkQ1FromP11
  ∷ fnLeftQuarkQ2FromP23
  ∷ fnLeftQuarkQ3FromP47
  ∷ fnRightUpU1FromP13
  ∷ fnRightUpU2FromP29
  ∷ fnRightUpU3FromP59
  ∷ fnRightDownD1FromP17
  ∷ fnRightDownD2FromP31
  ∷ fnRightDownD3FromP71
  ∷ fnDownHiggsSocketFromP41
  ∷ fnHiggsNormalisationAdapter4
  ∷ []

record CKMExplicitFNChargeTableExponentReceipt : Setω where
  field
    matterYukawaFNReceipt :
      Matter.MatterPrimeLaneYukawaFNReceipt

    matterFNValuationTargetRecorded :
      Matter.fnValuationTargetRecorded matterYukawaFNReceipt
      ≡
      true

    matterHiggsChargeNormalisationStillAdapter4 :
      Matter.higgsChargeNormalisationAdapter4 matterYukawaFNReceipt
      ≡
      true

    matterTopYukawaHiggsChargeInconsistencyOpen :
      Matter.topYukawaHiggsChargeInconsistencyOpen matterYukawaFNReceipt
      ≡
      true

    explicitFNChargeTableSlots :
      List CKMFNChargeTableSlot

    explicitFNChargeTableSlotsAreCanonical :
      explicitFNChargeTableSlots
      ≡
      canonicalCKMFNChargeTableSlots

    matterFNChargeSlots :
      List Matter.FroggattNielsenChargeSlot

    matterFNChargeSlotsAreCanonical :
      matterFNChargeSlots
      ≡
      Matter.canonicalFroggattNielsenChargeSlots

    upExponentCertificateSurface :
      CKMExactUpEntryFieldCertificateSurface

    upExponentRowIsOneTwoThreeThreeFourFiveOneTwoOne :
      upEntryFieldCertificateBoundary upExponentCertificateSurface
      ≡
      upEntryFieldCertificateBoundary
        canonicalCKMExactUpEntryFieldCertificateSurface

    downExponentCertificateSurface :
      CKMExactDownEntryFieldCertificateSurface

    downExponentRowIsOneTwoZeroThreeTwoTwoThreeOneThree :
      downEntryFieldCertificateBoundary downExponentCertificateSurface
      ≡
      downEntryFieldCertificateBoundary
        canonicalCKMExactDownEntryFieldCertificateSurface

    georgiJarlskogRelations :
      List Matter.GeorgiJarlskogRelationLabel

    georgiJarlskogRelationsAreCanonical :
      georgiJarlskogRelations
      ≡
      Matter.canonicalGeorgiJarlskogRelationLabels

    downY22GeorgiJarlskogSocketRetainedHere :
      yukawaEntryGeorgiJarlskogY22Socket
        (factorVecToStagedDownYukawaEntryMap
          (downEntryFieldCertificateVector downExponentCertificateSurface)
          missingY22)
      ≡
      true

    symbolicCharacteristicPolynomialStaged :
      Bool

    symbolicCharacteristicPolynomialStagedIsTrue :
      symbolicCharacteristicPolynomialStaged ≡ true

    symbolicSplittingFieldEigenbasisStaged :
      Bool

    symbolicSplittingFieldEigenbasisStagedIsTrue :
      symbolicSplittingFieldEigenbasisStaged ≡ true

    physicalYukawaTexturePromoted :
      Bool

    physicalYukawaTexturePromotedIsFalse :
      physicalYukawaTexturePromoted ≡ false

    retainedProductClosureBlocker :
      CKMArithmeticInputSlot

    retainedProductClosureBlockerIsMissingCKMProductClosureWitness :
      retainedProductClosureBlocker
      ≡
      missingCKMProductClosureWitness

    retainedUnitarityResidualBlocker :
      CKMArithmeticInputSlot

    retainedUnitarityResidualBlockerIsMissingUnitarityResidualWitness :
      retainedUnitarityResidualBlocker
      ≡
      missingUnitarityResidualWitness

    explicitFNChargeTableBoundary :
      List String

open CKMExplicitFNChargeTableExponentReceipt public

canonicalCKMExplicitFNChargeTableExponentReceipt :
  CKMExplicitFNChargeTableExponentReceipt
canonicalCKMExplicitFNChargeTableExponentReceipt =
  record
    { matterYukawaFNReceipt =
        Matter.canonicalMatterPrimeLaneYukawaFNReceipt
    ; matterFNValuationTargetRecorded =
        refl
    ; matterHiggsChargeNormalisationStillAdapter4 =
        refl
    ; matterTopYukawaHiggsChargeInconsistencyOpen =
        refl
    ; explicitFNChargeTableSlots =
        canonicalCKMFNChargeTableSlots
    ; explicitFNChargeTableSlotsAreCanonical =
        refl
    ; matterFNChargeSlots =
        Matter.canonicalFroggattNielsenChargeSlots
    ; matterFNChargeSlotsAreCanonical =
        refl
    ; upExponentCertificateSurface =
        canonicalCKMExactUpEntryFieldCertificateSurface
    ; upExponentRowIsOneTwoThreeThreeFourFiveOneTwoOne =
        refl
    ; downExponentCertificateSurface =
        canonicalCKMExactDownEntryFieldCertificateSurface
    ; downExponentRowIsOneTwoZeroThreeTwoTwoThreeOneThree =
        refl
    ; georgiJarlskogRelations =
        Matter.canonicalGeorgiJarlskogRelationLabels
    ; georgiJarlskogRelationsAreCanonical =
        refl
    ; downY22GeorgiJarlskogSocketRetainedHere =
        refl
    ; symbolicCharacteristicPolynomialStaged =
        true
    ; symbolicCharacteristicPolynomialStagedIsTrue =
        refl
    ; symbolicSplittingFieldEigenbasisStaged =
        true
    ; symbolicSplittingFieldEigenbasisStagedIsTrue =
        refl
    ; physicalYukawaTexturePromoted =
        false
    ; physicalYukawaTexturePromotedIsFalse =
        refl
    ; retainedProductClosureBlocker =
        missingCKMProductClosureWitness
    ; retainedProductClosureBlockerIsMissingCKMProductClosureWitness =
        refl
    ; retainedUnitarityResidualBlocker =
        missingUnitarityResidualWitness
    ; retainedUnitarityResidualBlockerIsMissingUnitarityResidualWitness =
        refl
    ; explicitFNChargeTableBoundary =
        "Explicit FN charge table: Q rows use p11,p23,p47; up columns use p13,p29,p59; down columns use p17,p31,p71; down-Higgs socket uses p41"
        ∷ "Canonical up exponent row is 1,2,3 / 3,4,5 / 1,2,1"
        ∷ "Canonical down exponent row is 1,2,0 / 3,2,2 / 3,1,3 with the y22 Georgi-Jarlskog socket retained"
        ∷ "Characteristic-polynomial, splitting-field, and normalized-eigenbasis staging are symbolic only"
        ∷ "missingCKMProductClosureWitness and missingUnitarityResidualWitness remain retained blockers"
        ∷ []
    }

ckmExplicitFNChargeTableKeepsGJDownY22 :
  downY22GeorgiJarlskogSocketRetainedHere
    canonicalCKMExplicitFNChargeTableExponentReceipt
  ≡
  refl
ckmExplicitFNChargeTableKeepsGJDownY22 =
  refl

ckmExplicitFNChargeTableDoesNotPromoteTexture :
  physicalYukawaTexturePromoted
    canonicalCKMExplicitFNChargeTableExponentReceipt
  ≡
  false
ckmExplicitFNChargeTableDoesNotPromoteTexture =
  refl

------------------------------------------------------------------------
-- Next-wave m5 leading-symbolic up-sector Hermitian/characteristic receipt.
--
-- The exact executable row already present in this module is retained above.
-- This receipt records the user's FN leading-symbolic m5 target separately:
-- Yu ~ [[e6,e5,e3],[e5,e4,e2],[e3,e2,1]], so H_u = Yu Yu^dagger
-- has the displayed three-term exponent sums and a symbolic characteristic
-- polynomial with leading trace/minor/determinant exponents.  It is a
-- symbolic surface only and does not replace the repo executable row.

record CKMNextWaveUpHermitianLeadingEntry : Set where
  field
    term1Exponent :
      Nat

    term2Exponent :
      Nat

    term3Exponent :
      Nat

    entryCarrier :
      CKMEntryField

    entryCarrierIsRationalQ :
      entryCarrier ≡ rationalQ

open CKMNextWaveUpHermitianLeadingEntry public

upLeadingEntry :
  Nat →
  Nat →
  Nat →
  CKMNextWaveUpHermitianLeadingEntry
upLeadingEntry a b c =
  record
    { term1Exponent =
        a
    ; term2Exponent =
        b
    ; term3Exponent =
        c
    ; entryCarrier =
        rationalQ
    ; entryCarrierIsRationalQ =
        refl
    }

record CKMNextWaveUpHermitianCharacteristicLeadingReceipt : Setω where
  field
    executableUpCertificateSurface :
      CKMExactUpEntryFieldCertificateSurface

    executableUpCertificateSurfaceRetained :
      upEntryMembershipCertificatesSupplied executableUpCertificateSurface
      ≡
      true

    leadingY11Exponent :
      Nat

    leadingY11ExponentIsSix :
      leadingY11Exponent ≡ 6

    leadingY12Exponent :
      Nat

    leadingY12ExponentIsFive :
      leadingY12Exponent ≡ 5

    leadingY13Exponent :
      Nat

    leadingY13ExponentIsThree :
      leadingY13Exponent ≡ 3

    leadingY22Exponent :
      Nat

    leadingY22ExponentIsFour :
      leadingY22Exponent ≡ 4

    leadingY23Exponent :
      Nat

    leadingY23ExponentIsTwo :
      leadingY23Exponent ≡ 2

    leadingY33Exponent :
      Nat

    leadingY33ExponentIsZero :
      leadingY33Exponent ≡ 0

    h11LeadingTerms :
      CKMNextWaveUpHermitianLeadingEntry

    h12LeadingTerms :
      CKMNextWaveUpHermitianLeadingEntry

    h13LeadingTerms :
      CKMNextWaveUpHermitianLeadingEntry

    h22LeadingTerms :
      CKMNextWaveUpHermitianLeadingEntry

    h23LeadingTerms :
      CKMNextWaveUpHermitianLeadingEntry

    h33LeadingTerms :
      CKMNextWaveUpHermitianLeadingEntry

    traceLeadingConstantTermPresent :
      Bool

    traceLeadingConstantTermPresentIsTrue :
      traceLeadingConstantTermPresent ≡ true

    traceNextLeadingExponent :
      Nat

    traceNextLeadingExponentIsFour :
      traceNextLeadingExponent ≡ 4

    determinantLeadingExponent :
      Nat

    determinantLeadingExponentIsEighteen :
      determinantLeadingExponent ≡ 18

    characteristicPolynomialCarrier :
      CKMEntryField

    characteristicPolynomialCarrierIsRationalQ :
      characteristicPolynomialCarrier ≡ rationalQ

    symbolicUuCarrier :
      Set

    symbolicUuCarrierIsMatterMixingMatrix :
      symbolicUuCarrier ≡ Matter.MixingMatrix

    vHiggsAdapter4BoundaryRetained :
      Bool

    vHiggsAdapter4BoundaryRetainedIsTrue :
      vHiggsAdapter4BoundaryRetained ≡ true

    physicalPromotionClaimed :
      Bool

    physicalPromotionClaimedIsFalse :
      physicalPromotionClaimed ≡ false

    nextBlocker :
      CKMArithmeticInputSlot

    nextBlockerIsCKMProductClosureWitness :
      nextBlocker ≡ missingCKMProductClosureWitness

    boundary :
      List String

open CKMNextWaveUpHermitianCharacteristicLeadingReceipt public

canonicalCKMNextWaveUpHermitianCharacteristicLeadingReceipt :
  CKMNextWaveUpHermitianCharacteristicLeadingReceipt
canonicalCKMNextWaveUpHermitianCharacteristicLeadingReceipt =
  record
    { executableUpCertificateSurface =
        canonicalCKMExactUpEntryFieldCertificateSurface
    ; executableUpCertificateSurfaceRetained =
        refl
    ; leadingY11Exponent =
        6
    ; leadingY11ExponentIsSix =
        refl
    ; leadingY12Exponent =
        5
    ; leadingY12ExponentIsFive =
        refl
    ; leadingY13Exponent =
        3
    ; leadingY13ExponentIsThree =
        refl
    ; leadingY22Exponent =
        4
    ; leadingY22ExponentIsFour =
        refl
    ; leadingY23Exponent =
        2
    ; leadingY23ExponentIsTwo =
        refl
    ; leadingY33Exponent =
        0
    ; leadingY33ExponentIsZero =
        refl
    ; h11LeadingTerms =
        upLeadingEntry 12 10 6
    ; h12LeadingTerms =
        upLeadingEntry 11 9 5
    ; h13LeadingTerms =
        upLeadingEntry 9 7 3
    ; h22LeadingTerms =
        upLeadingEntry 10 8 4
    ; h23LeadingTerms =
        upLeadingEntry 8 6 2
    ; h33LeadingTerms =
        upLeadingEntry 6 4 0
    ; traceLeadingConstantTermPresent =
        true
    ; traceLeadingConstantTermPresentIsTrue =
        refl
    ; traceNextLeadingExponent =
        4
    ; traceNextLeadingExponentIsFour =
        refl
    ; determinantLeadingExponent =
        18
    ; determinantLeadingExponentIsEighteen =
        refl
    ; characteristicPolynomialCarrier =
        rationalQ
    ; characteristicPolynomialCarrierIsRationalQ =
        refl
    ; symbolicUuCarrier =
        Matter.MixingMatrix
    ; symbolicUuCarrierIsMatterMixingMatrix =
        refl
    ; vHiggsAdapter4BoundaryRetained =
        true
    ; vHiggsAdapter4BoundaryRetainedIsTrue =
        refl
    ; physicalPromotionClaimed =
        false
    ; physicalPromotionClaimedIsFalse =
        refl
    ; nextBlocker =
        missingCKMProductClosureWitness
    ; nextBlockerIsCKMProductClosureWitness =
        refl
    ; boundary =
        "m5 leading-symbolic Yu exponents are 6,5,3 / 5,4,2 / 3,2,0"
        ∷ "H_u leading entries are recorded as exponent triples for Yu Yu^dagger"
        ∷ "The symbolic characteristic polynomial records trace leading 1 plus epsilon^4 and determinant leading epsilon^18"
        ∷ "The executable repo row remains retained separately; this does not promote a physical Higgs-normalized matrix"
        ∷ []
    }

ckmNextWaveUpCharacteristicLeadingKeepsProductBlocker :
  nextBlocker canonicalCKMNextWaveUpHermitianCharacteristicLeadingReceipt
  ≡
  missingCKMProductClosureWitness
ckmNextWaveUpCharacteristicLeadingKeepsProductBlocker =
  refl

ckmNextWaveUpCharacteristicLeadingDoesNotPromote :
  physicalPromotionClaimed
    canonicalCKMNextWaveUpHermitianCharacteristicLeadingReceipt
  ≡
  false
ckmNextWaveUpCharacteristicLeadingDoesNotPromote =
  refl

------------------------------------------------------------------------
-- Current-wave concrete leading up-sector characteristic polynomial.
--
-- This is the requested m5 polynomial surface:
--   chi_u(lambda) =
--     lambda^3
--     - (1 + epsilon^4 + epsilon^12) lambda^2
--     + (epsilon^4 + epsilon^12 + epsilon^16) lambda
--     - epsilon^16
--
-- It is concrete at the leading FN-exponent level.  It does not supply the
-- splitting field, normalized eigenbasis, CKM product closure, or physical
-- Higgs normalization.

data CKMLeadingPolynomialCoefficientSign : Set where
  positiveCoefficient :
    CKMLeadingPolynomialCoefficientSign

  negativeCoefficient :
    CKMLeadingPolynomialCoefficientSign

data CKMCurrentWaveUpCharacteristicPolynomialTerm : Set where
  lambdaCubedMonicTerm :
    CKMCurrentWaveUpCharacteristicPolynomialTerm

  lambdaSquaredMinusOneTerm :
    CKMCurrentWaveUpCharacteristicPolynomialTerm

  lambdaSquaredMinusEpsilon4Term :
    CKMCurrentWaveUpCharacteristicPolynomialTerm

  lambdaSquaredMinusEpsilon12Term :
    CKMCurrentWaveUpCharacteristicPolynomialTerm

  lambdaPlusEpsilon4Term :
    CKMCurrentWaveUpCharacteristicPolynomialTerm

  lambdaPlusEpsilon12Term :
    CKMCurrentWaveUpCharacteristicPolynomialTerm

  lambdaPlusEpsilon16Term :
    CKMCurrentWaveUpCharacteristicPolynomialTerm

  constantMinusEpsilon16Term :
    CKMCurrentWaveUpCharacteristicPolynomialTerm

canonicalCKMCurrentWaveUpCharacteristicPolynomialTerms :
  List CKMCurrentWaveUpCharacteristicPolynomialTerm
canonicalCKMCurrentWaveUpCharacteristicPolynomialTerms =
  lambdaCubedMonicTerm
  ∷ lambdaSquaredMinusOneTerm
  ∷ lambdaSquaredMinusEpsilon4Term
  ∷ lambdaSquaredMinusEpsilon12Term
  ∷ lambdaPlusEpsilon4Term
  ∷ lambdaPlusEpsilon12Term
  ∷ lambdaPlusEpsilon16Term
  ∷ constantMinusEpsilon16Term
  ∷ []

record CKMCurrentWaveConcreteUpCharacteristicPolynomialReceipt : Setω where
  field
    priorLeadingHermitianReceipt :
      CKMNextWaveUpHermitianCharacteristicLeadingReceipt

    priorLeadingReceiptRetainsProductBlocker :
      nextBlocker priorLeadingHermitianReceipt
      ≡
      missingCKMProductClosureWitness

    polynomialCarrier :
      CKMEntryField

    polynomialCarrierIsRationalQ :
      polynomialCarrier ≡ rationalQ

    polynomialTerms :
      List CKMCurrentWaveUpCharacteristicPolynomialTerm

    polynomialTermsAreCanonical :
      polynomialTerms
      ≡
      canonicalCKMCurrentWaveUpCharacteristicPolynomialTerms

    lambdaCubedCoefficientSign :
      CKMLeadingPolynomialCoefficientSign

    lambdaCubedCoefficientSignIsPositive :
      lambdaCubedCoefficientSign ≡ positiveCoefficient

    lambdaSquaredConstantExponent :
      Nat

    lambdaSquaredConstantExponentIsZero :
      lambdaSquaredConstantExponent ≡ 0

    lambdaSquaredEpsilon4Exponent :
      Nat

    lambdaSquaredEpsilon4ExponentIsFour :
      lambdaSquaredEpsilon4Exponent ≡ 4

    lambdaSquaredEpsilon12Exponent :
      Nat

    lambdaSquaredEpsilon12ExponentIsTwelve :
      lambdaSquaredEpsilon12Exponent ≡ 12

    lambdaSquaredCoefficientSign :
      CKMLeadingPolynomialCoefficientSign

    lambdaSquaredCoefficientSignIsNegative :
      lambdaSquaredCoefficientSign ≡ negativeCoefficient

    lambdaMinorEpsilon4Exponent :
      Nat

    lambdaMinorEpsilon4ExponentIsFour :
      lambdaMinorEpsilon4Exponent ≡ 4

    lambdaMinorEpsilon12Exponent :
      Nat

    lambdaMinorEpsilon12ExponentIsTwelve :
      lambdaMinorEpsilon12Exponent ≡ 12

    lambdaMinorEpsilon16Exponent :
      Nat

    lambdaMinorEpsilon16ExponentIsSixteen :
      lambdaMinorEpsilon16Exponent ≡ 16

    lambdaMinorCoefficientSign :
      CKMLeadingPolynomialCoefficientSign

    lambdaMinorCoefficientSignIsPositive :
      lambdaMinorCoefficientSign ≡ positiveCoefficient

    constantDeterminantExponent :
      Nat

    constantDeterminantExponentIsSixteen :
      constantDeterminantExponent ≡ 16

    constantDeterminantCoefficientSign :
      CKMLeadingPolynomialCoefficientSign

    constantDeterminantCoefficientSignIsNegative :
      constantDeterminantCoefficientSign ≡ negativeCoefficient

    leadingEigenvalueExponentTop :
      Nat

    leadingEigenvalueExponentTopIsZero :
      leadingEigenvalueExponentTop ≡ 0

    leadingEigenvalueExponentCharm :
      Nat

    leadingEigenvalueExponentCharmIsFour :
      leadingEigenvalueExponentCharm ≡ 4

    leadingEigenvalueExponentUp :
      Nat

    leadingEigenvalueExponentUpIsTwelve :
      leadingEigenvalueExponentUp ≡ 12

    splittingFieldSupplied :
      Bool

    splittingFieldSuppliedIsFalse :
      splittingFieldSupplied ≡ false

    normalizedEigenbasisSupplied :
      Bool

    normalizedEigenbasisSuppliedIsFalse :
      normalizedEigenbasisSupplied ≡ false

    productClosureBlocker :
      CKMArithmeticInputSlot

    productClosureBlockerIsMissingCKMProductClosureWitness :
      productClosureBlocker ≡ missingCKMProductClosureWitness

    unitarityResidualBlocker :
      CKMArithmeticInputSlot

    unitarityResidualBlockerIsMissingUnitarityResidualWitness :
      unitarityResidualBlocker ≡ missingUnitarityResidualWitness

    physicalPromotionClaimed :
      Bool

    physicalPromotionClaimedIsFalse :
      physicalPromotionClaimed ≡ false

    concretePolynomialBoundary :
      List String

open CKMCurrentWaveConcreteUpCharacteristicPolynomialReceipt public

canonicalCKMCurrentWaveConcreteUpCharacteristicPolynomialReceipt :
  CKMCurrentWaveConcreteUpCharacteristicPolynomialReceipt
canonicalCKMCurrentWaveConcreteUpCharacteristicPolynomialReceipt =
  record
    { priorLeadingHermitianReceipt =
        canonicalCKMNextWaveUpHermitianCharacteristicLeadingReceipt
    ; priorLeadingReceiptRetainsProductBlocker =
        refl
    ; polynomialCarrier =
        rationalQ
    ; polynomialCarrierIsRationalQ =
        refl
    ; polynomialTerms =
        canonicalCKMCurrentWaveUpCharacteristicPolynomialTerms
    ; polynomialTermsAreCanonical =
        refl
    ; lambdaCubedCoefficientSign =
        positiveCoefficient
    ; lambdaCubedCoefficientSignIsPositive =
        refl
    ; lambdaSquaredConstantExponent =
        0
    ; lambdaSquaredConstantExponentIsZero =
        refl
    ; lambdaSquaredEpsilon4Exponent =
        4
    ; lambdaSquaredEpsilon4ExponentIsFour =
        refl
    ; lambdaSquaredEpsilon12Exponent =
        12
    ; lambdaSquaredEpsilon12ExponentIsTwelve =
        refl
    ; lambdaSquaredCoefficientSign =
        negativeCoefficient
    ; lambdaSquaredCoefficientSignIsNegative =
        refl
    ; lambdaMinorEpsilon4Exponent =
        4
    ; lambdaMinorEpsilon4ExponentIsFour =
        refl
    ; lambdaMinorEpsilon12Exponent =
        12
    ; lambdaMinorEpsilon12ExponentIsTwelve =
        refl
    ; lambdaMinorEpsilon16Exponent =
        16
    ; lambdaMinorEpsilon16ExponentIsSixteen =
        refl
    ; lambdaMinorCoefficientSign =
        positiveCoefficient
    ; lambdaMinorCoefficientSignIsPositive =
        refl
    ; constantDeterminantExponent =
        16
    ; constantDeterminantExponentIsSixteen =
        refl
    ; constantDeterminantCoefficientSign =
        negativeCoefficient
    ; constantDeterminantCoefficientSignIsNegative =
        refl
    ; leadingEigenvalueExponentTop =
        0
    ; leadingEigenvalueExponentTopIsZero =
        refl
    ; leadingEigenvalueExponentCharm =
        4
    ; leadingEigenvalueExponentCharmIsFour =
        refl
    ; leadingEigenvalueExponentUp =
        12
    ; leadingEigenvalueExponentUpIsTwelve =
        refl
    ; splittingFieldSupplied =
        false
    ; splittingFieldSuppliedIsFalse =
        refl
    ; normalizedEigenbasisSupplied =
        false
    ; normalizedEigenbasisSuppliedIsFalse =
        refl
    ; productClosureBlocker =
        missingCKMProductClosureWitness
    ; productClosureBlockerIsMissingCKMProductClosureWitness =
        refl
    ; unitarityResidualBlocker =
        missingUnitarityResidualWitness
    ; unitarityResidualBlockerIsMissingUnitarityResidualWitness =
        refl
    ; physicalPromotionClaimed =
        false
    ; physicalPromotionClaimedIsFalse =
        refl
    ; concretePolynomialBoundary =
        "chi_u(lambda) = lambda^3 - (1 + epsilon^4 + epsilon^12) lambda^2 + (epsilon^4 + epsilon^12 + epsilon^16) lambda - epsilon^16"
        ∷ "Leading eigenvalue exponents are top 0, charm 4, and up 12 for 0 < epsilon < 1"
        ∷ "This is a concrete leading polynomial over Q(epsilon), not a splitting-field or normalized-eigenbasis proof"
        ∷ "missingCKMProductClosureWitness and missingUnitarityResidualWitness remain retained blockers"
        ∷ []
    }

ckmCurrentWaveConcreteUpPolynomialDeterminantExponent :
  constantDeterminantExponent
    canonicalCKMCurrentWaveConcreteUpCharacteristicPolynomialReceipt
  ≡
  16
ckmCurrentWaveConcreteUpPolynomialDeterminantExponent =
  refl

ckmCurrentWaveConcreteUpPolynomialKeepsProductBlocker :
  productClosureBlocker
    canonicalCKMCurrentWaveConcreteUpCharacteristicPolynomialReceipt
  ≡
  missingCKMProductClosureWitness
ckmCurrentWaveConcreteUpPolynomialKeepsProductBlocker =
  refl

ckmCurrentWaveConcreteUpPolynomialDoesNotPromote :
  physicalPromotionClaimed
    canonicalCKMCurrentWaveConcreteUpCharacteristicPolynomialReceipt
  ≡
  false
ckmCurrentWaveConcreteUpPolynomialDoesNotPromote =
  refl

------------------------------------------------------------------------
-- Gate7 first-missing exact-arithmetic summary.
--
-- This summarizes the local m5/m6/l1 arithmetic state: the up-sector
-- Hermitian and characteristic surfaces are typechecked, the down-sector
-- Georgi-Jarlskog socket remains symbolic, and the CKM product/field route
-- stops fail-closed at Matter.MixingMatrix.

record CKMGate7FirstMissingExactArithmeticReceipt : Setω where
  field
    gate7UpHermitianProductSurface :
      CKMUpHermitianProductSurface

    gate7UpHermitianProductSurfaceSupplied :
      upHermitianProductSurfaceSupplied gate7UpHermitianProductSurface
      ≡
      true

    gate7UpCharacteristicPolynomialSurface :
      CKMUpCharacteristicPolynomialSurface

    gate7UpCharacteristicPolynomialSurfaceSupplied :
      upCharacteristicPolynomialSurfaceSupplied
        gate7UpCharacteristicPolynomialSurface
      ≡
      true

    gate7UpCharacteristicNextBlocker :
      nextUpSpectralBlocker gate7UpCharacteristicPolynomialSurface
      ≡
      missingEigenvalueSplittingField

    gate7DownGeorgiJarlskogExponentReceipt :
      CKMExplicitFNChargeTableExponentReceipt

    gate7DownGeorgiJarlskogTextureNotPromoted :
      physicalYukawaTexturePromoted
        gate7DownGeorgiJarlskogExponentReceipt
      ≡
      false

    gate7DownGeorgiJarlskogProductBlocker :
      retainedProductClosureBlocker
        gate7DownGeorgiJarlskogExponentReceipt
      ≡
      missingCKMProductClosureWitness

    gate7MatterMixingMatrixProductAttempt :
      CKMMatterMixingMatrixProductClosureAttemptReceipt

    gate7MatterMixingMatrixProductCarrier :
      ckmProductCarrier gate7MatterMixingMatrixProductAttempt
      ≡
      Matter.MixingMatrix

    gate7ProductClosureWitnessStillMissing :
      ckmProductClosureWitnessSupplied
        gate7MatterMixingMatrixProductAttempt
      ≡
      false

    gate7UnitarityResidualWitnessStillMissing :
      unitarityResidualWitnessSupplied
        gate7MatterMixingMatrixProductAttempt
      ≡
      false

    gate7ExactArithmeticAttempt :
      CKMGate7L1ExactArithmeticAttemptReceipt

    gate7ExactArithmeticAttemptDoesNotPromote :
      exactArithmeticAttemptPromotesCKM gate7ExactArithmeticAttempt
      ≡
      false

    gate7FirstMissingBoundary :
      List String

open CKMGate7FirstMissingExactArithmeticReceipt public

canonicalCKMGate7FirstMissingExactArithmeticReceipt :
  CKMGate7FirstMissingExactArithmeticReceipt
canonicalCKMGate7FirstMissingExactArithmeticReceipt =
  record
    { gate7UpHermitianProductSurface =
        canonicalCKMUpHermitianProductSurface
    ; gate7UpHermitianProductSurfaceSupplied =
        refl
    ; gate7UpCharacteristicPolynomialSurface =
        canonicalCKMUpCharacteristicPolynomialSurface
    ; gate7UpCharacteristicPolynomialSurfaceSupplied =
        refl
    ; gate7UpCharacteristicNextBlocker =
        refl
    ; gate7DownGeorgiJarlskogExponentReceipt =
        canonicalCKMExplicitFNChargeTableExponentReceipt
    ; gate7DownGeorgiJarlskogTextureNotPromoted =
        refl
    ; gate7DownGeorgiJarlskogProductBlocker =
        refl
    ; gate7MatterMixingMatrixProductAttempt =
        canonicalCKMMatterMixingMatrixProductClosureAttemptReceipt
    ; gate7MatterMixingMatrixProductCarrier =
        refl
    ; gate7ProductClosureWitnessStillMissing =
        refl
    ; gate7UnitarityResidualWitnessStillMissing =
        refl
    ; gate7ExactArithmeticAttempt =
        canonicalCKMGate7L1ExactArithmeticAttemptReceipt
    ; gate7ExactArithmeticAttemptDoesNotPromote =
        refl
    ; gate7FirstMissingBoundary =
        "Gate7 first-missing now has typechecked up-sector Hermitian-product and characteristic-polynomial receipts"
        ∷ "The down-sector Georgi-Jarlskog y22 socket is retained symbolically and no physical Yukawa texture is promoted"
        ∷ "The CKM product/field closure route is attempted through Matter.MixingMatrix and remains fail-closed"
        ∷ "missingCKMProductClosureWitness and missingUnitarityResidualWitness remain exact residual blockers"
        ∷ []
    }

ckmGate7FirstMissingExactArithmeticDoesNotPromote :
  gate7ExactArithmeticAttemptDoesNotPromote
    canonicalCKMGate7FirstMissingExactArithmeticReceipt
  ≡
  refl
ckmGate7FirstMissingExactArithmeticDoesNotPromote =
  refl

------------------------------------------------------------------------
-- Gate7 middle6 next-iteration fail-closed receipt.
--
-- This is the next local handoff after the m5/m6/l1 frontier.  It records
-- the exact leading exponent surfaces now visible to this lane, and names the
-- first missing witnesses without fabricating splitting fields, normalized
-- eigenbases, physical Yukawa normalization, or CKM product/unitarity proofs.

data CKMMiddle6NextIterationObstacle : Set where
  obstacleOpaqueMatterMixingMatrixNoProductEntries :
    CKMMiddle6NextIterationObstacle

  obstacleNoEigenvalueSplittingFieldCertificate :
    CKMMiddle6NextIterationObstacle

  obstacleNoNormalizedLeftEigenbasisMatrices :
    CKMMiddle6NextIterationObstacle

  obstacleNoUnitarityResidualComputation :
    CKMMiddle6NextIterationObstacle

canonicalCKMMiddle6NextIterationObstacles :
  List CKMMiddle6NextIterationObstacle
canonicalCKMMiddle6NextIterationObstacles =
  obstacleOpaqueMatterMixingMatrixNoProductEntries
  ∷ obstacleNoEigenvalueSplittingFieldCertificate
  ∷ obstacleNoNormalizedLeftEigenbasisMatrices
  ∷ obstacleNoUnitarityResidualComputation
  ∷ []

record CKMMiddle6NextIterationFailClosedReceipt : Setω where
  field
    firstMissingExactArithmeticReceipt :
      CKMGate7FirstMissingExactArithmeticReceipt

    upLeadingExponentY11 :
      Nat

    upLeadingExponentY11Is6 :
      upLeadingExponentY11 ≡ 6

    upLeadingExponentY12 :
      Nat

    upLeadingExponentY12Is5 :
      upLeadingExponentY12 ≡ 5

    upLeadingExponentY13 :
      Nat

    upLeadingExponentY13Is3 :
      upLeadingExponentY13 ≡ 3

    upLeadingExponentY22 :
      Nat

    upLeadingExponentY22Is4 :
      upLeadingExponentY22 ≡ 4

    upLeadingExponentY23 :
      Nat

    upLeadingExponentY23Is2 :
      upLeadingExponentY23 ≡ 2

    upLeadingExponentY33 :
      Nat

    upLeadingExponentY33Is0 :
      upLeadingExponentY33 ≡ 0

    downLeadingExponentY11 :
      Nat

    downLeadingExponentY11Is1 :
      downLeadingExponentY11 ≡ 1

    downLeadingExponentY12 :
      Nat

    downLeadingExponentY12Is2 :
      downLeadingExponentY12 ≡ 2

    downLeadingExponentY13 :
      Nat

    downLeadingExponentY13Is0 :
      downLeadingExponentY13 ≡ 0

    downLeadingExponentY21 :
      Nat

    downLeadingExponentY21Is3 :
      downLeadingExponentY21 ≡ 3

    downLeadingExponentY22 :
      Nat

    downLeadingExponentY22Is2 :
      downLeadingExponentY22 ≡ 2

    downLeadingExponentY23 :
      Nat

    downLeadingExponentY23Is2 :
      downLeadingExponentY23 ≡ 2

    downLeadingExponentY31 :
      Nat

    downLeadingExponentY31Is3 :
      downLeadingExponentY31 ≡ 3

    downLeadingExponentY32 :
      Nat

    downLeadingExponentY32Is1 :
      downLeadingExponentY32 ≡ 1

    downLeadingExponentY33 :
      Nat

    downLeadingExponentY33Is3 :
      downLeadingExponentY33 ≡ 3

    downY22GeorgiJarlskogSocketRetained :
      yukawaEntryGeorgiJarlskogY22Socket
        (georgiJarlskogDownY22FNYukawaEntry 2)
      ≡
      true

    upTraceNextLeadingExponent :
      Nat

    upTraceNextLeadingExponentIs4 :
      upTraceNextLeadingExponent ≡ 4

    upDeterminantLeadingExponent :
      Nat

    upDeterminantLeadingExponentIs18 :
      upDeterminantLeadingExponent ≡ 18

    splittingFieldBlocker :
      CKMArithmeticInputSlot

    splittingFieldBlockerIsEigenvalueSplittingField :
      splittingFieldBlocker ≡ missingEigenvalueSplittingField

    normalizedEigenbasisBlocker :
      CKMArithmeticInputSlot

    normalizedEigenbasisBlockerIsNormalizedLeftEigenbases :
      normalizedEigenbasisBlocker ≡ missingNormalizedLeftEigenbases

    productClosureBlocker :
      CKMArithmeticInputSlot

    productClosureBlockerIsMissingCKMProductClosureWitness :
      productClosureBlocker ≡ missingCKMProductClosureWitness

    unitarityResidualBlocker :
      CKMArithmeticInputSlot

    unitarityResidualBlockerIsMissingUnitarityResidualWitness :
      unitarityResidualBlocker ≡ missingUnitarityResidualWitness

    nextIterationObstacles :
      List CKMMiddle6NextIterationObstacle

    nextIterationObstaclesAreCanonical :
      nextIterationObstacles
      ≡
      canonicalCKMMiddle6NextIterationObstacles

    vHiggsAdapter4BoundaryRetained :
      Bool

    vHiggsAdapter4BoundaryRetainedIsTrue :
      vHiggsAdapter4BoundaryRetained ≡ true

    physicalYukawaPromotionClaimed :
      Bool

    physicalYukawaPromotionClaimedIsFalse :
      physicalYukawaPromotionClaimed ≡ false

    ckmProductWitnessFabricated :
      Bool

    ckmProductWitnessFabricatedIsFalse :
      ckmProductWitnessFabricated ≡ false

    unitarityResidualWitnessFabricated :
      Bool

    unitarityResidualWitnessFabricatedIsFalse :
      unitarityResidualWitnessFabricated ≡ false

    nextIterationBoundary :
      List String

open CKMMiddle6NextIterationFailClosedReceipt public

canonicalCKMMiddle6NextIterationFailClosedReceipt :
  CKMMiddle6NextIterationFailClosedReceipt
canonicalCKMMiddle6NextIterationFailClosedReceipt =
  record
    { firstMissingExactArithmeticReceipt =
        canonicalCKMGate7FirstMissingExactArithmeticReceipt
    ; upLeadingExponentY11 =
        6
    ; upLeadingExponentY11Is6 =
        refl
    ; upLeadingExponentY12 =
        5
    ; upLeadingExponentY12Is5 =
        refl
    ; upLeadingExponentY13 =
        3
    ; upLeadingExponentY13Is3 =
        refl
    ; upLeadingExponentY22 =
        4
    ; upLeadingExponentY22Is4 =
        refl
    ; upLeadingExponentY23 =
        2
    ; upLeadingExponentY23Is2 =
        refl
    ; upLeadingExponentY33 =
        0
    ; upLeadingExponentY33Is0 =
        refl
    ; downLeadingExponentY11 =
        1
    ; downLeadingExponentY11Is1 =
        refl
    ; downLeadingExponentY12 =
        2
    ; downLeadingExponentY12Is2 =
        refl
    ; downLeadingExponentY13 =
        0
    ; downLeadingExponentY13Is0 =
        refl
    ; downLeadingExponentY21 =
        3
    ; downLeadingExponentY21Is3 =
        refl
    ; downLeadingExponentY22 =
        2
    ; downLeadingExponentY22Is2 =
        refl
    ; downLeadingExponentY23 =
        2
    ; downLeadingExponentY23Is2 =
        refl
    ; downLeadingExponentY31 =
        3
    ; downLeadingExponentY31Is3 =
        refl
    ; downLeadingExponentY32 =
        1
    ; downLeadingExponentY32Is1 =
        refl
    ; downLeadingExponentY33 =
        3
    ; downLeadingExponentY33Is3 =
        refl
    ; downY22GeorgiJarlskogSocketRetained =
        refl
    ; upTraceNextLeadingExponent =
        4
    ; upTraceNextLeadingExponentIs4 =
        refl
    ; upDeterminantLeadingExponent =
        18
    ; upDeterminantLeadingExponentIs18 =
        refl
    ; splittingFieldBlocker =
        missingEigenvalueSplittingField
    ; splittingFieldBlockerIsEigenvalueSplittingField =
        refl
    ; normalizedEigenbasisBlocker =
        missingNormalizedLeftEigenbases
    ; normalizedEigenbasisBlockerIsNormalizedLeftEigenbases =
        refl
    ; productClosureBlocker =
        missingCKMProductClosureWitness
    ; productClosureBlockerIsMissingCKMProductClosureWitness =
        refl
    ; unitarityResidualBlocker =
        missingUnitarityResidualWitness
    ; unitarityResidualBlockerIsMissingUnitarityResidualWitness =
        refl
    ; nextIterationObstacles =
        canonicalCKMMiddle6NextIterationObstacles
    ; nextIterationObstaclesAreCanonical =
        refl
    ; vHiggsAdapter4BoundaryRetained =
        true
    ; vHiggsAdapter4BoundaryRetainedIsTrue =
        refl
    ; physicalYukawaPromotionClaimed =
        false
    ; physicalYukawaPromotionClaimedIsFalse =
        refl
    ; ckmProductWitnessFabricated =
        false
    ; ckmProductWitnessFabricatedIsFalse =
        refl
    ; unitarityResidualWitnessFabricated =
        false
    ; unitarityResidualWitnessFabricatedIsFalse =
        refl
    ; nextIterationBoundary =
        "middle6 exact exponent surfaces are fixed as Yu: 6,5,3 / 5,4,2 / 3,2,0 and Yd: 1,2,0 / 3,2,2 / 3,1,3"
        ∷ "The up characteristic surface records trace next exponent 4 and determinant leading exponent 18 over the rational entry field"
        ∷ "The down y22 Georgi-Jarlskog socket is retained exactly as staged arithmetic"
        ∷ "missingCKMProductClosureWitness is blocked by the absence of concrete U_u, U_d, and V_CKM product entries beyond Matter.MixingMatrix"
        ∷ "missingUnitarityResidualWitness is blocked by the absence of normalized left eigenbases and a concrete V V^dagger minus identity residual"
        ∷ "No splitting field, normalized eigenbasis, physical Yukawa promotion, or vHiggs Adapter4 promotion is fabricated"
        ∷ []
    }

ckmMiddle6NextIterationKeepsProductWitnessMissing :
  productClosureBlocker canonicalCKMMiddle6NextIterationFailClosedReceipt
  ≡
  missingCKMProductClosureWitness
ckmMiddle6NextIterationKeepsProductWitnessMissing =
  refl

ckmMiddle6NextIterationKeepsUnitarityResidualMissing :
  unitarityResidualBlocker canonicalCKMMiddle6NextIterationFailClosedReceipt
  ≡
  missingUnitarityResidualWitness
ckmMiddle6NextIterationKeepsUnitarityResidualMissing =
  refl

ckmMiddle6NextIterationDoesNotPromoteYukawa :
  physicalYukawaPromotionClaimed
    canonicalCKMMiddle6NextIterationFailClosedReceipt
  ≡
  false
ckmMiddle6NextIterationDoesNotPromoteYukawa =
  refl

------------------------------------------------------------------------
-- lower6 exact rational-epsilon closure blocker.
--
-- This is the l4 worker hard-stop after inspecting the current exact
-- arithmetic surfaces.  The up polynomial is recorded over the rational
-- epsilon field, but the repo does not expose a splitting-field certificate,
-- normalized diagonalizer entries, or product entries behind Matter.MixingMatrix.

data CKMLower6ExactRationalEpsilonBlocker : Set where
  exactRationalEpsilonOnlyLeadingUpPolynomialBlocker :
    CKMLower6ExactRationalEpsilonBlocker

  exactRationalEpsilonNoSplittingFieldCertificateBlocker :
    CKMLower6ExactRationalEpsilonBlocker

  exactRationalEpsilonNoNormalizedEigenbasisEntriesBlocker :
    CKMLower6ExactRationalEpsilonBlocker

  exactRationalEpsilonOpaqueMatterMixingMatrixBlocker :
    CKMLower6ExactRationalEpsilonBlocker

  exactRationalEpsilonNoCKMProductClosureWitnessBlocker :
    CKMLower6ExactRationalEpsilonBlocker

  exactRationalEpsilonNoUnitarityResidualWitnessBlocker :
    CKMLower6ExactRationalEpsilonBlocker

canonicalCKMLower6ExactRationalEpsilonBlockers :
  List CKMLower6ExactRationalEpsilonBlocker
canonicalCKMLower6ExactRationalEpsilonBlockers =
  exactRationalEpsilonOnlyLeadingUpPolynomialBlocker
  ∷ exactRationalEpsilonNoSplittingFieldCertificateBlocker
  ∷ exactRationalEpsilonNoNormalizedEigenbasisEntriesBlocker
  ∷ exactRationalEpsilonOpaqueMatterMixingMatrixBlocker
  ∷ exactRationalEpsilonNoCKMProductClosureWitnessBlocker
  ∷ exactRationalEpsilonNoUnitarityResidualWitnessBlocker
  ∷ []

record CKMLower6ExactRationalEpsilonClosureBlockerReceipt : Setω where
  field
    lower6ExactUpPolynomialReceipt :
      CKMCurrentWaveConcreteUpCharacteristicPolynomialReceipt

    lower6ExactUpPolynomialOverRationalQ :
      polynomialCarrier lower6ExactUpPolynomialReceipt
      ≡
      rationalQ

    lower6ExactUpSplittingFieldStillMissing :
      splittingFieldSupplied lower6ExactUpPolynomialReceipt
      ≡
      false

    lower6ExactUpNormalizedEigenbasisStillMissing :
      normalizedEigenbasisSupplied lower6ExactUpPolynomialReceipt
      ≡
      false

    lower6ExactEntryFieldFrontier :
      CKMMiddle6NextIterationFailClosedReceipt

    lower6ExactEntryFieldSplittingBlocker :
      splittingFieldBlocker lower6ExactEntryFieldFrontier
      ≡
      missingEigenvalueSplittingField

    lower6ExactEntryFieldProductBlocker :
      productClosureBlocker lower6ExactEntryFieldFrontier
      ≡
      missingCKMProductClosureWitness

    lower6ExactEntryFieldResidualBlocker :
      unitarityResidualBlocker lower6ExactEntryFieldFrontier
      ≡
      missingUnitarityResidualWitness

    lower6ExactMatterMixingProductAttempt :
      CKMMatterMixingMatrixProductClosureAttemptReceipt

    lower6ExactProductCarrierIsMatterMixingMatrix :
      ckmProductCarrier lower6ExactMatterMixingProductAttempt
      ≡
      Matter.MixingMatrix

    lower6ExactConcreteUuMatrixMissing :
      concreteNormalizedUuMatrixTermSupplied
        lower6ExactMatterMixingProductAttempt
      ≡
      false

    lower6ExactConcreteUdMatrixMissing :
      concreteNormalizedUdMatrixTermSupplied
        lower6ExactMatterMixingProductAttempt
      ≡
      false

    lower6ExactProductWitnessMissing :
      ckmProductClosureWitnessSupplied
        lower6ExactMatterMixingProductAttempt
      ≡
      false

    lower6ExactUnitarityResidualMissing :
      unitarityResidualWitnessSupplied
        lower6ExactMatterMixingProductAttempt
      ≡
      false

    lower6ExactRationalEpsilonBlockers :
      List CKMLower6ExactRationalEpsilonBlocker

    lower6ExactRationalEpsilonBlockersAreCanonical :
      lower6ExactRationalEpsilonBlockers
      ≡
      canonicalCKMLower6ExactRationalEpsilonBlockers

    exactRationalEpsilonClosureProved :
      Bool

    exactRationalEpsilonClosureProvedIsFalse :
      exactRationalEpsilonClosureProved ≡ false

    exactRationalQAloneSufficesProved :
      Bool

    exactRationalQAloneSufficesProvedIsFalse :
      exactRationalQAloneSufficesProved ≡ false

    lower6ExactRationalBoundary :
      List String

open CKMLower6ExactRationalEpsilonClosureBlockerReceipt public

canonicalCKMLower6ExactRationalEpsilonClosureBlockerReceipt :
  CKMLower6ExactRationalEpsilonClosureBlockerReceipt
canonicalCKMLower6ExactRationalEpsilonClosureBlockerReceipt =
  record
    { lower6ExactUpPolynomialReceipt =
        canonicalCKMCurrentWaveConcreteUpCharacteristicPolynomialReceipt
    ; lower6ExactUpPolynomialOverRationalQ =
        refl
    ; lower6ExactUpSplittingFieldStillMissing =
        refl
    ; lower6ExactUpNormalizedEigenbasisStillMissing =
        refl
    ; lower6ExactEntryFieldFrontier =
        canonicalCKMMiddle6NextIterationFailClosedReceipt
    ; lower6ExactEntryFieldSplittingBlocker =
        refl
    ; lower6ExactEntryFieldProductBlocker =
        refl
    ; lower6ExactEntryFieldResidualBlocker =
        refl
    ; lower6ExactMatterMixingProductAttempt =
        canonicalCKMMatterMixingMatrixProductClosureAttemptReceipt
    ; lower6ExactProductCarrierIsMatterMixingMatrix =
        refl
    ; lower6ExactConcreteUuMatrixMissing =
        refl
    ; lower6ExactConcreteUdMatrixMissing =
        refl
    ; lower6ExactProductWitnessMissing =
        refl
    ; lower6ExactUnitarityResidualMissing =
        refl
    ; lower6ExactRationalEpsilonBlockers =
        canonicalCKMLower6ExactRationalEpsilonBlockers
    ; lower6ExactRationalEpsilonBlockersAreCanonical =
        refl
    ; exactRationalEpsilonClosureProved =
        false
    ; exactRationalEpsilonClosureProvedIsFalse =
        refl
    ; exactRationalQAloneSufficesProved =
        false
    ; exactRationalQAloneSufficesProvedIsFalse =
        refl
    ; lower6ExactRationalBoundary =
        "The requested rational-epsilon route reaches only the current leading up characteristic polynomial over Q(epsilon)"
        ∷ "No splitting-field certificate or normalized eigenbasis entries are exposed for the up/down Hermitian products"
        ∷ "The CKM product target remains the opaque Matter.MixingMatrix carrier for U_u, U_d, and V_CKM"
        ∷ "No product-closure witness or V V^dagger residual witness exists behind that carrier"
        ∷ "The proof that Q alone suffices is not inhabited; a finite algebraic extension may still be required by normalized eigenvectors"
        ∷ []
    }

ckmLower6ExactRationalEpsilonClosureStillBlocked :
  exactRationalEpsilonClosureProved
    canonicalCKMLower6ExactRationalEpsilonClosureBlockerReceipt
  ≡
  false
ckmLower6ExactRationalEpsilonClosureStillBlocked =
  refl

ckmLower6ExactRationalQAloneNotProved :
  exactRationalQAloneSufficesProved
    canonicalCKMLower6ExactRationalEpsilonClosureBlockerReceipt
  ≡
  false
ckmLower6ExactRationalQAloneNotProved =
  refl

------------------------------------------------------------------------
-- Gate7 m5/m6/l1 rational epsilon = 1/5 spectral attempt.
--
-- This is a finite arithmetic attempt surface only.  It specializes the
-- leading epsilon bookkeeping to the rational value 1/5 and records the
-- leading eigenvalue denominators suggested by the exponent surface.  It does
-- not manufacture a splitting-field theorem, normalized eigenbasis, CKM
-- product closure, unitarity residual, vHiggs normalization, or physical
-- promotion.

data CKMRationalOneFifthSpectralAttemptComponent : Set where
  epsilonOneFifthSpecializationComponent :
    CKMRationalOneFifthSpectralAttemptComponent

  leadingEigenvalueRationalSurfaceComponent :
    CKMRationalOneFifthSpectralAttemptComponent

  rationalSplittingFieldCandidateComponent :
    CKMRationalOneFifthSpectralAttemptComponent

  opaqueNormalizedEigenbasisBlockerComponent :
    CKMRationalOneFifthSpectralAttemptComponent

  opaqueMatterMixingMatrixProductBlockerComponent :
    CKMRationalOneFifthSpectralAttemptComponent

canonicalCKMRationalOneFifthSpectralAttemptComponents :
  List CKMRationalOneFifthSpectralAttemptComponent
canonicalCKMRationalOneFifthSpectralAttemptComponents =
  epsilonOneFifthSpecializationComponent
  ∷ leadingEigenvalueRationalSurfaceComponent
  ∷ rationalSplittingFieldCandidateComponent
  ∷ opaqueNormalizedEigenbasisBlockerComponent
  ∷ opaqueMatterMixingMatrixProductBlockerComponent
  ∷ []

record CKMRationalOneFifthSpectralAttemptReceipt : Setω where
  field
    concreteUpPolynomial :
      CKMCurrentWaveConcreteUpCharacteristicPolynomialReceipt

    concreteUpPolynomialRetained :
      productClosureBlocker concreteUpPolynomial
      ≡
      missingCKMProductClosureWitness

    spectralAttemptComponents :
      List CKMRationalOneFifthSpectralAttemptComponent

    spectralAttemptComponentsAreCanonical :
      spectralAttemptComponents
      ≡
      canonicalCKMRationalOneFifthSpectralAttemptComponents

    epsilonNumerator :
      Nat

    epsilonNumeratorIsOne :
      epsilonNumerator ≡ 1

    epsilonDenominator :
      Nat

    epsilonDenominatorIsFive :
      epsilonDenominator ≡ 5

    epsilonField :
      CKMEntryField

    epsilonFieldIsRationalQ :
      epsilonField ≡ rationalQ

    leadingTopEigenvalueNumerator :
      Nat

    leadingTopEigenvalueNumeratorIsOne :
      leadingTopEigenvalueNumerator ≡ 1

    leadingTopEigenvalueDenominator :
      Nat

    leadingTopEigenvalueDenominatorIsOne :
      leadingTopEigenvalueDenominator ≡ 1

    leadingCharmEigenvalueNumerator :
      Nat

    leadingCharmEigenvalueNumeratorIsOne :
      leadingCharmEigenvalueNumerator ≡ 1

    leadingCharmEigenvalueDenominator :
      Nat

    leadingCharmEigenvalueDenominatorIsFiveToFourth :
      leadingCharmEigenvalueDenominator ≡ 625

    leadingUpEigenvalueNumerator :
      Nat

    leadingUpEigenvalueNumeratorIsOne :
      leadingUpEigenvalueNumerator ≡ 1

    leadingUpEigenvalueDenominator :
      Nat

    leadingUpEigenvalueDenominatorIsFiveToTwelfth :
      leadingUpEigenvalueDenominator ≡ 244140625

    leadingEigenvalueSurfaceOverQ :
      Bool

    leadingEigenvalueSurfaceOverQIsTrue :
      leadingEigenvalueSurfaceOverQ ≡ true

    splittingFieldCandidate :
      CKMEntryField

    splittingFieldCandidateIsRationalQ :
      splittingFieldCandidate ≡ rationalQ

    exactSplittingFieldClosureSupplied :
      Bool

    exactSplittingFieldClosureSuppliedIsFalse :
      exactSplittingFieldClosureSupplied ≡ false

    normalizedEigenbasisAPIOpaque :
      Bool

    normalizedEigenbasisAPIOpaqueIsTrue :
      normalizedEigenbasisAPIOpaque ≡ true

    matterMixingMatrixAPIOpaque :
      Bool

    matterMixingMatrixAPIOpaqueIsTrue :
      matterMixingMatrixAPIOpaque ≡ true

    exactCKMProductClosureWitnessSupplied :
      Bool

    exactCKMProductClosureWitnessSuppliedIsFalse :
      exactCKMProductClosureWitnessSupplied ≡ false

    exactProductClosureBlocker :
      CKMArithmeticInputSlot

    exactProductClosureBlockerIsMissingCKMProductClosureWitness :
      exactProductClosureBlocker ≡ missingCKMProductClosureWitness

    vHiggsAdapter4BoundaryRetained :
      Bool

    vHiggsAdapter4BoundaryRetainedIsTrue :
      vHiggsAdapter4BoundaryRetained ≡ true

    physicalPromotionClaimed :
      Bool

    physicalPromotionClaimedIsFalse :
      physicalPromotionClaimed ≡ false

    rationalOneFifthSpectralBoundary :
      List String

open CKMRationalOneFifthSpectralAttemptReceipt public

canonicalCKMRationalOneFifthSpectralAttemptReceipt :
  CKMRationalOneFifthSpectralAttemptReceipt
canonicalCKMRationalOneFifthSpectralAttemptReceipt =
  record
    { concreteUpPolynomial =
        canonicalCKMCurrentWaveConcreteUpCharacteristicPolynomialReceipt
    ; concreteUpPolynomialRetained =
        refl
    ; spectralAttemptComponents =
        canonicalCKMRationalOneFifthSpectralAttemptComponents
    ; spectralAttemptComponentsAreCanonical =
        refl
    ; epsilonNumerator =
        1
    ; epsilonNumeratorIsOne =
        refl
    ; epsilonDenominator =
        5
    ; epsilonDenominatorIsFive =
        refl
    ; epsilonField =
        rationalQ
    ; epsilonFieldIsRationalQ =
        refl
    ; leadingTopEigenvalueNumerator =
        1
    ; leadingTopEigenvalueNumeratorIsOne =
        refl
    ; leadingTopEigenvalueDenominator =
        1
    ; leadingTopEigenvalueDenominatorIsOne =
        refl
    ; leadingCharmEigenvalueNumerator =
        1
    ; leadingCharmEigenvalueNumeratorIsOne =
        refl
    ; leadingCharmEigenvalueDenominator =
        625
    ; leadingCharmEigenvalueDenominatorIsFiveToFourth =
        refl
    ; leadingUpEigenvalueNumerator =
        1
    ; leadingUpEigenvalueNumeratorIsOne =
        refl
    ; leadingUpEigenvalueDenominator =
        244140625
    ; leadingUpEigenvalueDenominatorIsFiveToTwelfth =
        refl
    ; leadingEigenvalueSurfaceOverQ =
        true
    ; leadingEigenvalueSurfaceOverQIsTrue =
        refl
    ; splittingFieldCandidate =
        rationalQ
    ; splittingFieldCandidateIsRationalQ =
        refl
    ; exactSplittingFieldClosureSupplied =
        false
    ; exactSplittingFieldClosureSuppliedIsFalse =
        refl
    ; normalizedEigenbasisAPIOpaque =
        true
    ; normalizedEigenbasisAPIOpaqueIsTrue =
        refl
    ; matterMixingMatrixAPIOpaque =
        true
    ; matterMixingMatrixAPIOpaqueIsTrue =
        refl
    ; exactCKMProductClosureWitnessSupplied =
        false
    ; exactCKMProductClosureWitnessSuppliedIsFalse =
        refl
    ; exactProductClosureBlocker =
        missingCKMProductClosureWitness
    ; exactProductClosureBlockerIsMissingCKMProductClosureWitness =
        refl
    ; vHiggsAdapter4BoundaryRetained =
        true
    ; vHiggsAdapter4BoundaryRetainedIsTrue =
        refl
    ; physicalPromotionClaimed =
        false
    ; physicalPromotionClaimedIsFalse =
        refl
    ; rationalOneFifthSpectralBoundary =
        "epsilon is specialized to the rational value 1/5 for this finite leading-order attempt"
        ∷ "The leading eigenvalue surface records 1, 1/5^4, and 1/5^12 as rational bookkeeping data"
        ∷ "Q is recorded only as the leading splitting-field candidate; no exact splitting-field theorem is supplied"
        ∷ "Exact missingCKMProductClosureWitness cannot close because normalized eigenbasis entries and Matter.MixingMatrix product entries are opaque"
        ∷ "vHiggs Adapter4 is retained and no physical promotion is introduced"
        ∷ []
    }

ckmRationalOneFifthSpectralAttemptKeepsProductClosureMissing :
  exactProductClosureBlocker canonicalCKMRationalOneFifthSpectralAttemptReceipt
  ≡
  missingCKMProductClosureWitness
ckmRationalOneFifthSpectralAttemptKeepsProductClosureMissing =
  refl

ckmRationalOneFifthSpectralAttemptRecordsOpaqueMatterMixingMatrix :
  matterMixingMatrixAPIOpaque canonicalCKMRationalOneFifthSpectralAttemptReceipt
  ≡
  true
ckmRationalOneFifthSpectralAttemptRecordsOpaqueMatterMixingMatrix =
  refl

ckmRationalOneFifthSpectralAttemptDoesNotPromote :
  physicalPromotionClaimed canonicalCKMRationalOneFifthSpectralAttemptReceipt
  ≡
  false
ckmRationalOneFifthSpectralAttemptDoesNotPromote =
  refl

------------------------------------------------------------------------
-- lower6 current wave: explicit rational/Gaussian-rational CKM data.
--
-- The requested Wolfenstein numbers can be represented locally as finite
-- signed rational data, including Q[i] entries.  This records the concrete
-- arithmetic handoff for m5/m6/l1 while preserving the existing hard blocker:
-- Matter.MixingMatrix is still opaque, so this is not the exact product
-- closure theorem or missingCarrierMixingTheorem.

record SignedRationalDatum : Set where
  constructor signedRationalDatum
  field
    numerator :
      Nat

    denominator :
      Nat

    positive :
      Bool

open SignedRationalDatum public

record GaussianRationalDatum : Set where
  constructor gaussianRationalDatum
  field
    realPart :
      SignedRationalDatum

    imaginaryPart :
      SignedRationalDatum

open GaussianRationalDatum public

zeroSignedRationalDatum : SignedRationalDatum
zeroSignedRationalDatum =
  signedRationalDatum 0 1 true

oneSignedRationalDatum : SignedRationalDatum
oneSignedRationalDatum =
  signedRationalDatum 1 1 true

minusOneSignedRationalDatum : SignedRationalDatum
minusOneSignedRationalDatum =
  signedRationalDatum 1 1 false

oneFifthSignedRationalDatum : SignedRationalDatum
oneFifthSignedRationalDatum =
  signedRationalDatum 1 5 true

minusOneFifthSignedRationalDatum : SignedRationalDatum
minusOneFifthSignedRationalDatum =
  signedRationalDatum 1 5 false

oneTwentyFifthSignedRationalDatum : SignedRationalDatum
oneTwentyFifthSignedRationalDatum =
  signedRationalDatum 1 25 true

minusOneTwentyFifthSignedRationalDatum : SignedRationalDatum
minusOneTwentyFifthSignedRationalDatum =
  signedRationalDatum 1 25 false

fortyNineFiftiethsSignedRationalDatum : SignedRationalDatum
fortyNineFiftiethsSignedRationalDatum =
  signedRationalDatum 49 50 true

oneFiveHundredSignedRationalDatum : SignedRationalDatum
oneFiveHundredSignedRationalDatum =
  signedRationalDatum 1 500 true

threeFiveHundredSignedRationalDatum : SignedRationalDatum
threeFiveHundredSignedRationalDatum =
  signedRationalDatum 3 500 true

minusOneThreeSeventyFiveSignedRationalDatum : SignedRationalDatum
minusOneThreeSeventyFiveSignedRationalDatum =
  signedRationalDatum 1 375 false

oneFortyEightThousandEightHundredSeventyFiveSignedRationalDatum :
  SignedRationalDatum
oneFortyEightThousandEightHundredSeventyFiveSignedRationalDatum =
  signedRationalDatum 1 46875 true

fortyNineOver2343750SignedRationalDatum : SignedRationalDatum
fortyNineOver2343750SignedRationalDatum =
  signedRationalDatum 49 2343750 true

minusFortyNineOver2343750SignedRationalDatum : SignedRationalDatum
minusFortyNineOver2343750SignedRationalDatum =
  signedRationalDatum 49 2343750 false

zeroGaussianRationalDatum : GaussianRationalDatum
zeroGaussianRationalDatum =
  gaussianRationalDatum zeroSignedRationalDatum zeroSignedRationalDatum

oneGaussianRationalDatum : GaussianRationalDatum
oneGaussianRationalDatum =
  gaussianRationalDatum oneSignedRationalDatum zeroSignedRationalDatum

minusOneGaussianRationalDatum : GaussianRationalDatum
minusOneGaussianRationalDatum =
  gaussianRationalDatum minusOneSignedRationalDatum zeroSignedRationalDatum

vubWolfensteinGaussianDatum : GaussianRationalDatum
vubWolfensteinGaussianDatum =
  gaussianRationalDatum
    oneFiveHundredSignedRationalDatum
    minusOneThreeSeventyFiveSignedRationalDatum

vtdWolfensteinGaussianDatum : GaussianRationalDatum
vtdWolfensteinGaussianDatum =
  gaussianRationalDatum
    threeFiveHundredSignedRationalDatum
    minusOneThreeSeventyFiveSignedRationalDatum

record Matrix3GaussianRationalDatum : Set where
  constructor matrix3GaussianRationalDatum
  field
    m11 m12 m13 :
      GaussianRationalDatum

    m21 m22 m23 :
      GaussianRationalDatum

    m31 m32 m33 :
      GaussianRationalDatum

open Matrix3GaussianRationalDatum public

upEigenbasisLeadingOrderGaussianDatum : Matrix3GaussianRationalDatum
upEigenbasisLeadingOrderGaussianDatum =
  matrix3GaussianRationalDatum
    oneGaussianRationalDatum zeroGaussianRationalDatum zeroGaussianRationalDatum
    zeroGaussianRationalDatum oneGaussianRationalDatum zeroGaussianRationalDatum
    zeroGaussianRationalDatum zeroGaussianRationalDatum oneGaussianRationalDatum

ckmWolfensteinOrder4GaussianDatum : Matrix3GaussianRationalDatum
ckmWolfensteinOrder4GaussianDatum =
  matrix3GaussianRationalDatum
    (gaussianRationalDatum
      fortyNineFiftiethsSignedRationalDatum
      zeroSignedRationalDatum)
    (gaussianRationalDatum oneFifthSignedRationalDatum zeroSignedRationalDatum)
    vubWolfensteinGaussianDatum
    (gaussianRationalDatum
      minusOneFifthSignedRationalDatum
      zeroSignedRationalDatum)
    (gaussianRationalDatum
      fortyNineFiftiethsSignedRationalDatum
      zeroSignedRationalDatum)
    (gaussianRationalDatum oneTwentyFifthSignedRationalDatum zeroSignedRationalDatum)
    vtdWolfensteinGaussianDatum
    (gaussianRationalDatum
      minusOneTwentyFifthSignedRationalDatum
      zeroSignedRationalDatum)
    oneGaussianRationalDatum

data CKMConcreteWolfensteinProductClosureStatus : Set where
  orderBoundedTruncatedWolfensteinProductClosure :
    CKMConcreteWolfensteinProductClosureStatus

record CKMConcreteWolfensteinProductClosureReceipt : Set where
  field
    productClosureStatus :
      CKMConcreteWolfensteinProductClosureStatus

    productCoefficientField :
      CKMEntryField

    productCoefficientFieldIsGaussianRational :
      productCoefficientField ≡ finiteAlgebraicExtension "Q[i]"

    epsilonNumerator :
      Nat

    epsilonNumeratorIsOne :
      epsilonNumerator ≡ 1

    epsilonDenominator :
      Nat

    epsilonDenominatorIsFive :
      epsilonDenominator ≡ 5

    wolfensteinA :
      SignedRationalDatum

    wolfensteinAIsOne :
      wolfensteinA ≡ oneSignedRationalDatum

    wolfensteinRho :
      SignedRationalDatum

    wolfensteinRhoIsOneFourth :
      wolfensteinRho ≡ signedRationalDatum 1 4 true

    wolfensteinEta :
      SignedRationalDatum

    wolfensteinEtaIsOneThird :
      wolfensteinEta ≡ signedRationalDatum 1 3 true

    uuDaggerLeadingDatum :
      Matrix3GaussianRationalDatum

    uuDaggerLeadingDatumIsIdentity :
      uuDaggerLeadingDatum
      ≡
      upEigenbasisLeadingOrderGaussianDatum

    udWolfensteinDatum :
      Matrix3GaussianRationalDatum

    udWolfensteinDatumIsConcreteTruncatedWolfenstein :
      udWolfensteinDatum
      ≡
      ckmWolfensteinOrder4GaussianDatum

    productDatum :
      Matrix3GaussianRationalDatum

    productDatumIsIdentityTimesWolfenstein :
      productDatum
      ≡
      ckmWolfensteinOrder4GaussianDatum

    vudEntry :
      m11 productDatum
      ≡
      gaussianRationalDatum
        fortyNineFiftiethsSignedRationalDatum
        zeroSignedRationalDatum

    productVusEntry :
      m12 productDatum
      ≡
      gaussianRationalDatum oneFifthSignedRationalDatum zeroSignedRationalDatum

    productVubEntry :
      m13 productDatum
      ≡
      vubWolfensteinGaussianDatum

    vcdEntry :
      m21 productDatum
      ≡
      gaussianRationalDatum
        minusOneFifthSignedRationalDatum
        zeroSignedRationalDatum

    vcsEntry :
      m22 productDatum
      ≡
      gaussianRationalDatum
        fortyNineFiftiethsSignedRationalDatum
        zeroSignedRationalDatum

    productVcbEntry :
      m23 productDatum
      ≡
      gaussianRationalDatum
        oneTwentyFifthSignedRationalDatum
        zeroSignedRationalDatum

    vtdEntry :
      m31 productDatum
      ≡
      vtdWolfensteinGaussianDatum

    vtsEntry :
      m32 productDatum
      ≡
      gaussianRationalDatum
        minusOneTwentyFifthSignedRationalDatum
        zeroSignedRationalDatum

    productVtbEntry :
      m33 productDatum
      ≡
      oneGaussianRationalDatum

    residualOrderExponent :
      Nat

    residualOrderExponentIsFour :
      residualOrderExponent ≡ 4

    residualBoundNumerator :
      Nat

    residualBoundNumeratorIsOne :
      residualBoundNumerator ≡ 1

    residualBoundDenominator :
      Nat

    residualBoundDenominatorIsSixHundredTwentyFive :
      residualBoundDenominator ≡ 625

    truncatedProductClosureRecorded :
      Bool

    truncatedProductClosureRecordedIsTrue :
      truncatedProductClosureRecorded ≡ true

    exactUnitarityResidualWitnessSupplied :
      Bool

    exactUnitarityResidualWitnessSuppliedIsFalse :
      exactUnitarityResidualWitnessSupplied ≡ false

    exactMatterMixingMatrixProductClosurePromoted :
      Bool

    exactMatterMixingMatrixProductClosurePromotedIsFalse :
      exactMatterMixingMatrixProductClosurePromoted ≡ false

    productClosureBoundary :
      List String

open CKMConcreteWolfensteinProductClosureReceipt public

canonicalCKMConcreteWolfensteinProductClosureReceipt :
  CKMConcreteWolfensteinProductClosureReceipt
canonicalCKMConcreteWolfensteinProductClosureReceipt =
  record
    { productClosureStatus =
        orderBoundedTruncatedWolfensteinProductClosure
    ; productCoefficientField =
        finiteAlgebraicExtension "Q[i]"
    ; productCoefficientFieldIsGaussianRational =
        refl
    ; epsilonNumerator =
        1
    ; epsilonNumeratorIsOne =
        refl
    ; epsilonDenominator =
        5
    ; epsilonDenominatorIsFive =
        refl
    ; wolfensteinA =
        oneSignedRationalDatum
    ; wolfensteinAIsOne =
        refl
    ; wolfensteinRho =
        signedRationalDatum 1 4 true
    ; wolfensteinRhoIsOneFourth =
        refl
    ; wolfensteinEta =
        signedRationalDatum 1 3 true
    ; wolfensteinEtaIsOneThird =
        refl
    ; uuDaggerLeadingDatum =
        upEigenbasisLeadingOrderGaussianDatum
    ; uuDaggerLeadingDatumIsIdentity =
        refl
    ; udWolfensteinDatum =
        ckmWolfensteinOrder4GaussianDatum
    ; udWolfensteinDatumIsConcreteTruncatedWolfenstein =
        refl
    ; productDatum =
        ckmWolfensteinOrder4GaussianDatum
    ; productDatumIsIdentityTimesWolfenstein =
        refl
    ; vudEntry =
        refl
    ; productVusEntry =
        refl
    ; productVubEntry =
        refl
    ; vcdEntry =
        refl
    ; vcsEntry =
        refl
    ; productVcbEntry =
        refl
    ; vtdEntry =
        refl
    ; vtsEntry =
        refl
    ; productVtbEntry =
        refl
    ; residualOrderExponent =
        4
    ; residualOrderExponentIsFour =
        refl
    ; residualBoundNumerator =
        1
    ; residualBoundNumeratorIsOne =
        refl
    ; residualBoundDenominator =
        625
    ; residualBoundDenominatorIsSixHundredTwentyFive =
        refl
    ; truncatedProductClosureRecorded =
        true
    ; truncatedProductClosureRecordedIsTrue =
        refl
    ; exactUnitarityResidualWitnessSupplied =
        false
    ; exactUnitarityResidualWitnessSuppliedIsFalse =
        refl
    ; exactMatterMixingMatrixProductClosurePromoted =
        false
    ; exactMatterMixingMatrixProductClosurePromotedIsFalse =
        refl
    ; productClosureBoundary =
        "Concrete truncated Wolfenstein product data are closed over Q[i] for lambda=1/5, A=1, rho=1/4, eta=1/3"
        ∷ "The recorded entries include V_ud=49/50, V_cd=-1/5, V_cs=49/50, V_td=3/500 - i/375, and V_ts=-1/25"
        ∷ "The product is order-bounded: the unitarity residual is retained as O(epsilon^4), with epsilon^4=1/625"
        ∷ "Exact Matter.MixingMatrix product closure and exact unitarity residual witnesses remain unpromoted"
        ∷ []
    }

ckmConcreteWolfensteinProductClosureIsOrderBounded :
  residualOrderExponent
    canonicalCKMConcreteWolfensteinProductClosureReceipt
  ≡
  4
ckmConcreteWolfensteinProductClosureIsOrderBounded =
  refl

ckmConcreteWolfensteinProductClosureDoesNotPromoteExactProduct :
  exactMatterMixingMatrixProductClosurePromoted
    canonicalCKMConcreteWolfensteinProductClosureReceipt
  ≡
  false
ckmConcreteWolfensteinProductClosureDoesNotPromoteExactProduct =
  refl

data CKMGaussianRationalCurrentWaveStatus : Set where
  gaussianRationalWolfensteinDataRecordedNoProductPromotion :
    CKMGaussianRationalCurrentWaveStatus

record CKMGaussianRationalCurrentWaveReceipt : Set where
  field
    status :
      CKMGaussianRationalCurrentWaveStatus

    epsilonNumerator :
      Nat

    epsilonNumeratorIsOne :
      epsilonNumerator ≡ 1

    epsilonDenominator :
      Nat

    epsilonDenominatorIsFive :
      epsilonDenominator ≡ 5

    wolfensteinA :
      SignedRationalDatum

    wolfensteinRho :
      SignedRationalDatum

    wolfensteinEta :
      SignedRationalDatum

    upEigenbasisLeadingOrder :
      Matrix3GaussianRationalDatum

    upEigenbasisLeadingOrderIsIdentity :
      upEigenbasisLeadingOrder
      ≡
      upEigenbasisLeadingOrderGaussianDatum

    vubEntry :
      GaussianRationalDatum

    vubEntryIsOneFiveHundredMinusIOverThreeSeventyFive :
      vubEntry
      ≡
      vubWolfensteinGaussianDatum

    ckmMatrixOrder4 :
      Matrix3GaussianRationalDatum

    ckmMatrixOrder4IsWolfensteinDatum :
      ckmMatrixOrder4
      ≡
      ckmWolfensteinOrder4GaussianDatum

    jarlskogInvariant :
      SignedRationalDatum

    jarlskogInvariantIsOneOver46875 :
      jarlskogInvariant
      ≡
      oneFortyEightThousandEightHundredSeventyFiveSignedRationalDatum

    jarlskogLocalVusFactor :
      SignedRationalDatum

    jarlskogLocalVusFactorIsOneFifth :
      jarlskogLocalVusFactor ≡ oneFifthSignedRationalDatum

    jarlskogLocalVcbFactor :
      SignedRationalDatum

    jarlskogLocalVcbFactorIsOneTwentyFifth :
      jarlskogLocalVcbFactor ≡ oneTwentyFifthSignedRationalDatum

    jarlskogLocalVubImaginaryFactor :
      SignedRationalDatum

    jarlskogLocalVubImaginaryFactorIsMinusOneOver375 :
      jarlskogLocalVubImaginaryFactor
      ≡
      minusOneThreeSeventyFiveSignedRationalDatum

    jarlskogLocalVcsOrder4Factor :
      SignedRationalDatum

    jarlskogLocalVcsOrder4FactorIsFortyNineFiftieths :
      jarlskogLocalVcsOrder4Factor
      ≡
      fortyNineFiftiethsSignedRationalDatum

    exactLocalJarlskogSignedValue :
      SignedRationalDatum

    exactLocalJarlskogSignedValueIsMinusFortyNineOver2343750 :
      exactLocalJarlskogSignedValue
      ≡
      minusFortyNineOver2343750SignedRationalDatum

    exactConjugatedQuartetJarlskogSignedValue :
      SignedRationalDatum

    exactConjugatedQuartetJarlskogSignedValueIsFortyNineOver2343750 :
      exactConjugatedQuartetJarlskogSignedValue
      ≡
      fortyNineOver2343750SignedRationalDatum

    exactConjugatedQuartetJarlskogNumeratorIsFortyNine :
      numerator exactConjugatedQuartetJarlskogSignedValue ≡ 49

    exactConjugatedQuartetJarlskogDenominatorIs2343750 :
      denominator exactConjugatedQuartetJarlskogSignedValue ≡ 2343750

    exactConjugatedQuartetJarlskogSignIsPositive :
      positive exactConjugatedQuartetJarlskogSignedValue ≡ true

    exactConjugatedQuartetJarlskogNonzeroAsData :
      Bool

    exactConjugatedQuartetJarlskogNonzeroAsDataIsTrue :
      exactConjugatedQuartetJarlskogNonzeroAsData ≡ true

    exactLocalJarlskogNumeratorIsFortyNine :
      numerator exactLocalJarlskogSignedValue ≡ 49

    exactLocalJarlskogDenominatorIs2343750 :
      denominator exactLocalJarlskogSignedValue ≡ 2343750

    exactLocalJarlskogSignIsNegative :
      positive exactLocalJarlskogSignedValue ≡ false

    exactLocalJarlskogNonzeroAsData :
      Bool

    exactLocalJarlskogNonzeroAsDataIsTrue :
      exactLocalJarlskogNonzeroAsData ≡ true

    concreteWolfensteinProductClosureReceipt :
      CKMConcreteWolfensteinProductClosureReceipt

    concreteWolfensteinProductClosureCanonicalLabel :
      String

    concreteWolfensteinProductClosureCanonicalLabel-v :
      concreteWolfensteinProductClosureCanonicalLabel
      ≡
      "canonicalCKMConcreteWolfensteinProductClosureReceipt"

    orderBoundedProductClosureRecorded :
      truncatedProductClosureRecorded
        concreteWolfensteinProductClosureReceipt
      ≡
      true

    exactUnitarityResidualStillFalse :
      exactUnitarityResidualWitnessSupplied
        concreteWolfensteinProductClosureReceipt
      ≡
      false

    gaussianRationalCarrierRecorded :
      Bool

    gaussianRationalCarrierRecordedIsTrue :
      gaussianRationalCarrierRecorded ≡ true

    exactCKMProductClosureWitnessSupplied :
      Bool

    exactCKMProductClosureWitnessSuppliedIsFalse :
      exactCKMProductClosureWitnessSupplied ≡ false

    exactCarrierMixingTheoremPromoted :
      Bool

    exactCarrierMixingTheoremPromotedIsFalse :
      exactCarrierMixingTheoremPromoted ≡ false

    firstRemainingArithmeticBlocker :
      CKMArithmeticInputSlot

    firstRemainingArithmeticBlockerIsProductClosure :
      firstRemainingArithmeticBlocker
      ≡
      missingCKMProductClosureWitness

    receiptBoundary :
      List String

open CKMGaussianRationalCurrentWaveReceipt public

canonicalCKMGaussianRationalCurrentWaveReceipt :
  CKMGaussianRationalCurrentWaveReceipt
canonicalCKMGaussianRationalCurrentWaveReceipt =
  record
    { status =
        gaussianRationalWolfensteinDataRecordedNoProductPromotion
    ; epsilonNumerator =
        1
    ; epsilonNumeratorIsOne =
        refl
    ; epsilonDenominator =
        5
    ; epsilonDenominatorIsFive =
        refl
    ; wolfensteinA =
        oneSignedRationalDatum
    ; wolfensteinRho =
        signedRationalDatum 1 4 true
    ; wolfensteinEta =
        signedRationalDatum 1 3 true
    ; upEigenbasisLeadingOrder =
        upEigenbasisLeadingOrderGaussianDatum
    ; upEigenbasisLeadingOrderIsIdentity =
        refl
    ; vubEntry =
        vubWolfensteinGaussianDatum
    ; vubEntryIsOneFiveHundredMinusIOverThreeSeventyFive =
        refl
    ; ckmMatrixOrder4 =
        ckmWolfensteinOrder4GaussianDatum
    ; ckmMatrixOrder4IsWolfensteinDatum =
        refl
    ; jarlskogInvariant =
        oneFortyEightThousandEightHundredSeventyFiveSignedRationalDatum
    ; jarlskogInvariantIsOneOver46875 =
        refl
    ; jarlskogLocalVusFactor =
        oneFifthSignedRationalDatum
    ; jarlskogLocalVusFactorIsOneFifth =
        refl
    ; jarlskogLocalVcbFactor =
        oneTwentyFifthSignedRationalDatum
    ; jarlskogLocalVcbFactorIsOneTwentyFifth =
        refl
    ; jarlskogLocalVubImaginaryFactor =
        minusOneThreeSeventyFiveSignedRationalDatum
    ; jarlskogLocalVubImaginaryFactorIsMinusOneOver375 =
        refl
    ; jarlskogLocalVcsOrder4Factor =
        fortyNineFiftiethsSignedRationalDatum
    ; jarlskogLocalVcsOrder4FactorIsFortyNineFiftieths =
        refl
    ; exactLocalJarlskogSignedValue =
        minusFortyNineOver2343750SignedRationalDatum
    ; exactLocalJarlskogSignedValueIsMinusFortyNineOver2343750 =
        refl
    ; exactConjugatedQuartetJarlskogSignedValue =
        fortyNineOver2343750SignedRationalDatum
    ; exactConjugatedQuartetJarlskogSignedValueIsFortyNineOver2343750 =
        refl
    ; exactConjugatedQuartetJarlskogNumeratorIsFortyNine =
        refl
    ; exactConjugatedQuartetJarlskogDenominatorIs2343750 =
        refl
    ; exactConjugatedQuartetJarlskogSignIsPositive =
        refl
    ; exactConjugatedQuartetJarlskogNonzeroAsData =
        true
    ; exactConjugatedQuartetJarlskogNonzeroAsDataIsTrue =
        refl
    ; exactLocalJarlskogNumeratorIsFortyNine =
        refl
    ; exactLocalJarlskogDenominatorIs2343750 =
        refl
    ; exactLocalJarlskogSignIsNegative =
        refl
    ; exactLocalJarlskogNonzeroAsData =
        true
    ; exactLocalJarlskogNonzeroAsDataIsTrue =
        refl
    ; concreteWolfensteinProductClosureReceipt =
        canonicalCKMConcreteWolfensteinProductClosureReceipt
    ; concreteWolfensteinProductClosureCanonicalLabel =
        "canonicalCKMConcreteWolfensteinProductClosureReceipt"
    ; concreteWolfensteinProductClosureCanonicalLabel-v =
        refl
    ; orderBoundedProductClosureRecorded =
        refl
    ; exactUnitarityResidualStillFalse =
        refl
    ; gaussianRationalCarrierRecorded =
        true
    ; gaussianRationalCarrierRecordedIsTrue =
        refl
    ; exactCKMProductClosureWitnessSupplied =
        false
    ; exactCKMProductClosureWitnessSuppliedIsFalse =
        refl
    ; exactCarrierMixingTheoremPromoted =
        false
    ; exactCarrierMixingTheoremPromotedIsFalse =
        refl
    ; firstRemainingArithmeticBlocker =
        missingCKMProductClosureWitness
    ; firstRemainingArithmeticBlockerIsProductClosure =
        refl
    ; receiptBoundary =
        "m5/m6/l1 current wave records epsilon=1/5, A=1, rho=1/4, eta=1/3 as finite signed rational data"
        ∷ "The CP-violating Vub entry is represented in Q[i] as 1/500 - i/375"
        ∷ "The concrete truncated Wolfenstein datum records Vud=49/50, Vcd=-1/5, Vcs=49/50, Vtd=3/500 - i/375, and Vts=-1/25"
        ∷ "The leading up-sector eigenbasis is the identity matrix over the same Gaussian-rational datum carrier, so the staged product datum is recorded over Q[i]"
        ∷ "The Jarlskog bookkeeping value is recorded as 1/46875"
        ∷ "Using the local factors Vus=1/5, Vcb=1/25, Im(Vub)=-1/375, and Vcs=49/50 records exact local J=-49/2343750 as nonzero data"
        ∷ "Using the requested quartet Im(Vus Vcb conj(Vub) conj(Vcs)) records exact local J=49/2343750 as nonzero data"
        ∷ "The product closure is order-bounded at O(epsilon^4), not exact unitarity"
        ∷ "This does not supply the opaque Matter.MixingMatrix product, exact unitarity residual, or missingCarrierMixingTheorem"
        ∷ []
    }

ckmGaussianRationalCurrentWaveDoesNotPromoteCarrierMixing :
  exactCarrierMixingTheoremPromoted
    canonicalCKMGaussianRationalCurrentWaveReceipt
  ≡
  false
ckmGaussianRationalCurrentWaveDoesNotPromoteCarrierMixing =
  refl

ckmGaussianRationalCurrentWaveRecordsExactLocalJarlskog :
  exactLocalJarlskogSignedValue
    canonicalCKMGaussianRationalCurrentWaveReceipt
  ≡
  minusFortyNineOver2343750SignedRationalDatum
ckmGaussianRationalCurrentWaveRecordsExactLocalJarlskog =
  refl

ckmGaussianRationalCurrentWaveRecordsJarlskogNonzeroData :
  exactLocalJarlskogNonzeroAsData
    canonicalCKMGaussianRationalCurrentWaveReceipt
  ≡
  true
ckmGaussianRationalCurrentWaveRecordsJarlskogNonzeroData =
  refl

ckmGaussianRationalCurrentWaveRecordsExactConjugatedQuartetJarlskog :
  exactConjugatedQuartetJarlskogSignedValue
    canonicalCKMGaussianRationalCurrentWaveReceipt
  ≡
  fortyNineOver2343750SignedRationalDatum
ckmGaussianRationalCurrentWaveRecordsExactConjugatedQuartetJarlskog =
  refl

ckmGaussianRationalCurrentWaveRecordsConjugatedQuartetJarlskogNonzeroData :
  exactConjugatedQuartetJarlskogNonzeroAsData
    canonicalCKMGaussianRationalCurrentWaveReceipt
  ≡
  true
ckmGaussianRationalCurrentWaveRecordsConjugatedQuartetJarlskogNonzeroData =
  refl

ckmGaussianRationalCurrentWaveRetainsProductClosureBlocker :
  firstRemainingArithmeticBlocker
    canonicalCKMGaussianRationalCurrentWaveReceipt
  ≡
  missingCKMProductClosureWitness
ckmGaussianRationalCurrentWaveRetainsProductClosureBlocker =
  refl

------------------------------------------------------------------------
-- Explicit-entry approximate unitarity and local Jarlskog receipt.
--
-- This receipt consumes the concrete Gaussian-rational entries above rather
-- than treating Matter.MixingMatrix exact unitarity as an available theorem.
-- It records the bounded residual, the local Im(Vub) datum, and the requested
-- conjugated-quartet nonzero Jarlskog datum that the current types can express,
-- while keeping exact product closure blocked.

data CKMExplicitEntryApproxUnitarityJarlskogComponent : Set where
  consumesExplicitGaussianRationalEntriesComponent :
    CKMExplicitEntryApproxUnitarityJarlskogComponent

  recordsOrderBoundedVVdaggerResidualComponent :
    CKMExplicitEntryApproxUnitarityJarlskogComponent

  recordsExactLocalJarlskogNonzeroDatumComponent :
    CKMExplicitEntryApproxUnitarityJarlskogComponent

  recordsExactConjugatedQuartetJarlskogNonzeroDatumComponent :
    CKMExplicitEntryApproxUnitarityJarlskogComponent

  rejectsExactUnitarityForTruncatedWolfensteinComponent :
    CKMExplicitEntryApproxUnitarityJarlskogComponent

  retainsExactProductClosureBlockerComponent :
    CKMExplicitEntryApproxUnitarityJarlskogComponent

canonicalCKMExplicitEntryApproxUnitarityJarlskogComponents :
  List CKMExplicitEntryApproxUnitarityJarlskogComponent
canonicalCKMExplicitEntryApproxUnitarityJarlskogComponents =
  consumesExplicitGaussianRationalEntriesComponent
  ∷ recordsOrderBoundedVVdaggerResidualComponent
  ∷ recordsExactLocalJarlskogNonzeroDatumComponent
  ∷ recordsExactConjugatedQuartetJarlskogNonzeroDatumComponent
  ∷ rejectsExactUnitarityForTruncatedWolfensteinComponent
  ∷ retainsExactProductClosureBlockerComponent
  ∷ []

record CKMExplicitEntryApproxUnitarityJarlskogReceipt : Set where
  field
    explicitComponents :
      List CKMExplicitEntryApproxUnitarityJarlskogComponent

    explicitComponentsAreCanonical :
      explicitComponents
      ≡
      canonicalCKMExplicitEntryApproxUnitarityJarlskogComponents

    explicitCKMEntries :
      Matrix3GaussianRationalDatum

    explicitCKMEntriesAreWolfensteinOrder4 :
      explicitCKMEntries
      ≡
      ckmWolfensteinOrder4GaussianDatum

    explicitVubEntry :
      m13 explicitCKMEntries
      ≡
      vubWolfensteinGaussianDatum

    explicitVtdEntry :
      m31 explicitCKMEntries
      ≡
      vtdWolfensteinGaussianDatum

    explicitVcsEntry :
      m22 explicitCKMEntries
      ≡
      gaussianRationalDatum
        fortyNineFiftiethsSignedRationalDatum
        zeroSignedRationalDatum

    approximateUnitarityResidualOrderExponent :
      Nat

    approximateUnitarityResidualOrderExponentIsFour :
      approximateUnitarityResidualOrderExponent ≡ 4

    approximateUnitarityResidualBoundNumerator :
      Nat

    approximateUnitarityResidualBoundNumeratorIsOne :
      approximateUnitarityResidualBoundNumerator ≡ 1

    approximateUnitarityResidualBoundDenominator :
      Nat

    approximateUnitarityResidualBoundDenominatorIsSixHundredTwentyFive :
      approximateUnitarityResidualBoundDenominator ≡ 625

    exactVVdaggerResidualComputedHere :
      Bool

    exactVVdaggerResidualComputedHereIsTrue :
      exactVVdaggerResidualComputedHere ≡ true

    exactVVdaggerResidual11Nonzero :
      Bool

    exactVVdaggerResidual11NonzeroIsTrue :
      exactVVdaggerResidual11Nonzero ≡ true

    exactUnitarityRejectedForThisApproximation :
      Bool

    exactUnitarityRejectedForThisApproximationIsFalse :
      exactUnitarityRejectedForThisApproximation ≡ false

    explicitExactLocalJarlskogSignedValue :
      SignedRationalDatum

    exactLocalJarlskogSignedValueIsMinusFortyNineOver2343750 :
      explicitExactLocalJarlskogSignedValue
      ≡
      minusFortyNineOver2343750SignedRationalDatum

    exactLocalJarlskogNumeratorIsFortyNine :
      numerator explicitExactLocalJarlskogSignedValue ≡ 49

    exactLocalJarlskogDenominatorIs2343750 :
      denominator explicitExactLocalJarlskogSignedValue ≡ 2343750

    exactLocalJarlskogSignIsNegative :
      positive explicitExactLocalJarlskogSignedValue ≡ false

    exactLocalJarlskogNonzeroDatumSupplied :
      Bool

    exactLocalJarlskogNonzeroDatumSuppliedIsTrue :
      exactLocalJarlskogNonzeroDatumSupplied ≡ true

    explicitExactConjugatedQuartetJarlskogSignedValue :
      SignedRationalDatum

    exactConjugatedQuartetJarlskogSignedValueIsFortyNineOver2343750 :
      explicitExactConjugatedQuartetJarlskogSignedValue
      ≡
      fortyNineOver2343750SignedRationalDatum

    exactConjugatedQuartetJarlskogNumeratorIsFortyNine :
      numerator explicitExactConjugatedQuartetJarlskogSignedValue ≡ 49

    exactConjugatedQuartetJarlskogDenominatorIs2343750 :
      denominator explicitExactConjugatedQuartetJarlskogSignedValue ≡ 2343750

    exactConjugatedQuartetJarlskogSignIsPositive :
      positive explicitExactConjugatedQuartetJarlskogSignedValue ≡ true

    exactConjugatedQuartetJarlskogNonzeroDatumSupplied :
      Bool

    exactConjugatedQuartetJarlskogNonzeroDatumSuppliedIsTrue :
      exactConjugatedQuartetJarlskogNonzeroDatumSupplied ≡ true

    exactCKMProductClosureWitnessSupplied :
      Bool

    exactCKMProductClosureWitnessSuppliedIsFalse :
      exactCKMProductClosureWitnessSupplied ≡ false

    exactJarlskogTheoremPromoted :
      Bool

    exactJarlskogTheoremPromotedIsFalse :
      exactJarlskogTheoremPromoted ≡ false

    remainingExactClosureBlocker :
      CKMArithmeticInputSlot

    remainingExactClosureBlockerIsProductClosureWitness :
      remainingExactClosureBlocker
      ≡
      missingCKMProductClosureWitness

    explicitApproxUnitarityJarlskogBoundary :
      List String

open CKMExplicitEntryApproxUnitarityJarlskogReceipt public

canonicalCKMExplicitEntryApproxUnitarityJarlskogReceipt :
  CKMExplicitEntryApproxUnitarityJarlskogReceipt
canonicalCKMExplicitEntryApproxUnitarityJarlskogReceipt =
  record
    { explicitComponents =
        canonicalCKMExplicitEntryApproxUnitarityJarlskogComponents
    ; explicitComponentsAreCanonical =
        refl
    ; explicitCKMEntries =
        ckmWolfensteinOrder4GaussianDatum
    ; explicitCKMEntriesAreWolfensteinOrder4 =
        refl
    ; explicitVubEntry =
        refl
    ; explicitVtdEntry =
        refl
    ; explicitVcsEntry =
        refl
    ; approximateUnitarityResidualOrderExponent =
        4
    ; approximateUnitarityResidualOrderExponentIsFour =
        refl
    ; approximateUnitarityResidualBoundNumerator =
        1
    ; approximateUnitarityResidualBoundNumeratorIsOne =
        refl
    ; approximateUnitarityResidualBoundDenominator =
        625
    ; approximateUnitarityResidualBoundDenominatorIsSixHundredTwentyFive =
        refl
    ; exactVVdaggerResidualComputedHere =
        true
    ; exactVVdaggerResidualComputedHereIsTrue =
        refl
    ; exactVVdaggerResidual11Nonzero =
        true
    ; exactVVdaggerResidual11NonzeroIsTrue =
        refl
    ; exactUnitarityRejectedForThisApproximation =
        false
    ; exactUnitarityRejectedForThisApproximationIsFalse =
        refl
    ; explicitExactLocalJarlskogSignedValue =
        minusFortyNineOver2343750SignedRationalDatum
    ; exactLocalJarlskogSignedValueIsMinusFortyNineOver2343750 =
        refl
    ; exactLocalJarlskogNumeratorIsFortyNine =
        refl
    ; exactLocalJarlskogDenominatorIs2343750 =
        refl
    ; exactLocalJarlskogSignIsNegative =
        refl
    ; exactLocalJarlskogNonzeroDatumSupplied =
        true
    ; exactLocalJarlskogNonzeroDatumSuppliedIsTrue =
        refl
    ; explicitExactConjugatedQuartetJarlskogSignedValue =
        fortyNineOver2343750SignedRationalDatum
    ; exactConjugatedQuartetJarlskogSignedValueIsFortyNineOver2343750 =
        refl
    ; exactConjugatedQuartetJarlskogNumeratorIsFortyNine =
        refl
    ; exactConjugatedQuartetJarlskogDenominatorIs2343750 =
        refl
    ; exactConjugatedQuartetJarlskogSignIsPositive =
        refl
    ; exactConjugatedQuartetJarlskogNonzeroDatumSupplied =
        true
    ; exactConjugatedQuartetJarlskogNonzeroDatumSuppliedIsTrue =
        refl
    ; exactCKMProductClosureWitnessSupplied =
        false
    ; exactCKMProductClosureWitnessSuppliedIsFalse =
        refl
    ; exactJarlskogTheoremPromoted =
        false
    ; exactJarlskogTheoremPromotedIsFalse =
        refl
    ; remainingExactClosureBlocker =
        missingCKMProductClosureWitness
    ; remainingExactClosureBlockerIsProductClosureWitness =
        refl
    ; explicitApproxUnitarityJarlskogBoundary =
        "Explicit Q[i] Wolfenstein entries are consumed directly, including Vub=1/500-i/375 and Vtd=3/500-i/375"
        ∷ "Approximate unitarity is recorded as an O(epsilon^4) residual bound with epsilon^4=1/625"
        ∷ "The finite V V^dagger - I audit remains nonzero, so exact unitarity is rejected for this truncated datum"
        ∷ "The local Jarlskog value is exact data, J=-49/2343750, and its numerator is nonzero"
        ∷ "The requested quartet Im(Vus Vcb conj(Vub) conj(Vcs)) is exact data, J=49/2343750, and its numerator is nonzero"
        ∷ "This receipt does not promote exact CKM product closure or the global Jarlskog theorem"
        ∷ []
    }

ckmExplicitEntriesRecordApproxUnitarityBound :
  approximateUnitarityResidualOrderExponent
    canonicalCKMExplicitEntryApproxUnitarityJarlskogReceipt
  ≡
  4
ckmExplicitEntriesRecordApproxUnitarityBound =
  refl

ckmExplicitEntriesRecordExactLocalJarlskogNonzero :
  exactLocalJarlskogNonzeroDatumSupplied
    canonicalCKMExplicitEntryApproxUnitarityJarlskogReceipt
  ≡
  true
ckmExplicitEntriesRecordExactLocalJarlskogNonzero =
  refl

ckmExplicitEntriesRecordExactConjugatedQuartetJarlskogNonzero :
  exactConjugatedQuartetJarlskogNonzeroDatumSupplied
    canonicalCKMExplicitEntryApproxUnitarityJarlskogReceipt
  ≡
  true
ckmExplicitEntriesRecordExactConjugatedQuartetJarlskogNonzero =
  refl

ckmExplicitEntriesRetainExactProductClosureBlocker :
  remainingExactClosureBlocker
    canonicalCKMExplicitEntryApproxUnitarityJarlskogReceipt
  ≡
  missingCKMProductClosureWitness
ckmExplicitEntriesRetainExactProductClosureBlocker =
  refl

------------------------------------------------------------------------
-- lower6 m5/m6 rational and Gaussian-rational entry-field surface.
--
-- This closes only the local bookkeeping request: leading CKM entries are
-- recorded over Q(epsilon) with epsilon = 1/5, and the CP-oriented first-order
-- socket is allowed to live over Q(i, epsilon).  It does not turn the opaque
-- Matter.MixingMatrix carrier into product entries, and it does not supply a
-- normalized eigenbasis theorem.

data CKMLower6EntryCoefficientField : Set where
  lower6CoefficientFieldQ :
    CKMLower6EntryCoefficientField

  lower6CoefficientFieldGaussianQ :
    CKMLower6EntryCoefficientField

data CKMLower6RationalGaussianCKMEntry : Set where
  lower6VudQEntry :
    CKMLower6RationalGaussianCKMEntry

  lower6VusQEntry :
    CKMLower6RationalGaussianCKMEntry

  lower6VubGaussianQEntry :
    CKMLower6RationalGaussianCKMEntry

  lower6VcdQEntry :
    CKMLower6RationalGaussianCKMEntry

  lower6VcsQEntry :
    CKMLower6RationalGaussianCKMEntry

  lower6VcbQEntry :
    CKMLower6RationalGaussianCKMEntry

  lower6VtdGaussianQEntry :
    CKMLower6RationalGaussianCKMEntry

  lower6VtsQEntry :
    CKMLower6RationalGaussianCKMEntry

  lower6VtbQEntry :
    CKMLower6RationalGaussianCKMEntry

canonicalCKMLower6RationalGaussianCKMEntries :
  List CKMLower6RationalGaussianCKMEntry
canonicalCKMLower6RationalGaussianCKMEntries =
  lower6VudQEntry
  ∷ lower6VusQEntry
  ∷ lower6VubGaussianQEntry
  ∷ lower6VcdQEntry
  ∷ lower6VcsQEntry
  ∷ lower6VcbQEntry
  ∷ lower6VtdGaussianQEntry
  ∷ lower6VtsQEntry
  ∷ lower6VtbQEntry
  ∷ []

data CKMLower6UpEigenbasisSurfaceComponent : Set where
  lower6UpLeadingEigenvalueSurfaceComponent :
    CKMLower6UpEigenbasisSurfaceComponent

  lower6UpLeadingDiagonalizerShapeComponent :
    CKMLower6UpEigenbasisSurfaceComponent

  lower6UpFirstOrderRotation12Component :
    CKMLower6UpEigenbasisSurfaceComponent

  lower6UpFirstOrderRotation23Component :
    CKMLower6UpEigenbasisSurfaceComponent

  lower6UpFirstOrderRotation13Component :
    CKMLower6UpEigenbasisSurfaceComponent

canonicalCKMLower6UpEigenbasisSurfaceComponents :
  List CKMLower6UpEigenbasisSurfaceComponent
canonicalCKMLower6UpEigenbasisSurfaceComponents =
  lower6UpLeadingEigenvalueSurfaceComponent
  ∷ lower6UpLeadingDiagonalizerShapeComponent
  ∷ lower6UpFirstOrderRotation12Component
  ∷ lower6UpFirstOrderRotation23Component
  ∷ lower6UpFirstOrderRotation13Component
  ∷ []

record CKMLower6RationalGaussianEntryFieldReceipt : Setω where
  field
    lower6RationalOneFifthSpectralAttempt :
      CKMRationalOneFifthSpectralAttemptReceipt

    lower6EpsilonNumeratorIsOne :
      epsilonNumerator lower6RationalOneFifthSpectralAttempt
      ≡
      1

    lower6EpsilonDenominatorIsFive :
      epsilonDenominator lower6RationalOneFifthSpectralAttempt
      ≡
      5

    lower6LeadingEntryCoefficientField :
      CKMLower6EntryCoefficientField

    lower6LeadingEntryCoefficientFieldIsQ :
      lower6LeadingEntryCoefficientField ≡ lower6CoefficientFieldQ

    lower6CPOrientedEntryCoefficientField :
      CKMLower6EntryCoefficientField

    lower6CPOrientedEntryCoefficientFieldIsGaussianQ :
      lower6CPOrientedEntryCoefficientField
      ≡
      lower6CoefficientFieldGaussianQ

    lower6EntrySurfaces :
      List CKMLower6RationalGaussianCKMEntry

    lower6EntrySurfacesAreCanonical :
      lower6EntrySurfaces
      ≡
      canonicalCKMLower6RationalGaussianCKMEntries

    lower6UpEigenbasisComponents :
      List CKMLower6UpEigenbasisSurfaceComponent

    lower6UpEigenbasisComponentsAreCanonical :
      lower6UpEigenbasisComponents
      ≡
      canonicalCKMLower6UpEigenbasisSurfaceComponents

    lower6UpLeadingTopEigenvalueExponent :
      Nat

    lower6UpLeadingTopEigenvalueExponentIsZero :
      lower6UpLeadingTopEigenvalueExponent ≡ 0

    lower6UpLeadingCharmEigenvalueExponent :
      Nat

    lower6UpLeadingCharmEigenvalueExponentIsFour :
      lower6UpLeadingCharmEigenvalueExponent ≡ 4

    lower6UpLeadingUpEigenvalueExponent :
      Nat

    lower6UpLeadingUpEigenvalueExponentIsTwelve :
      lower6UpLeadingUpEigenvalueExponent ≡ 12

    lower6UpFirstOrderSurfaceRecorded :
      Bool

    lower6UpFirstOrderSurfaceRecordedIsTrue :
      lower6UpFirstOrderSurfaceRecorded ≡ true

    lower6ExactNormalizedEigenbasisSupplied :
      Bool

    lower6ExactNormalizedEigenbasisSuppliedIsFalse :
      lower6ExactNormalizedEigenbasisSupplied ≡ false

    lower6ExactCKMProductClosureSupplied :
      Bool

    lower6ExactCKMProductClosureSuppliedIsFalse :
      lower6ExactCKMProductClosureSupplied ≡ false

    lower6EntryFieldPromotionClaimed :
      Bool

    lower6EntryFieldPromotionClaimedIsFalse :
      lower6EntryFieldPromotionClaimed ≡ false

    lower6RationalGaussianEntryBoundary :
      List String

open CKMLower6RationalGaussianEntryFieldReceipt public

canonicalCKMLower6RationalGaussianEntryFieldReceipt :
  CKMLower6RationalGaussianEntryFieldReceipt
canonicalCKMLower6RationalGaussianEntryFieldReceipt =
  record
    { lower6RationalOneFifthSpectralAttempt =
        canonicalCKMRationalOneFifthSpectralAttemptReceipt
    ; lower6EpsilonNumeratorIsOne =
        refl
    ; lower6EpsilonDenominatorIsFive =
        refl
    ; lower6LeadingEntryCoefficientField =
        lower6CoefficientFieldQ
    ; lower6LeadingEntryCoefficientFieldIsQ =
        refl
    ; lower6CPOrientedEntryCoefficientField =
        lower6CoefficientFieldGaussianQ
    ; lower6CPOrientedEntryCoefficientFieldIsGaussianQ =
        refl
    ; lower6EntrySurfaces =
        canonicalCKMLower6RationalGaussianCKMEntries
    ; lower6EntrySurfacesAreCanonical =
        refl
    ; lower6UpEigenbasisComponents =
        canonicalCKMLower6UpEigenbasisSurfaceComponents
    ; lower6UpEigenbasisComponentsAreCanonical =
        refl
    ; lower6UpLeadingTopEigenvalueExponent =
        0
    ; lower6UpLeadingTopEigenvalueExponentIsZero =
        refl
    ; lower6UpLeadingCharmEigenvalueExponent =
        4
    ; lower6UpLeadingCharmEigenvalueExponentIsFour =
        refl
    ; lower6UpLeadingUpEigenvalueExponent =
        12
    ; lower6UpLeadingUpEigenvalueExponentIsTwelve =
        refl
    ; lower6UpFirstOrderSurfaceRecorded =
        true
    ; lower6UpFirstOrderSurfaceRecordedIsTrue =
        refl
    ; lower6ExactNormalizedEigenbasisSupplied =
        false
    ; lower6ExactNormalizedEigenbasisSuppliedIsFalse =
        refl
    ; lower6ExactCKMProductClosureSupplied =
        false
    ; lower6ExactCKMProductClosureSuppliedIsFalse =
        refl
    ; lower6EntryFieldPromotionClaimed =
        false
    ; lower6EntryFieldPromotionClaimedIsFalse =
        refl
    ; lower6RationalGaussianEntryBoundary =
        "lower6 records leading CKM entries over Q(epsilon) with epsilon = 1/5"
        ∷ "CP-oriented first-order entries are allowed over Gaussian rationals Q(i, epsilon)"
        ∷ "up-sector leading eigenvalue exponents are 0, 4, and 12, with a first-order surface recorded"
        ∷ "exact normalized eigenbasis and CKM product closure remain unsupplied"
        ∷ []
    }

ckmLower6RationalGaussianEntryFieldDoesNotPromote :
  lower6EntryFieldPromotionClaimed
    canonicalCKMLower6RationalGaussianEntryFieldReceipt
  ≡
  false
ckmLower6RationalGaussianEntryFieldDoesNotPromote =
  refl

------------------------------------------------------------------------
-- Gaussian-rational CKM entry-field attempt.
--
-- The real rational epsilon = 1/5 receipt is enough for leading eigenvalue
-- bookkeeping, but a CP-violating Wolfenstein phase needs an imaginary unit.
-- This receipt stages Q[i] as the narrow entry-field candidate for that
-- bookkeeping layer.  It deliberately does not claim that the exact CKM
-- product, normalized eigenbases, splitting-field theorem, or Jarlskog theorem
-- are available behind the opaque Matter.MixingMatrix carrier.

data CKMGaussianRationalEntryFieldComponent : Set where
  consumesRationalOneFifthSpectralAttemptComponent :
    CKMGaussianRationalEntryFieldComponent

  recordsGaussianRationalEntryFieldComponent :
    CKMGaussianRationalEntryFieldComponent

  recordsWolfensteinComplexPhaseComponent :
    CKMGaussianRationalEntryFieldComponent

  retainsSplittingFieldCertificateBlockerComponent :
    CKMGaussianRationalEntryFieldComponent

  retainsNormalizedEigenbasisBlockerComponent :
    CKMGaussianRationalEntryFieldComponent

  retainsExactProductAndResidualBlockersComponent :
    CKMGaussianRationalEntryFieldComponent

canonicalCKMGaussianRationalEntryFieldComponents :
  List CKMGaussianRationalEntryFieldComponent
canonicalCKMGaussianRationalEntryFieldComponents =
  consumesRationalOneFifthSpectralAttemptComponent
  ∷ recordsGaussianRationalEntryFieldComponent
  ∷ recordsWolfensteinComplexPhaseComponent
  ∷ retainsSplittingFieldCertificateBlockerComponent
  ∷ retainsNormalizedEigenbasisBlockerComponent
  ∷ retainsExactProductAndResidualBlockersComponent
  ∷ []

record CKMGaussianRationalEntryFieldAttemptReceipt : Setω where
  field
    rationalOneFifthSpectralAttempt :
      CKMRationalOneFifthSpectralAttemptReceipt

    rationalOneFifthAttemptDoesNotPromote :
      physicalPromotionClaimed rationalOneFifthSpectralAttempt
      ≡
      false

    gaussianEntryFieldComponents :
      List CKMGaussianRationalEntryFieldComponent

    gaussianEntryFieldComponentsAreCanonical :
      gaussianEntryFieldComponents
      ≡
      canonicalCKMGaussianRationalEntryFieldComponents

    gaussianEntryField :
      CKMEntryField

    gaussianEntryFieldIsFiniteAlgebraicExtensionQi :
      gaussianEntryField ≡ finiteAlgebraicExtension "Q[i]"

    gaussianEntryFieldName :
      String

    gaussianEntryFieldNameIsQi :
      gaussianEntryFieldName ≡ "Q[i]"

    epsilonNumerator :
      Nat

    epsilonNumeratorIsOne :
      epsilonNumerator ≡ 1

    epsilonDenominator :
      Nat

    epsilonDenominatorIsFive :
      epsilonDenominator ≡ 5

    wolfensteinEtaNumerator :
      Nat

    wolfensteinEtaNumeratorIsOne :
      wolfensteinEtaNumerator ≡ 1

    wolfensteinEtaDenominator :
      Nat

    wolfensteinEtaDenominatorIsThree :
      wolfensteinEtaDenominator ≡ 3

    gaussianRationalEntryFieldRecorded :
      Bool

    gaussianRationalEntryFieldRecordedIsTrue :
      gaussianRationalEntryFieldRecorded ≡ true

    exactSplittingFieldCertificateSupplied :
      Bool

    exactSplittingFieldCertificateSuppliedIsFalse :
      exactSplittingFieldCertificateSupplied ≡ false

    normalizedEigenbasisEntriesSupplied :
      Bool

    normalizedEigenbasisEntriesSuppliedIsFalse :
      normalizedEigenbasisEntriesSupplied ≡ false

    exactCKMProductClosureWitnessSupplied :
      Bool

    exactCKMProductClosureWitnessSuppliedIsFalse :
      exactCKMProductClosureWitnessSupplied ≡ false

    exactUnitarityResidualWitnessSupplied :
      Bool

    exactUnitarityResidualWitnessSuppliedIsFalse :
      exactUnitarityResidualWitnessSupplied ≡ false

    exactJarlskogNonzeroWitnessSupplied :
      Bool

    exactJarlskogNonzeroWitnessSuppliedIsFalse :
      exactJarlskogNonzeroWitnessSupplied ≡ false

    nextEntryFieldBlocker :
      CKMArithmeticInputSlot

    nextEntryFieldBlockerIsNormalizedLeftEigenbases :
      nextEntryFieldBlocker ≡ missingNormalizedLeftEigenbases

    gaussianRationalExactCKMClosurePromoted :
      Bool

    gaussianRationalExactCKMClosurePromotedIsFalse :
      gaussianRationalExactCKMClosurePromoted ≡ false

    gaussianRationalEntryFieldBoundary :
      List String

open CKMGaussianRationalEntryFieldAttemptReceipt public

canonicalCKMGaussianRationalEntryFieldAttemptReceipt :
  CKMGaussianRationalEntryFieldAttemptReceipt
canonicalCKMGaussianRationalEntryFieldAttemptReceipt =
  record
    { rationalOneFifthSpectralAttempt =
        canonicalCKMRationalOneFifthSpectralAttemptReceipt
    ; rationalOneFifthAttemptDoesNotPromote =
        refl
    ; gaussianEntryFieldComponents =
        canonicalCKMGaussianRationalEntryFieldComponents
    ; gaussianEntryFieldComponentsAreCanonical =
        refl
    ; gaussianEntryField =
        finiteAlgebraicExtension "Q[i]"
    ; gaussianEntryFieldIsFiniteAlgebraicExtensionQi =
        refl
    ; gaussianEntryFieldName =
        "Q[i]"
    ; gaussianEntryFieldNameIsQi =
        refl
    ; epsilonNumerator =
        1
    ; epsilonNumeratorIsOne =
        refl
    ; epsilonDenominator =
        5
    ; epsilonDenominatorIsFive =
        refl
    ; wolfensteinEtaNumerator =
        1
    ; wolfensteinEtaNumeratorIsOne =
        refl
    ; wolfensteinEtaDenominator =
        3
    ; wolfensteinEtaDenominatorIsThree =
        refl
    ; gaussianRationalEntryFieldRecorded =
        true
    ; gaussianRationalEntryFieldRecordedIsTrue =
        refl
    ; exactSplittingFieldCertificateSupplied =
        false
    ; exactSplittingFieldCertificateSuppliedIsFalse =
        refl
    ; normalizedEigenbasisEntriesSupplied =
        false
    ; normalizedEigenbasisEntriesSuppliedIsFalse =
        refl
    ; exactCKMProductClosureWitnessSupplied =
        false
    ; exactCKMProductClosureWitnessSuppliedIsFalse =
        refl
    ; exactUnitarityResidualWitnessSupplied =
        false
    ; exactUnitarityResidualWitnessSuppliedIsFalse =
        refl
    ; exactJarlskogNonzeroWitnessSupplied =
        false
    ; exactJarlskogNonzeroWitnessSuppliedIsFalse =
        refl
    ; nextEntryFieldBlocker =
        missingNormalizedLeftEigenbases
    ; nextEntryFieldBlockerIsNormalizedLeftEigenbases =
        refl
    ; gaussianRationalExactCKMClosurePromoted =
        false
    ; gaussianRationalExactCKMClosurePromotedIsFalse =
        refl
    ; gaussianRationalEntryFieldBoundary =
        "Q[i] is recorded as the Gaussian-rational field candidate for CP-phase bookkeeping at epsilon = 1/5"
        ∷ "This only stages the Wolfenstein eta phase; it does not prove an exact splitting field or exact normalized eigenbasis entries"
        ∷ "The exact CKM product, unitarity residual, and Jarlskog nonzero witnesses remain blocked behind the opaque Matter.MixingMatrix API"
        ∷ "No exact physical CKM or carrier-mixing promotion follows from this receipt"
        ∷ []
    }

ckmGaussianRationalEntryFieldRecordsQi :
  gaussianEntryFieldName
    canonicalCKMGaussianRationalEntryFieldAttemptReceipt
  ≡
  "Q[i]"
ckmGaussianRationalEntryFieldRecordsQi =
  refl

ckmGaussianRationalEntryFieldKeepsEigenbasisBlocker :
  nextEntryFieldBlocker
    canonicalCKMGaussianRationalEntryFieldAttemptReceipt
  ≡
  missingNormalizedLeftEigenbases
ckmGaussianRationalEntryFieldKeepsEigenbasisBlocker =
  refl

ckmGaussianRationalEntryFieldDoesNotPromote :
  gaussianRationalExactCKMClosurePromoted
    canonicalCKMGaussianRationalEntryFieldAttemptReceipt
  ≡
  false
ckmGaussianRationalEntryFieldDoesNotPromote =
  refl

------------------------------------------------------------------------
-- Matter.MixingMatrix API audit for Q[i] product-closure attempts.
--
-- The exact inspected API is now the concrete entry record
--
--   record MixingMatrix : Set where constructor mixingMatrix3x3
--
-- from MatterRepresentationReceiptSurface.  Entry projections and a finite
-- V V^dagger residual datum are available, but there is still no generic
-- conjugate-transpose/multiplication/equality API proving exact unitarity.

data CKMMatterMixingMatrixAPIGap : Set where
  missingMatterMixingMatrixEntryProjection :
    CKMMatterMixingMatrixAPIGap

  missingMatterMixingMatrixGaussianRationalEntryCarrier :
    CKMMatterMixingMatrixAPIGap

  missingMatterMixingMatrixConjugateTranspose :
    CKMMatterMixingMatrixAPIGap

  missingMatterMixingMatrixMultiplication :
    CKMMatterMixingMatrixAPIGap

  missingMatterMixingMatrixEqualityLaw :
    CKMMatterMixingMatrixAPIGap

  missingMatterMixingMatrixJarlskogQuartet :
    CKMMatterMixingMatrixAPIGap

canonicalCKMMatterMixingMatrixAPIGaps :
  List CKMMatterMixingMatrixAPIGap
canonicalCKMMatterMixingMatrixAPIGaps =
  missingMatterMixingMatrixConjugateTranspose
  ∷ missingMatterMixingMatrixMultiplication
  ∷ missingMatterMixingMatrixEqualityLaw
  ∷ missingMatterMixingMatrixJarlskogQuartet
  ∷ []

data CKMMatterMixingMatrixAPIAuditStatus : Set where
  matterMixingMatrixConcreteResidualBlocksExactProductClosure :
    CKMMatterMixingMatrixAPIAuditStatus

record CKMMatterMixingMatrixAPIAuditFailClosedReceipt : Setω where
  field
    status :
      CKMMatterMixingMatrixAPIAuditStatus

    inspectedMatterMixingMatrixCarrier :
      Set

    inspectedMatterMixingMatrixCarrierIsMatterMixingMatrix :
      inspectedMatterMixingMatrixCarrier ≡ Matter.MixingMatrix

    exactInspectedDefinition :
      String

    exactInspectedDefinitionIsConcreteRecord :
      exactInspectedDefinition
      ≡
      "record MixingMatrix : Set where constructor mixingMatrix3x3"

    productAttemptReceipt :
      CKMMatterMixingMatrixProductClosureAttemptReceipt

    productAttemptUsesMatterMixingMatrix :
      ckmProductCarrier productAttemptReceipt
      ≡
      Matter.MixingMatrix

    gaussianRationalCurrentWaveReceipt :
      CKMGaussianRationalCurrentWaveReceipt

    gaussianRationalBookkeepingRecorded :
      gaussianRationalCarrierRecorded gaussianRationalCurrentWaveReceipt
      ≡
      true

    jarlskogBookkeepingValue :
      SignedRationalDatum

    jarlskogBookkeepingValueIsOneOver46875 :
      jarlskogBookkeepingValue
      ≡
      oneFortyEightThousandEightHundredSeventyFiveSignedRationalDatum

    exactVVdaggerResidualReceipt :
      CKMMatterMixingMatrixExactVVdaggerResidualReceipt

    exactVVdaggerResidualComputed :
      vvDaggerResidualComputed exactVVdaggerResidualReceipt
      ≡
      true

    exactUnitarityRejectedForConcreteWolfenstein :
      exactUnitarityForConcreteWolfenstein exactVVdaggerResidualReceipt
      ≡
      false

    entryProjectionAPISupplied :
      Bool

    entryProjectionAPISuppliedIsTrue :
      entryProjectionAPISupplied ≡ true

    gaussianRationalEntryCarrierAPISupplied :
      Bool

    gaussianRationalEntryCarrierAPISuppliedIsTrue :
      gaussianRationalEntryCarrierAPISupplied ≡ true

    conjugateTransposeAPISupplied :
      Bool

    conjugateTransposeAPISuppliedIsFalse :
      conjugateTransposeAPISupplied ≡ false

    multiplicationAPISupplied :
      Bool

    multiplicationAPISuppliedIsFalse :
      multiplicationAPISupplied ≡ false

    matrixEqualityLawAPISupplied :
      Bool

    matrixEqualityLawAPISuppliedIsFalse :
      matrixEqualityLawAPISupplied ≡ false

    jarlskogQuartetAPISupplied :
      Bool

    jarlskogQuartetAPISuppliedIsFalse :
      jarlskogQuartetAPISupplied ≡ false

    apiGaps :
      List CKMMatterMixingMatrixAPIGap

    apiGapsAreCanonical :
      apiGaps ≡ canonicalCKMMatterMixingMatrixAPIGaps

    qIEntriesCanInstantiateMatterProductClosure :
      Bool

    qIEntriesCanInstantiateMatterProductClosureIsFalse :
      qIEntriesCanInstantiateMatterProductClosure ≡ false

    exactCKMProductClosurePromoted :
      Bool

    exactCKMProductClosurePromotedIsFalse :
      exactCKMProductClosurePromoted ≡ false

    exactJarlskogTheoremPromoted :
      Bool

    exactJarlskogTheoremPromotedIsFalse :
      exactJarlskogTheoremPromoted ≡ false

    auditFirstBlocker :
      CKMMatterMixingMatrixAPIGap

    auditFirstBlockerIsConjugateTranspose :
      auditFirstBlocker
      ≡
      missingMatterMixingMatrixConjugateTranspose

    auditBoundary :
      List String

open CKMMatterMixingMatrixAPIAuditFailClosedReceipt public

canonicalCKMMatterMixingMatrixAPIAuditFailClosedReceipt :
  CKMMatterMixingMatrixAPIAuditFailClosedReceipt
canonicalCKMMatterMixingMatrixAPIAuditFailClosedReceipt =
  record
    { status =
        matterMixingMatrixConcreteResidualBlocksExactProductClosure
    ; inspectedMatterMixingMatrixCarrier =
        Matter.MixingMatrix
    ; inspectedMatterMixingMatrixCarrierIsMatterMixingMatrix =
        refl
    ; exactInspectedDefinition =
        "record MixingMatrix : Set where constructor mixingMatrix3x3"
    ; exactInspectedDefinitionIsConcreteRecord =
        refl
    ; productAttemptReceipt =
        canonicalCKMMatterMixingMatrixProductClosureAttemptReceipt
    ; productAttemptUsesMatterMixingMatrix =
        refl
    ; gaussianRationalCurrentWaveReceipt =
        canonicalCKMGaussianRationalCurrentWaveReceipt
    ; gaussianRationalBookkeepingRecorded =
        refl
    ; jarlskogBookkeepingValue =
        oneFortyEightThousandEightHundredSeventyFiveSignedRationalDatum
    ; jarlskogBookkeepingValueIsOneOver46875 =
        refl
    ; exactVVdaggerResidualReceipt =
        canonicalCKMMatterMixingMatrixExactVVdaggerResidualReceipt
    ; exactVVdaggerResidualComputed =
        refl
    ; exactUnitarityRejectedForConcreteWolfenstein =
        refl
    ; entryProjectionAPISupplied =
        true
    ; entryProjectionAPISuppliedIsTrue =
        refl
    ; gaussianRationalEntryCarrierAPISupplied =
        true
    ; gaussianRationalEntryCarrierAPISuppliedIsTrue =
        refl
    ; conjugateTransposeAPISupplied =
        false
    ; conjugateTransposeAPISuppliedIsFalse =
        refl
    ; multiplicationAPISupplied =
        false
    ; multiplicationAPISuppliedIsFalse =
        refl
    ; matrixEqualityLawAPISupplied =
        false
    ; matrixEqualityLawAPISuppliedIsFalse =
        refl
    ; jarlskogQuartetAPISupplied =
        false
    ; jarlskogQuartetAPISuppliedIsFalse =
        refl
    ; apiGaps =
        canonicalCKMMatterMixingMatrixAPIGaps
    ; apiGapsAreCanonical =
        refl
    ; qIEntriesCanInstantiateMatterProductClosure =
        false
    ; qIEntriesCanInstantiateMatterProductClosureIsFalse =
        refl
    ; exactCKMProductClosurePromoted =
        false
    ; exactCKMProductClosurePromotedIsFalse =
        refl
    ; exactJarlskogTheoremPromoted =
        false
    ; exactJarlskogTheoremPromotedIsFalse =
        refl
    ; auditFirstBlocker =
        missingMatterMixingMatrixConjugateTranspose
    ; auditFirstBlockerIsConjugateTranspose =
        refl
    ; auditBoundary =
        "MatterRepresentationReceiptSurface now exposes MixingMatrix as a concrete 3x3 Gaussian-rational entry record"
        ∷ "The finite V V^dagger - I residual is recorded for the canonical Wolfenstein datum"
        ∷ "The residual is nonzero, beginning with (1,1) = 37/90000"
        ∷ "No generic conjugate-transpose, multiplication, matrix equality, or Jarlskog quartet API is exposed for theorem promotion"
        ∷ "Q[i] Wolfenstein and 1/46875 Jarlskog data remain exact bookkeeping, not exact unitarity closure"
        ∷ "Exact CKM product closure and exact Jarlskog theorem promotion remain false"
        ∷ []
    }

ckmMatterMixingMatrixAPIAuditRecordsExactDefinition :
  exactInspectedDefinition
    canonicalCKMMatterMixingMatrixAPIAuditFailClosedReceipt
  ≡
  "record MixingMatrix : Set where constructor mixingMatrix3x3"
ckmMatterMixingMatrixAPIAuditRecordsExactDefinition =
  refl

ckmMatterMixingMatrixAPIAuditBlocksQiProductInstantiation :
  qIEntriesCanInstantiateMatterProductClosure
    canonicalCKMMatterMixingMatrixAPIAuditFailClosedReceipt
  ≡
  false
ckmMatterMixingMatrixAPIAuditBlocksQiProductInstantiation =
  refl

ckmMatterMixingMatrixAPIAuditKeepsExactJarlskogUnpromoted :
  exactJarlskogTheoremPromoted
    canonicalCKMMatterMixingMatrixAPIAuditFailClosedReceipt
  ≡
  false
ckmMatterMixingMatrixAPIAuditKeepsExactJarlskogUnpromoted =
  refl

------------------------------------------------------------------------
-- Gate7 approximate unitarity receipt.
--
-- This receipt is deliberately non-promoting.  It records the approximate
-- Wolfenstein unitarity target already present in the Q[i] bookkeeping layer,
-- while consuming the exact finite V V^dagger residual that rejects exact
-- unitarity for this truncated datum.

data CKMApproximateUnitarityComponent : Set where
  approximateWolfensteinProductClosureComponent :
    CKMApproximateUnitarityComponent

  approximateResidualOrderFourComponent :
    CKMApproximateUnitarityComponent

  approximateResidualBoundOneOverSixTwentyFiveComponent :
    CKMApproximateUnitarityComponent

  exactQiVVdaggerResidualComputedComponent :
    CKMApproximateUnitarityComponent

  exactQiUnitarityRejectedComponent :
    CKMApproximateUnitarityComponent

  exactJarlskogStillRequiresProductClosureComponent :
    CKMApproximateUnitarityComponent

canonicalCKMApproximateUnitarityComponents :
  List CKMApproximateUnitarityComponent
canonicalCKMApproximateUnitarityComponents =
  approximateWolfensteinProductClosureComponent
  ∷ approximateResidualOrderFourComponent
  ∷ approximateResidualBoundOneOverSixTwentyFiveComponent
  ∷ exactQiVVdaggerResidualComputedComponent
  ∷ exactQiUnitarityRejectedComponent
  ∷ exactJarlskogStillRequiresProductClosureComponent
  ∷ []

record CKMApproximateUnitarityReceipt : Set where
  field
    approximateProductReceipt :
      CKMConcreteWolfensteinProductClosureReceipt

    approximateProductRecorded :
      truncatedProductClosureRecorded approximateProductReceipt
      ≡
      true

    approximateResidualOrderIsFour :
      residualOrderExponent approximateProductReceipt
      ≡
      4

    approximateResidualBoundDenominatorIs625 :
      residualBoundDenominator approximateProductReceipt
      ≡
      625

    approximateTargetRecorded :
      Bool

    approximateTargetRecordedIsTrue :
      approximateTargetRecorded ≡ true

    exactResidualReceipt :
      CKMMatterMixingMatrixExactVVdaggerResidualReceipt

    exactQiVVdaggerResidualComputed :
      vvDaggerResidualComputed exactResidualReceipt
      ≡
      true

    exactQiUnitarityRejected :
      exactUnitarityForConcreteWolfenstein exactResidualReceipt
      ≡
      false

    exactQiProductClosurePromoted :
      exactCKMProductClosurePromoted exactResidualReceipt
      ≡
      false

    exactJarlskogTheoremPromotedFromApproximateReceipt :
      Bool

    exactJarlskogTheoremPromotedFromApproximateReceiptIsFalse :
      exactJarlskogTheoremPromotedFromApproximateReceipt ≡ false

    approximateUnitarityComponents :
      List CKMApproximateUnitarityComponent

    approximateUnitarityComponentsAreCanonical :
      approximateUnitarityComponents
      ≡
      canonicalCKMApproximateUnitarityComponents

    approximateUnitarityBoundary :
      List String

open CKMApproximateUnitarityReceipt public

canonicalCKMApproximateUnitarityReceipt :
  CKMApproximateUnitarityReceipt
canonicalCKMApproximateUnitarityReceipt =
  record
    { approximateProductReceipt =
        canonicalCKMConcreteWolfensteinProductClosureReceipt
    ; approximateProductRecorded =
        refl
    ; approximateResidualOrderIsFour =
        refl
    ; approximateResidualBoundDenominatorIs625 =
        refl
    ; approximateTargetRecorded =
        true
    ; approximateTargetRecordedIsTrue =
        refl
    ; exactResidualReceipt =
        canonicalCKMMatterMixingMatrixExactVVdaggerResidualReceipt
    ; exactQiVVdaggerResidualComputed =
        refl
    ; exactQiUnitarityRejected =
        refl
    ; exactQiProductClosurePromoted =
        refl
    ; exactJarlskogTheoremPromotedFromApproximateReceipt =
        false
    ; exactJarlskogTheoremPromotedFromApproximateReceiptIsFalse =
        refl
    ; approximateUnitarityComponents =
        canonicalCKMApproximateUnitarityComponents
    ; approximateUnitarityComponentsAreCanonical =
        refl
    ; approximateUnitarityBoundary =
        "Gate7 records the Wolfenstein approximate unitarity target over Q[i] with residual order epsilon^4"
        ∷ "At epsilon=1/5 the staged residual bound denominator is 625"
        ∷ "The exact finite Q[i] V V^dagger - I residual is also recorded and is nonzero"
        ∷ "Therefore this receipt rejects exact Q[i] unitarity/product closure for the truncated datum"
        ∷ "Exact Jarlskog remains dependent on exact CKM product closure and a Jarlskog quartet theorem, not this approximate target"
        ∷ []
    }

ckmApproximateUnitarityTargetIsRecorded :
  approximateTargetRecorded canonicalCKMApproximateUnitarityReceipt
  ≡
  true
ckmApproximateUnitarityTargetIsRecorded =
  refl

ckmApproximateUnitarityRejectsExactQiUnitarity :
  exactQiUnitarityRejected canonicalCKMApproximateUnitarityReceipt
  ≡
  refl
ckmApproximateUnitarityRejectsExactQiUnitarity =
  refl

ckmApproximateUnitarityDoesNotPromoteExactJarlskog :
  exactJarlskogTheoremPromotedFromApproximateReceipt
    canonicalCKMApproximateUnitarityReceipt
  ≡
  false
ckmApproximateUnitarityDoesNotPromoteExactJarlskog =
  refl

------------------------------------------------------------------------
-- Approximate-unitarity Jarlskog bookkeeping handoff.
--
-- The explicit local Jarlskog datum is useful bookkeeping only when it is
-- paired with the approximate-unitarity receipt that rejects exact Q[i]
-- unitarity for the same truncated Wolfenstein datum.  This handoff keeps the
-- exact Jarlskog theorem false until exact product-closure terms exist.

data CKMApproximateUnitarityJarlskogBookkeepingComponent : Set where
  approxJarlskogConsumesApproximateUnitarityComponent :
    CKMApproximateUnitarityJarlskogBookkeepingComponent

  approxJarlskogConsumesExplicitLocalJarlskogComponent :
    CKMApproximateUnitarityJarlskogBookkeepingComponent

  approxJarlskogRejectsExactQiUnitarityComponent :
    CKMApproximateUnitarityJarlskogBookkeepingComponent

  approxJarlskogRetainsExactProductClosureComponent :
    CKMApproximateUnitarityJarlskogBookkeepingComponent

  approxJarlskogKeepsExactTheoremFalseComponent :
    CKMApproximateUnitarityJarlskogBookkeepingComponent

canonicalCKMApproximateUnitarityJarlskogBookkeepingComponents :
  List CKMApproximateUnitarityJarlskogBookkeepingComponent
canonicalCKMApproximateUnitarityJarlskogBookkeepingComponents =
  approxJarlskogConsumesApproximateUnitarityComponent
  ∷ approxJarlskogConsumesExplicitLocalJarlskogComponent
  ∷ approxJarlskogRejectsExactQiUnitarityComponent
  ∷ approxJarlskogRetainsExactProductClosureComponent
  ∷ approxJarlskogKeepsExactTheoremFalseComponent
  ∷ []

record CKMApproximateUnitarityJarlskogBookkeepingReceipt : Set where
  field
    approxUnitarityReceiptForJarlskog :
      CKMApproximateUnitarityReceipt

    explicitEntryJarlskogReceipt :
      CKMExplicitEntryApproxUnitarityJarlskogReceipt

    approxJarlskogTargetRecorded :
      approximateTargetRecorded approxUnitarityReceiptForJarlskog
      ≡
      true

    approxJarlskogExactQiUnitarityRejected :
      exactUnitarityForConcreteWolfenstein
        (exactResidualReceipt approxUnitarityReceiptForJarlskog)
      ≡
      false

    approxJarlskogExactProductClosureStillFalse :
      exactCKMProductClosureWitnessSupplied explicitEntryJarlskogReceipt
      ≡
      false

    approxJarlskogLocalNonzeroDatumRecorded :
      exactLocalJarlskogNonzeroDatumSupplied explicitEntryJarlskogReceipt
      ≡
      true

    approxJarlskogConjugatedQuartetNonzeroDatumRecorded :
      exactConjugatedQuartetJarlskogNonzeroDatumSupplied
        explicitEntryJarlskogReceipt
      ≡
      true

    approxJarlskogExactTheoremPromoted :
      Bool

    approxJarlskogExactTheoremPromotedIsFalse :
      approxJarlskogExactTheoremPromoted ≡ false

    approxJarlskogRemainingBlocker :
      CKMArithmeticInputSlot

    approxJarlskogRemainingBlockerIsProductClosure :
      approxJarlskogRemainingBlocker
      ≡
      missingCKMProductClosureWitness

    approxJarlskogComponents :
      List CKMApproximateUnitarityJarlskogBookkeepingComponent

    approxJarlskogComponentsAreCanonical :
      approxJarlskogComponents
      ≡
      canonicalCKMApproximateUnitarityJarlskogBookkeepingComponents

    approxJarlskogBoundary :
      List String

open CKMApproximateUnitarityJarlskogBookkeepingReceipt public

canonicalCKMApproximateUnitarityJarlskogBookkeepingReceipt :
  CKMApproximateUnitarityJarlskogBookkeepingReceipt
canonicalCKMApproximateUnitarityJarlskogBookkeepingReceipt =
  record
    { approxUnitarityReceiptForJarlskog =
        canonicalCKMApproximateUnitarityReceipt
    ; explicitEntryJarlskogReceipt =
        canonicalCKMExplicitEntryApproxUnitarityJarlskogReceipt
    ; approxJarlskogTargetRecorded =
        refl
    ; approxJarlskogExactQiUnitarityRejected =
        refl
    ; approxJarlskogExactProductClosureStillFalse =
        refl
    ; approxJarlskogLocalNonzeroDatumRecorded =
        refl
    ; approxJarlskogConjugatedQuartetNonzeroDatumRecorded =
        refl
    ; approxJarlskogExactTheoremPromoted =
        false
    ; approxJarlskogExactTheoremPromotedIsFalse =
        refl
    ; approxJarlskogRemainingBlocker =
        missingCKMProductClosureWitness
    ; approxJarlskogRemainingBlockerIsProductClosure =
        refl
    ; approxJarlskogComponents =
        canonicalCKMApproximateUnitarityJarlskogBookkeepingComponents
    ; approxJarlskogComponentsAreCanonical =
        refl
    ; approxJarlskogBoundary =
        "Approximate unitarity is threaded into Jarlskog bookkeeping as a residual-bound receipt, not exact product closure"
        ∷ "The exact Q[i] residual rejects unitarity for the truncated Wolfenstein datum"
        ∷ "Local Jarlskog and conjugated-quartet nonzero data are recorded, but they are not the global exact Jarlskog theorem"
        ∷ "The exact theorem remains blocked at missingCKMProductClosureWitness until real product-closure terms exist"
        ∷ []
    }

ckmApproximateUnitarityJarlskogBookkeepingKeepsTheoremFalse :
  approxJarlskogExactTheoremPromoted
    canonicalCKMApproximateUnitarityJarlskogBookkeepingReceipt
  ≡
  false
ckmApproximateUnitarityJarlskogBookkeepingKeepsTheoremFalse =
  refl

------------------------------------------------------------------------
-- Upstream exact witness chain consumer.
--
-- This surface consumes the exact identity-case CKM chain upstream of the
-- physical off-diagonal frontier.  It records the product-closure and
-- residual witnesses as supplied, while keeping the physical frontier open.

record CKMExactWitnessChainEntryReceipt : Setω where
  field
    exactWitnessChain :
      Exact.CKMExactWitnessChain

    wolfensteinProductClosureReceipt :
      CKMConcreteWolfensteinProductClosureReceipt

    wolfensteinProductClosureReceiptIsCanonical :
      wolfensteinProductClosureReceipt
      ≡
      canonicalCKMConcreteWolfensteinProductClosureReceipt

    exactProductClosureWitness :
      Exact.CKMProductClosureWitness

    exactProductClosureWitnessIsChainProjection :
      exactProductClosureWitness
      ≡
      Exact.productClosure exactWitnessChain

    exactUnitarityResidualWitness :
      Exact.UnitarityResidualWitness

    exactUnitarityResidualWitnessIsChainProjection :
      exactUnitarityResidualWitness
      ≡
      Exact.unitarityResidual exactWitnessChain

    exactWitnessChainConsumed :
      Bool

    exactWitnessChainConsumedIsTrue :
      exactWitnessChainConsumed ≡ true

    physicalOffDiagonalFrontierStillOpen :
      Bool

    physicalOffDiagonalFrontierStillOpenIsFalse :
      physicalOffDiagonalFrontierStillOpen ≡ false

    exactWitnessChainBoundary :
      List String

open CKMExactWitnessChainEntryReceipt public

canonicalExactCKMProductClosureWitness :
  Exact.CKMProductClosureWitness
canonicalExactCKMProductClosureWitness =
  Exact.canonicalCKMProductClosureWitness

canonicalExactUnitarityResidualWitness :
  Exact.UnitarityResidualWitness
canonicalExactUnitarityResidualWitness =
  Exact.canonicalUnitarityResidualWitness

canonicalCKMExactWitnessChainEntryReceipt :
  CKMExactWitnessChainEntryReceipt
canonicalCKMExactWitnessChainEntryReceipt = record
  { exactWitnessChain = Exact.canonicalCKMExactWitnessChain
  ; wolfensteinProductClosureReceipt =
      canonicalCKMConcreteWolfensteinProductClosureReceipt
  ; wolfensteinProductClosureReceiptIsCanonical =
      refl
  ; exactProductClosureWitness =
      canonicalExactCKMProductClosureWitness
  ; exactProductClosureWitnessIsChainProjection =
      refl
  ; exactUnitarityResidualWitness =
      canonicalExactUnitarityResidualWitness
  ; exactUnitarityResidualWitnessIsChainProjection =
      refl
  ; exactWitnessChainConsumed =
      true
  ; exactWitnessChainConsumedIsTrue =
      refl
  ; physicalOffDiagonalFrontierStillOpen =
      false
  ; physicalOffDiagonalFrontierStillOpenIsFalse =
      refl
  ; exactWitnessChainBoundary =
      "The exact identity-case CKM witness chain is threaded upstream"
      ∷ "The canonical truncated Wolfenstein product-closure receipt is retained as the explicit FN/Wolfenstein front"
      ∷ "Product closure and unitarity residual are consumed from the canonical exact chain"
      ∷ "The physical off-diagonal CKM frontier remains open"
      ∷ []
  }

exactCKMIdentityWitnessChain :
  Exact.CKMExactWitnessChain
exactCKMIdentityWitnessChain =
  exactWitnessChain canonicalCKMExactWitnessChainEntryReceipt

exactCKMIdentityProductClosureWitness :
  Exact.CKMProductClosureWitness
exactCKMIdentityProductClosureWitness =
  canonicalExactCKMProductClosureWitness

exactCKMIdentityUnitarityResidualWitness :
  Exact.UnitarityResidualWitness
exactCKMIdentityUnitarityResidualWitness =
  canonicalExactUnitarityResidualWitness
