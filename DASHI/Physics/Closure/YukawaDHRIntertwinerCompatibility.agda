module DASHI.Physics.Closure.YukawaDHRIntertwinerCompatibility where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CKMCarrierDerived as CKMD
import DASHI.Physics.Closure.CKMExactWitnesses as Exact
import DASHI.Physics.Closure.CKMUnitarityFromCarrier as CKMU
import DASHI.Physics.Closure.HiggsSymmetryBreakingReceipt as Higgs
import DASHI.Physics.Closure.MatterRepresentationReceiptSurface as Matter
import DASHI.Physics.QFT.DHRSectorDecomposition as DHR

------------------------------------------------------------------------
-- Yukawa/DHR intertwiner compatibility on the actual carrier data.
--
-- The repository already has the exact carrier witness chain in
-- `CKMExactWitnesses.agda`.  This file packages that chain with the concrete
-- DHR sector objects already present in the repo:
--   * U(1)   -> canonicalU1SectorObject
--   * SU(2)  -> canonicalSU2SectorObject
--   * depth-9 color route -> canonicalSU3FrontierObject
--
-- The factorwise compatibility records are fail-closed and concrete: the
-- carrier action is the identity on the canonical Yukawa matrices, so the
-- compatibilities are witnessed by definitional equality.  The full SM-sector
-- receipt then combines the three factorwise records with the exact upstream
-- Yukawa/DHR witness chain.

carrierActionIdentity :
  Matter.MixingMatrix →
  Matter.MixingMatrix
carrierActionIdentity m = m

data YukawaDHRActionSector : Set where
  identityCarrierSector :
    YukawaDHRActionSector

  u1NonIdentitySector :
    YukawaDHRActionSector

  su2NonIdentitySector :
    YukawaDHRActionSector

  su3Depth9NonIdentityFrontierSector :
    YukawaDHRActionSector

canonicalYukawaDHRActionSectors :
  List YukawaDHRActionSector
canonicalYukawaDHRActionSectors =
  identityCarrierSector
  ∷ u1NonIdentitySector
  ∷ su2NonIdentitySector
  ∷ su3Depth9NonIdentityFrontierSector
  ∷ []

canonicalNonIdentityYukawaDHRActionSectors :
  List YukawaDHRActionSector
canonicalNonIdentityYukawaDHRActionSectors =
  u1NonIdentitySector
  ∷ su2NonIdentitySector
  ∷ su3Depth9NonIdentityFrontierSector
  ∷ []

data YukawaDHRSymbolicCarrierAction : Set where
  identitySymbolicCarrierAction :
    YukawaDHRSymbolicCarrierAction

  u1CanonicalSymbolicSectorAction :
    YukawaDHRSymbolicCarrierAction

  su2CanonicalSymbolicSectorAction :
    YukawaDHRSymbolicCarrierAction

  su3Depth9CanonicalSymbolicFrontierAction :
    YukawaDHRSymbolicCarrierAction

symbolicActionSector :
  YukawaDHRSymbolicCarrierAction →
  YukawaDHRActionSector
symbolicActionSector identitySymbolicCarrierAction =
  identityCarrierSector
symbolicActionSector u1CanonicalSymbolicSectorAction =
  u1NonIdentitySector
symbolicActionSector su2CanonicalSymbolicSectorAction =
  su2NonIdentitySector
symbolicActionSector su3Depth9CanonicalSymbolicFrontierAction =
  su3Depth9NonIdentityFrontierSector

symbolicCarrierAction :
  YukawaDHRSymbolicCarrierAction →
  Matter.MixingMatrix →
  Matter.MixingMatrix
symbolicCarrierAction identitySymbolicCarrierAction m =
  m
symbolicCarrierAction u1CanonicalSymbolicSectorAction m =
  m
symbolicCarrierAction su2CanonicalSymbolicSectorAction m =
  m
symbolicCarrierAction su3Depth9CanonicalSymbolicFrontierAction m =
  m

upYukawaMatrix : Matter.MixingMatrix
upYukawaMatrix =
  Exact.DiagonalYukawa3x3.matrix Exact.canonicalUpYukawa3x3

downYukawaMatrix : Matter.MixingMatrix
downYukawaMatrix =
  Exact.DiagonalYukawa3x3.matrix Exact.canonicalDownYukawa3x3

data YukawaDHRCompatibilityBlocker : Set where
  missingPhysicalFermionMassReceipt :
    YukawaDHRCompatibilityBlocker

  missingGenericYukawaSplittingFieldEigenbasis :
    YukawaDHRCompatibilityBlocker

  missingAbsoluteHiggsScaleW4Calibration :
    YukawaDHRCompatibilityBlocker

  missingActualDHRSectorRepresentations :
    YukawaDHRCompatibilityBlocker

  missingPhysicalYukawaMatrices :
    YukawaDHRCompatibilityBlocker

  missingDHRIntertwinerActionBeyondIdentity :
    YukawaDHRCompatibilityBlocker

canonicalYukawaDHRCompatibilityBlockers :
  List YukawaDHRCompatibilityBlocker
canonicalYukawaDHRCompatibilityBlockers =
  missingPhysicalFermionMassReceipt
  ∷ missingGenericYukawaSplittingFieldEigenbasis
  ∷ missingAbsoluteHiggsScaleW4Calibration
  ∷ missingActualDHRSectorRepresentations
  ∷ missingPhysicalYukawaMatrices
  ∷ missingDHRIntertwinerActionBeyondIdentity
  ∷ []

data YukawaGenerationIndex : Set where
  firstGeneration :
    YukawaGenerationIndex

  secondGeneration :
    YukawaGenerationIndex

  thirdGeneration :
    YukawaGenerationIndex

canonicalYukawaGenerationIndices :
  List YukawaGenerationIndex
canonicalYukawaGenerationIndices =
  firstGeneration
  ∷ secondGeneration
  ∷ thirdGeneration
  ∷ []

matrixEntry :
  Matter.MixingMatrix →
  YukawaGenerationIndex →
  YukawaGenerationIndex →
  Matter.MixingGaussianRationalDatum
matrixEntry m firstGeneration firstGeneration =
  Matter.v11 m
matrixEntry m firstGeneration secondGeneration =
  Matter.v12 m
matrixEntry m firstGeneration thirdGeneration =
  Matter.v13 m
matrixEntry m secondGeneration firstGeneration =
  Matter.v21 m
matrixEntry m secondGeneration secondGeneration =
  Matter.v22 m
matrixEntry m secondGeneration thirdGeneration =
  Matter.v23 m
matrixEntry m thirdGeneration firstGeneration =
  Matter.v31 m
matrixEntry m thirdGeneration secondGeneration =
  Matter.v32 m
matrixEntry m thirdGeneration thirdGeneration =
  Matter.v33 m

carrierUpYukawaFormulaEntry :
  YukawaGenerationIndex →
  YukawaGenerationIndex →
  Matter.MixingGaussianRationalDatum
carrierUpYukawaFormulaEntry =
  matrixEntry upYukawaMatrix

carrierDownYukawaFormulaEntry :
  YukawaGenerationIndex →
  YukawaGenerationIndex →
  Matter.MixingGaussianRationalDatum
carrierDownYukawaFormulaEntry =
  matrixEntry downYukawaMatrix

data YukawaFormulaLane : Set where
  upTypeYukawaFormulaLane :
    YukawaFormulaLane

  downTypeYukawaFormulaLane :
    YukawaFormulaLane

carrierYukawaFormulaEntry :
  YukawaFormulaLane →
  YukawaGenerationIndex →
  YukawaGenerationIndex →
  Matter.MixingGaussianRationalDatum
carrierYukawaFormulaEntry upTypeYukawaFormulaLane =
  carrierUpYukawaFormulaEntry
carrierYukawaFormulaEntry downTypeYukawaFormulaLane =
  carrierDownYukawaFormulaEntry

data YukawaDHRFormulaBlocker : Set where
  missingPhysicalLeftDHRLocalizedEndomorphismFamily :
    YukawaDHRFormulaBlocker

  missingPhysicalRightDHRLocalizedEndomorphismFamily :
    YukawaDHRFormulaBlocker

  missingHiggsFieldOperatorOnDHRCarrier :
    YukawaDHRFormulaBlocker

  missingDHRBraKetPairingOnMatterCarrier :
    YukawaDHRFormulaBlocker

  missingNonIdentityDHRIntertwinerMultiplication :
    YukawaDHRFormulaBlocker

canonicalYukawaDHRFormulaBlockers :
  List YukawaDHRFormulaBlocker
canonicalYukawaDHRFormulaBlockers =
  missingPhysicalLeftDHRLocalizedEndomorphismFamily
  ∷ missingPhysicalRightDHRLocalizedEndomorphismFamily
  ∷ missingHiggsFieldOperatorOnDHRCarrier
  ∷ missingDHRBraKetPairingOnMatterCarrier
  ∷ missingNonIdentityDHRIntertwinerMultiplication
  ∷ []

record CarrierDHRYukawaFormulaSurface : Setω where
  field
    formulaLabel :
      String

    formulaLabelIsBraKetSurface :
      formulaLabel ≡ "Y_ij = <rho_i, Phi_H * rho_j>"

    generationIndices :
      List YukawaGenerationIndex

    generationIndicesAreCanonical :
      generationIndices ≡ canonicalYukawaGenerationIndices

    higgsReceipt :
      Higgs.HiggsSymmetryBreakingReceipt

    higgsPrimitive :
      Matter.HiggsDoubletPrimitive

    higgsPrimitiveIsCanonical :
      higgsPrimitive ≡ Matter.canonicalHiggsDoubletPrimitive

    leftQuarkPrimitive :
      Matter.LeftQuarkDoubletFamilyPrimitive

    leftQuarkPrimitiveIsCanonical :
      leftQuarkPrimitive
      ≡
      Matter.canonicalLeftQuarkDoubletFamilyPrimitive

    rightUpQuarkPrimitive :
      Matter.RightUpQuarkFamilyPrimitive

    rightUpQuarkPrimitiveIsCanonical :
      rightUpQuarkPrimitive
      ≡
      Matter.canonicalRightUpQuarkFamilyPrimitive

    rightDownQuarkPrimitive :
      Matter.RightDownQuarkFamilyPrimitive

    rightDownQuarkPrimitiveIsCanonical :
      rightDownQuarkPrimitive
      ≡
      Matter.canonicalRightDownQuarkFamilyPrimitive

    ckmCarrierDerivedReceipt :
      CKMD.CKMCarrierDerivedReceipt

    ckmUnitaryReceipt :
      CKMU.CKMUnitaryReceipt

    carrierCKMMatrix :
      Matter.MixingMatrix

    carrierCKMMatrixAgreesWithDerived :
      carrierCKMMatrix
      ≡
      CKMD.ckmCarrierMatrix ckmCarrierDerivedReceipt

    carrierCKMMatrixAgreesWithUnitary :
      carrierCKMMatrix
      ≡
      CKMU.carrierCKMMatrix ckmUnitaryReceipt

    carrierCKMMatrixIsIdentity :
      carrierCKMMatrix ≡ Matter.identityMixingMatrix

    upYukawaCarrierMatrix :
      Matter.MixingMatrix

    upYukawaCarrierMatrixIsCanonical :
      upYukawaCarrierMatrix ≡ upYukawaMatrix

    upYukawaCarrierMatrixAgreesWithDerived :
      upYukawaCarrierMatrix
      ≡
      CKMD.yukawaUpMatrix ckmCarrierDerivedReceipt

    downYukawaCarrierMatrix :
      Matter.MixingMatrix

    downYukawaCarrierMatrixIsCanonical :
      downYukawaCarrierMatrix ≡ downYukawaMatrix

    downYukawaCarrierMatrixAgreesWithDerived :
      downYukawaCarrierMatrix
      ≡
      CKMD.yukawaDownMatrix ckmCarrierDerivedReceipt

    upFormulaEntry :
      YukawaGenerationIndex →
      YukawaGenerationIndex →
      Matter.MixingGaussianRationalDatum

    upFormulaEntryIsCarrierMatrixEntry :
      (i j : YukawaGenerationIndex) →
      upFormulaEntry i j
      ≡
      matrixEntry upYukawaCarrierMatrix i j

    downFormulaEntry :
      YukawaGenerationIndex →
      YukawaGenerationIndex →
      Matter.MixingGaussianRationalDatum

    downFormulaEntryIsCarrierMatrixEntry :
      (i j : YukawaGenerationIndex) →
      downFormulaEntry i j
      ≡
      matrixEntry downYukawaCarrierMatrix i j

    exactIdentityDHRWitness :
      Exact.YukawaDHRIntertwinerCompatibilityWitness

    exactIdentityDHRWitnessIsCanonical :
      exactIdentityDHRWitness
      ≡
      Exact.canonicalYukawaDHRIntertwinerCompatibilityWitness

    exactIdentityDHRWitnessUpCompatible :
      Exact.dhrAction exactIdentityDHRWitness upYukawaCarrierMatrix
      ≡
      upYukawaCarrierMatrix

    exactIdentityDHRWitnessDownCompatible :
      Exact.dhrAction exactIdentityDHRWitness downYukawaCarrierMatrix
      ≡
      downYukawaCarrierMatrix

    formulaBlockers :
      List YukawaDHRFormulaBlocker

    formulaBlockersAreCanonical :
      formulaBlockers ≡ canonicalYukawaDHRFormulaBlockers

    physicalLeftDHRLocalizedEndomorphismFamilyConstructed :
      Bool

    physicalLeftDHRLocalizedEndomorphismFamilyConstructedIsFalse :
      physicalLeftDHRLocalizedEndomorphismFamilyConstructed ≡ false

    physicalRightDHRLocalizedEndomorphismFamilyConstructed :
      Bool

    physicalRightDHRLocalizedEndomorphismFamilyConstructedIsFalse :
      physicalRightDHRLocalizedEndomorphismFamilyConstructed ≡ false

    higgsFieldOperatorOnDHRCarrierConstructed :
      Bool

    higgsFieldOperatorOnDHRCarrierConstructedIsFalse :
      higgsFieldOperatorOnDHRCarrierConstructed ≡ false

    dhrBraKetPairingOnMatterCarrierConstructed :
      Bool

    dhrBraKetPairingOnMatterCarrierConstructedIsFalse :
      dhrBraKetPairingOnMatterCarrierConstructed ≡ false

    physicalDHRYukawaFormulaPromoted :
      Bool

    physicalDHRYukawaFormulaPromotedIsFalse :
      physicalDHRYukawaFormulaPromoted ≡ false

    formulaBoundary :
      List String

open CarrierDHRYukawaFormulaSurface public

canonicalCarrierDHRYukawaFormulaSurface :
  CarrierDHRYukawaFormulaSurface
canonicalCarrierDHRYukawaFormulaSurface = record
  { formulaLabel =
      "Y_ij = <rho_i, Phi_H * rho_j>"
  ; formulaLabelIsBraKetSurface =
      refl
  ; generationIndices =
      canonicalYukawaGenerationIndices
  ; generationIndicesAreCanonical =
      refl
  ; higgsReceipt =
      Higgs.canonicalHiggsSymmetryBreakingReceipt
  ; higgsPrimitive =
      Matter.canonicalHiggsDoubletPrimitive
  ; higgsPrimitiveIsCanonical =
      refl
  ; leftQuarkPrimitive =
      Matter.canonicalLeftQuarkDoubletFamilyPrimitive
  ; leftQuarkPrimitiveIsCanonical =
      refl
  ; rightUpQuarkPrimitive =
      Matter.canonicalRightUpQuarkFamilyPrimitive
  ; rightUpQuarkPrimitiveIsCanonical =
      refl
  ; rightDownQuarkPrimitive =
      Matter.canonicalRightDownQuarkFamilyPrimitive
  ; rightDownQuarkPrimitiveIsCanonical =
      refl
  ; ckmCarrierDerivedReceipt =
      CKMD.canonicalCKMCarrierDerived
  ; ckmUnitaryReceipt =
      CKMU.canonicalCKMUnitary
  ; carrierCKMMatrix =
      CKMD.ckmCarrierMatrix CKMD.canonicalCKMCarrierDerived
  ; carrierCKMMatrixAgreesWithDerived =
      refl
  ; carrierCKMMatrixAgreesWithUnitary =
      refl
  ; carrierCKMMatrixIsIdentity =
      refl
  ; upYukawaCarrierMatrix =
      upYukawaMatrix
  ; upYukawaCarrierMatrixIsCanonical =
      refl
  ; upYukawaCarrierMatrixAgreesWithDerived =
      refl
  ; downYukawaCarrierMatrix =
      downYukawaMatrix
  ; downYukawaCarrierMatrixIsCanonical =
      refl
  ; downYukawaCarrierMatrixAgreesWithDerived =
      refl
  ; upFormulaEntry =
      carrierUpYukawaFormulaEntry
  ; upFormulaEntryIsCarrierMatrixEntry =
      λ _ _ → refl
  ; downFormulaEntry =
      carrierDownYukawaFormulaEntry
  ; downFormulaEntryIsCarrierMatrixEntry =
      λ _ _ → refl
  ; exactIdentityDHRWitness =
      Exact.canonicalYukawaDHRIntertwinerCompatibilityWitness
  ; exactIdentityDHRWitnessIsCanonical =
      refl
  ; exactIdentityDHRWitnessUpCompatible =
      refl
  ; exactIdentityDHRWitnessDownCompatible =
      refl
  ; formulaBlockers =
      canonicalYukawaDHRFormulaBlockers
  ; formulaBlockersAreCanonical =
      refl
  ; physicalLeftDHRLocalizedEndomorphismFamilyConstructed =
      false
  ; physicalLeftDHRLocalizedEndomorphismFamilyConstructedIsFalse =
      refl
  ; physicalRightDHRLocalizedEndomorphismFamilyConstructed =
      false
  ; physicalRightDHRLocalizedEndomorphismFamilyConstructedIsFalse =
      refl
  ; higgsFieldOperatorOnDHRCarrierConstructed =
      false
  ; higgsFieldOperatorOnDHRCarrierConstructedIsFalse =
      refl
  ; dhrBraKetPairingOnMatterCarrierConstructed =
      false
  ; dhrBraKetPairingOnMatterCarrierConstructedIsFalse =
      refl
  ; physicalDHRYukawaFormulaPromoted =
      false
  ; physicalDHRYukawaFormulaPromotedIsFalse =
      refl
  ; formulaBoundary =
      "The displayed surface Y_ij = <rho_i, Phi_H * rho_j> is implemented only at the concrete carrier-matrix entry level"
      ∷ "For each generation pair i,j the up/down formula entries are exactly the corresponding entries of the canonical diagonal Yukawa matrices"
      ∷ "The Higgs input is the canonical Higgs doublet primitive and the existing Higgs symmetry-breaking receipt"
      ∷ "The CKM carrier-derived and CKM-unitarity receipts are threaded and agree on the identity carrier matrix"
      ∷ "The only DHR action consumed here is the existing exact identity action on the canonical up/down carrier matrices"
      ∷ "No physical localised rho_i/rho_j endomorphism family, Higgs field operator on a DHR carrier, bra-ket pairing, or non-identity DHR multiplication is constructed"
      ∷ []
  }

record U1PhaseChargeSelectionSymbolicIntertwinerReceipt : Set₁ where
  field
    u1SectorObject :
      DHR.U1SectorObject

    u1SectorObjectIsCanonical :
      u1SectorObject ≡ DHR.canonicalU1SectorObject

    leftQuarkDoubletPrimitive :
      Matter.LeftQuarkDoubletFamilyPrimitive

    leftQuarkDoubletPrimitiveIsCanonical :
      leftQuarkDoubletPrimitive
      ≡
      Matter.canonicalLeftQuarkDoubletFamilyPrimitive

    rightUpQuarkPrimitive :
      Matter.RightUpQuarkFamilyPrimitive

    rightUpQuarkPrimitiveIsCanonical :
      rightUpQuarkPrimitive
      ≡
      Matter.canonicalRightUpQuarkFamilyPrimitive

    rightDownQuarkPrimitive :
      Matter.RightDownQuarkFamilyPrimitive

    rightDownQuarkPrimitiveIsCanonical :
      rightDownQuarkPrimitive
      ≡
      Matter.canonicalRightDownQuarkFamilyPrimitive

    higgsDoubletPrimitive :
      Matter.HiggsDoubletPrimitive

    higgsDoubletPrimitiveIsCanonical :
      higgsDoubletPrimitive
      ≡
      Matter.canonicalHiggsDoubletPrimitive

    leftQuarkChargeIsOneSixth :
      Matter.leftQuarkPrimitiveHypercharge leftQuarkDoubletPrimitive
      ≡
      Matter.canonicalHyperchargeOneSixthPrimitive

    rightUpChargeIsTwoThirds :
      Matter.rightUpQuarkPrimitiveHypercharge rightUpQuarkPrimitive
      ≡
      Matter.canonicalHyperchargeTwoThirdsPrimitive

    rightDownChargeIsMinusOneThird :
      Matter.rightDownQuarkPrimitiveHypercharge rightDownQuarkPrimitive
      ≡
      Matter.canonicalHyperchargeMinusOneThirdPrimitive

    higgsChargeIsPlusOne :
      Matter.higgsPrimitiveHypercharge higgsDoubletPrimitive
      ≡
      Matter.canonicalHyperchargePlusOnePrimitive

    selectedSymbolicAction :
      YukawaDHRSymbolicCarrierAction

    selectedSymbolicActionIsU1 :
      selectedSymbolicAction ≡ u1CanonicalSymbolicSectorAction

    selectedSymbolicActionSectorIsU1NonIdentity :
      symbolicActionSector selectedSymbolicAction ≡ u1NonIdentitySector

    upMatrixSymbolicallyIntertwined :
      symbolicCarrierAction selectedSymbolicAction upYukawaMatrix
      ≡
      upYukawaMatrix

    downMatrixSymbolicallyIntertwined :
      symbolicCarrierAction selectedSymbolicAction downYukawaMatrix
      ≡
      downYukawaMatrix

    phaseChargeSelectionConstructed :
      Bool

    phaseChargeSelectionConstructedIsTrue :
      phaseChargeSelectionConstructed ≡ true

    physicalU1SectorRepresentationConstructed :
      Bool

    physicalU1SectorRepresentationConstructedIsFalse :
      physicalU1SectorRepresentationConstructed ≡ false

    receiptBoundary :
      List String

open U1PhaseChargeSelectionSymbolicIntertwinerReceipt public

canonicalU1PhaseChargeSelectionSymbolicIntertwinerReceipt :
  U1PhaseChargeSelectionSymbolicIntertwinerReceipt
canonicalU1PhaseChargeSelectionSymbolicIntertwinerReceipt = record
  { u1SectorObject =
      DHR.canonicalU1SectorObject
  ; u1SectorObjectIsCanonical =
      refl
  ; leftQuarkDoubletPrimitive =
      Matter.canonicalLeftQuarkDoubletFamilyPrimitive
  ; leftQuarkDoubletPrimitiveIsCanonical =
      refl
  ; rightUpQuarkPrimitive =
      Matter.canonicalRightUpQuarkFamilyPrimitive
  ; rightUpQuarkPrimitiveIsCanonical =
      refl
  ; rightDownQuarkPrimitive =
      Matter.canonicalRightDownQuarkFamilyPrimitive
  ; rightDownQuarkPrimitiveIsCanonical =
      refl
  ; higgsDoubletPrimitive =
      Matter.canonicalHiggsDoubletPrimitive
  ; higgsDoubletPrimitiveIsCanonical =
      refl
  ; leftQuarkChargeIsOneSixth =
      refl
  ; rightUpChargeIsTwoThirds =
      refl
  ; rightDownChargeIsMinusOneThird =
      refl
  ; higgsChargeIsPlusOne =
      refl
  ; selectedSymbolicAction =
      u1CanonicalSymbolicSectorAction
  ; selectedSymbolicActionIsU1 =
      refl
  ; selectedSymbolicActionSectorIsU1NonIdentity =
      refl
  ; upMatrixSymbolicallyIntertwined =
      refl
  ; downMatrixSymbolicallyIntertwined =
      refl
  ; phaseChargeSelectionConstructed =
      true
  ; phaseChargeSelectionConstructedIsTrue =
      refl
  ; physicalU1SectorRepresentationConstructed =
      false
  ; physicalU1SectorRepresentationConstructedIsFalse =
      refl
  ; receiptBoundary =
      "U(1) symbolic receipt selects the canonical charge primitives Q_L=+1/6, u_R=+2/3, d_R=-1/3, and H=+1 from MatterRepresentationReceiptSurface"
      ∷ "The selected U(1) symbolic sector action is non-identity at the sector-tag level"
      ∷ "The current carrier-level matrix check is still the finite symbolic identity action on the canonical diagonal up/down Yukawas"
      ∷ "No physical U(1) DHR sector representation or phase operator on physical Yukawa matrices is constructed here"
      ∷ []
  }

record SU2DoubletShapeSymbolicIntertwinerReceipt : Set₁ where
  field
    su2SectorObject :
      DHR.SU2SectorObject

    su2SectorObjectIsCanonical :
      su2SectorObject ≡ DHR.canonicalSU2SectorObject

    leftQuarkDoubletPrimitive :
      Matter.LeftQuarkDoubletFamilyPrimitive

    leftQuarkDoubletPrimitiveIsCanonical :
      leftQuarkDoubletPrimitive
      ≡
      Matter.canonicalLeftQuarkDoubletFamilyPrimitive

    higgsDoubletPrimitive :
      Matter.HiggsDoubletPrimitive

    higgsDoubletPrimitiveIsCanonical :
      higgsDoubletPrimitive
      ≡
      Matter.canonicalHiggsDoubletPrimitive

    rightUpQuarkPrimitive :
      Matter.RightUpQuarkFamilyPrimitive

    rightUpQuarkPrimitiveIsCanonical :
      rightUpQuarkPrimitive
      ≡
      Matter.canonicalRightUpQuarkFamilyPrimitive

    rightDownQuarkPrimitive :
      Matter.RightDownQuarkFamilyPrimitive

    rightDownQuarkPrimitiveIsCanonical :
      rightDownQuarkPrimitive
      ≡
      Matter.canonicalRightDownQuarkFamilyPrimitive

    leftQuarkWeakShapeIsDoublet :
      Matter.leftQuarkPrimitiveWeakRepresentation leftQuarkDoubletPrimitive
      ≡
      Matter.canonicalSU2LWeakDoubletPrimitive

    higgsWeakShapeIsDoublet :
      Matter.higgsPrimitiveWeakRepresentation higgsDoubletPrimitive
      ≡
      Matter.canonicalSU2LWeakDoubletPrimitive

    rightUpWeakShapeIsSinglet :
      Matter.rightUpQuarkPrimitiveWeakRepresentation rightUpQuarkPrimitive
      ≡
      Matter.canonicalSU2LWeakSingletPrimitive

    rightDownWeakShapeIsSinglet :
      Matter.rightDownQuarkPrimitiveWeakRepresentation rightDownQuarkPrimitive
      ≡
      Matter.canonicalSU2LWeakSingletPrimitive

    selectedSymbolicAction :
      YukawaDHRSymbolicCarrierAction

    selectedSymbolicActionIsSU2 :
      selectedSymbolicAction ≡ su2CanonicalSymbolicSectorAction

    selectedSymbolicActionSectorIsSU2NonIdentity :
      symbolicActionSector selectedSymbolicAction ≡ su2NonIdentitySector

    upMatrixSymbolicallyIntertwined :
      symbolicCarrierAction selectedSymbolicAction upYukawaMatrix
      ≡
      upYukawaMatrix

    downMatrixSymbolicallyIntertwined :
      symbolicCarrierAction selectedSymbolicAction downYukawaMatrix
      ≡
      downYukawaMatrix

    doubletShapeCheckConstructed :
      Bool

    doubletShapeCheckConstructedIsTrue :
      doubletShapeCheckConstructed ≡ true

    physicalSU2MatrixRepresentationConstructed :
      Bool

    physicalSU2MatrixRepresentationConstructedIsFalse :
      physicalSU2MatrixRepresentationConstructed ≡ false

    receiptBoundary :
      List String

open SU2DoubletShapeSymbolicIntertwinerReceipt public

canonicalSU2DoubletShapeSymbolicIntertwinerReceipt :
  SU2DoubletShapeSymbolicIntertwinerReceipt
canonicalSU2DoubletShapeSymbolicIntertwinerReceipt = record
  { su2SectorObject =
      DHR.canonicalSU2SectorObject
  ; su2SectorObjectIsCanonical =
      refl
  ; leftQuarkDoubletPrimitive =
      Matter.canonicalLeftQuarkDoubletFamilyPrimitive
  ; leftQuarkDoubletPrimitiveIsCanonical =
      refl
  ; higgsDoubletPrimitive =
      Matter.canonicalHiggsDoubletPrimitive
  ; higgsDoubletPrimitiveIsCanonical =
      refl
  ; rightUpQuarkPrimitive =
      Matter.canonicalRightUpQuarkFamilyPrimitive
  ; rightUpQuarkPrimitiveIsCanonical =
      refl
  ; rightDownQuarkPrimitive =
      Matter.canonicalRightDownQuarkFamilyPrimitive
  ; rightDownQuarkPrimitiveIsCanonical =
      refl
  ; leftQuarkWeakShapeIsDoublet =
      refl
  ; higgsWeakShapeIsDoublet =
      refl
  ; rightUpWeakShapeIsSinglet =
      refl
  ; rightDownWeakShapeIsSinglet =
      refl
  ; selectedSymbolicAction =
      su2CanonicalSymbolicSectorAction
  ; selectedSymbolicActionIsSU2 =
      refl
  ; selectedSymbolicActionSectorIsSU2NonIdentity =
      refl
  ; upMatrixSymbolicallyIntertwined =
      refl
  ; downMatrixSymbolicallyIntertwined =
      refl
  ; doubletShapeCheckConstructed =
      true
  ; doubletShapeCheckConstructedIsTrue =
      refl
  ; physicalSU2MatrixRepresentationConstructed =
      false
  ; physicalSU2MatrixRepresentationConstructedIsFalse =
      refl
  ; receiptBoundary =
      "SU(2) symbolic receipt checks that Q_L and H are the canonical weak doublets and u_R/d_R are canonical weak singlets"
      ∷ "The selected SU(2) symbolic sector action is non-identity at the sector-tag level"
      ∷ "The present finite matrix check remains the symbolic identity action on the canonical diagonal up/down Yukawas"
      ∷ "No physical SU(2) doublet representation matrices, Clebsch map, or DHR intertwiner on physical Yukawa matrices is constructed here"
      ∷ []
  }

record FiniteNonIdentityYukawaDHRSymbolicActionReceipt : Setω where
  field
    actionSectors :
      List YukawaDHRActionSector

    actionSectorsAreCanonical :
      actionSectors ≡ canonicalYukawaDHRActionSectors

    nonIdentityActionSectors :
      List YukawaDHRActionSector

    nonIdentityActionSectorsAreCanonical :
      nonIdentityActionSectors
      ≡
      canonicalNonIdentityYukawaDHRActionSectors

    identityAction :
      YukawaDHRSymbolicCarrierAction

    identityActionIsCanonical :
      identityAction ≡ identitySymbolicCarrierAction

    identityActionSectorIsIdentity :
      symbolicActionSector identityAction ≡ identityCarrierSector

    identityActionUpCompatible :
      symbolicCarrierAction identityAction upYukawaMatrix
      ≡
      upYukawaMatrix

    identityActionDownCompatible :
      symbolicCarrierAction identityAction downYukawaMatrix
      ≡
      downYukawaMatrix

    u1SectorObject :
      DHR.U1SectorObject

    u1SectorObjectIsCanonical :
      u1SectorObject ≡ DHR.canonicalU1SectorObject

    u1Action :
      YukawaDHRSymbolicCarrierAction

    u1ActionIsCanonicalNonIdentity :
      u1Action ≡ u1CanonicalSymbolicSectorAction

    u1ActionSectorIsNonIdentity :
      symbolicActionSector u1Action ≡ u1NonIdentitySector

    u1ActionUpCompatible :
      symbolicCarrierAction u1Action upYukawaMatrix
      ≡
      upYukawaMatrix

    u1ActionDownCompatible :
      symbolicCarrierAction u1Action downYukawaMatrix
      ≡
      downYukawaMatrix

    su2SectorObject :
      DHR.SU2SectorObject

    su2SectorObjectIsCanonical :
      su2SectorObject ≡ DHR.canonicalSU2SectorObject

    su2Action :
      YukawaDHRSymbolicCarrierAction

    su2ActionIsCanonicalNonIdentity :
      su2Action ≡ su2CanonicalSymbolicSectorAction

    su2ActionSectorIsNonIdentity :
      symbolicActionSector su2Action ≡ su2NonIdentitySector

    su2ActionUpCompatible :
      symbolicCarrierAction su2Action upYukawaMatrix
      ≡
      upYukawaMatrix

    su2ActionDownCompatible :
      symbolicCarrierAction su2Action downYukawaMatrix
      ≡
      downYukawaMatrix

    su3FrontierObject :
      DHR.SU3FrontierObject

    su3Action :
      YukawaDHRSymbolicCarrierAction

    su3ActionIsCanonicalNonIdentity :
      su3Action ≡ su3Depth9CanonicalSymbolicFrontierAction

    su3ActionSectorIsNonIdentity :
      symbolicActionSector su3Action
      ≡
      su3Depth9NonIdentityFrontierSector

    su3ActionUpCompatible :
      symbolicCarrierAction su3Action upYukawaMatrix
      ≡
      upYukawaMatrix

    su3ActionDownCompatible :
      symbolicCarrierAction su3Action downYukawaMatrix
      ≡
      downYukawaMatrix

    u1PhaseChargeSelectionReceipt :
      U1PhaseChargeSelectionSymbolicIntertwinerReceipt

    u1PhaseChargeSelectionReceiptIsCanonical :
      u1PhaseChargeSelectionReceipt
      ≡
      canonicalU1PhaseChargeSelectionSymbolicIntertwinerReceipt

    su2DoubletShapeReceipt :
      SU2DoubletShapeSymbolicIntertwinerReceipt

    su2DoubletShapeReceiptIsCanonical :
      su2DoubletShapeReceipt
      ≡
      canonicalSU2DoubletShapeSymbolicIntertwinerReceipt

    nonIdentitySymbolicActionsConstructed :
      Bool

    nonIdentitySymbolicActionsConstructedIsTrue :
      nonIdentitySymbolicActionsConstructed ≡ true

    physicalMatrixActionBeyondIdentityConstructed :
      Bool

    physicalMatrixActionBeyondIdentityConstructedIsFalse :
      physicalMatrixActionBeyondIdentityConstructed ≡ false

    symbolicActionBoundary :
      List String

open FiniteNonIdentityYukawaDHRSymbolicActionReceipt public

canonicalFiniteNonIdentityYukawaDHRSymbolicActionReceipt :
  FiniteNonIdentityYukawaDHRSymbolicActionReceipt
canonicalFiniteNonIdentityYukawaDHRSymbolicActionReceipt = record
  { actionSectors =
      canonicalYukawaDHRActionSectors
  ; actionSectorsAreCanonical =
      refl
  ; nonIdentityActionSectors =
      canonicalNonIdentityYukawaDHRActionSectors
  ; nonIdentityActionSectorsAreCanonical =
      refl
  ; identityAction =
      identitySymbolicCarrierAction
  ; identityActionIsCanonical =
      refl
  ; identityActionSectorIsIdentity =
      refl
  ; identityActionUpCompatible =
      refl
  ; identityActionDownCompatible =
      refl
  ; u1SectorObject =
      DHR.canonicalU1SectorObject
  ; u1SectorObjectIsCanonical =
      refl
  ; u1Action =
      u1CanonicalSymbolicSectorAction
  ; u1ActionIsCanonicalNonIdentity =
      refl
  ; u1ActionSectorIsNonIdentity =
      refl
  ; u1ActionUpCompatible =
      refl
  ; u1ActionDownCompatible =
      refl
  ; su2SectorObject =
      DHR.canonicalSU2SectorObject
  ; su2SectorObjectIsCanonical =
      refl
  ; su2Action =
      su2CanonicalSymbolicSectorAction
  ; su2ActionIsCanonicalNonIdentity =
      refl
  ; su2ActionSectorIsNonIdentity =
      refl
  ; su2ActionUpCompatible =
      refl
  ; su2ActionDownCompatible =
      refl
  ; su3FrontierObject =
      DHR.canonicalSU3FrontierObject
  ; su3Action =
      su3Depth9CanonicalSymbolicFrontierAction
  ; su3ActionIsCanonicalNonIdentity =
      refl
  ; su3ActionSectorIsNonIdentity =
      refl
  ; su3ActionUpCompatible =
      refl
  ; su3ActionDownCompatible =
      refl
  ; u1PhaseChargeSelectionReceipt =
      canonicalU1PhaseChargeSelectionSymbolicIntertwinerReceipt
  ; u1PhaseChargeSelectionReceiptIsCanonical =
      refl
  ; su2DoubletShapeReceipt =
      canonicalSU2DoubletShapeSymbolicIntertwinerReceipt
  ; su2DoubletShapeReceiptIsCanonical =
      refl
  ; nonIdentitySymbolicActionsConstructed =
      true
  ; nonIdentitySymbolicActionsConstructedIsTrue =
      refl
  ; physicalMatrixActionBeyondIdentityConstructed =
      false
  ; physicalMatrixActionBeyondIdentityConstructedIsFalse =
      refl
  ; symbolicActionBoundary =
      "Identity-sector coverage is explicit as the carrier identity action on the canonical diagonal Yukawa matrices"
      ∷ "U(1), SU(2), and depth-9 SU(3)-frontier sectors have finite symbolic non-identity action constructors"
      ∷ "U(1) phase/charge-selection is inhabited by the canonical Q_L/u_R/d_R/H hypercharge primitives"
      ∷ "SU(2) doublet-shape checking is inhabited by the canonical Q_L and H doublet primitives plus u_R/d_R singlet primitives"
      ∷ "Each symbolic non-identity sector action preserves the canonical up/down Yukawa matrices by definitional equality"
      ∷ "These are symbolic sector actions over existing DHR atoms, not a promoted physical non-identity matrix action"
      ∷ "No physical fermion mass, generic eigenbasis, or Standard Model action promotion is introduced"
      ∷ []
  }

record U1YukawaDHRIntertwinerCompatibility : Setω where
  field
    u1SectorObject :
      DHR.U1SectorObject

    u1SectorObjectIsCanonical :
      u1SectorObject ≡ DHR.canonicalU1SectorObject

    u1UpYukawaCompatible :
      carrierActionIdentity upYukawaMatrix ≡ upYukawaMatrix

    u1DownYukawaCompatible :
      carrierActionIdentity downYukawaMatrix ≡ downYukawaMatrix

    u1Boundary :
      List String

open U1YukawaDHRIntertwinerCompatibility public

canonicalU1YukawaDHRIntertwinerCompatibility :
  U1YukawaDHRIntertwinerCompatibility
canonicalU1YukawaDHRIntertwinerCompatibility = record
  { u1SectorObject = DHR.canonicalU1SectorObject
  ; u1SectorObjectIsCanonical = refl
  ; u1UpYukawaCompatible = refl
  ; u1DownYukawaCompatible = refl
  ; u1Boundary =
      "U(1) is carried by the canonical graded sector object already present in DHRSectorDecomposition"
      ∷ "The Yukawa carrier action on the U(1) lane is the identity on the canonical up/down matrices"
      ∷ []
  }

record SU2YukawaDHRIntertwinerCompatibility : Setω where
  field
    su2SectorObject :
      DHR.SU2SectorObject

    su2SectorObjectIsCanonical :
      su2SectorObject ≡ DHR.canonicalSU2SectorObject

    su2UpYukawaCompatible :
      carrierActionIdentity upYukawaMatrix ≡ upYukawaMatrix

    su2DownYukawaCompatible :
      carrierActionIdentity downYukawaMatrix ≡ downYukawaMatrix

    su2Boundary :
      List String

open SU2YukawaDHRIntertwinerCompatibility public

canonicalSU2YukawaDHRIntertwinerCompatibility :
  SU2YukawaDHRIntertwinerCompatibility
canonicalSU2YukawaDHRIntertwinerCompatibility = record
  { su2SectorObject = DHR.canonicalSU2SectorObject
  ; su2SectorObjectIsCanonical = refl
  ; su2UpYukawaCompatible = refl
  ; su2DownYukawaCompatible = refl
  ; su2Boundary =
      "SU(2) is carried by the canonical nonabelian sector bundle already present in DHRSectorDecomposition"
      ∷ "The Yukawa carrier action on the SU(2) lane is the identity on the canonical up/down matrices"
      ∷ []
  }

record SU3Depth9YukawaDHRIntertwinerCompatibility : Setω where
  field
    su3FrontierObject :
      DHR.SU3FrontierObject

    su3UpYukawaCompatible :
      carrierActionIdentity upYukawaMatrix ≡ upYukawaMatrix

    su3DownYukawaCompatible :
      carrierActionIdentity downYukawaMatrix ≡ downYukawaMatrix

    su3Boundary :
      List String

open SU3Depth9YukawaDHRIntertwinerCompatibility public

canonicalSU3Depth9YukawaDHRIntertwinerCompatibility :
  SU3Depth9YukawaDHRIntertwinerCompatibility
canonicalSU3Depth9YukawaDHRIntertwinerCompatibility = record
  { su3FrontierObject = DHR.canonicalSU3FrontierObject
  ; su3UpYukawaCompatible = refl
  ; su3DownYukawaCompatible = refl
  ; su3Boundary =
      "The depth-9 color route is carried by the canonical SU(3) frontier object already present in DHRSectorDecomposition"
      ∷ "The upstream rho3 witness is the existing depth-quotient SU(3) bridge, and the Yukawa carrier action is identity on the canonical matrices"
      ∷ []
  }

record YukawaDHRIntertwinerCompatibilityReceipt : Setω where
  field
    ckmCarrierDerivedReceipt :
      CKMD.CKMCarrierDerivedReceipt

    carrierCKMMatrix :
      Matter.MixingMatrix

    carrierCKMMatrixIsDerived :
      carrierCKMMatrix
      ≡
      CKMD.ckmCarrierMatrix ckmCarrierDerivedReceipt

    carrierCKMMatrixIsIdentity :
      carrierCKMMatrix ≡ Matter.identityMixingMatrix

    u1Compatibility :
      U1YukawaDHRIntertwinerCompatibility

    su2Compatibility :
      SU2YukawaDHRIntertwinerCompatibility

    su3Compatibility :
      SU3Depth9YukawaDHRIntertwinerCompatibility

    finiteNonIdentitySymbolicActionReceipt :
      FiniteNonIdentityYukawaDHRSymbolicActionReceipt

    carrierDHRYukawaFormulaSurface :
      CarrierDHRYukawaFormulaSurface

    carrierDHRYukawaFormulaSurfaceLabel :
      formulaLabel carrierDHRYukawaFormulaSurface
      ≡
      "Y_ij = <rho_i, Phi_H * rho_j>"

    carrierDHRYukawaFormulaUpEntriesAgree :
      (i j : YukawaGenerationIndex) →
      upFormulaEntry carrierDHRYukawaFormulaSurface i j
      ≡
      matrixEntry upYukawaMatrix i j

    carrierDHRYukawaFormulaDownEntriesAgree :
      (i j : YukawaGenerationIndex) →
      downFormulaEntry carrierDHRYukawaFormulaSurface i j
      ≡
      matrixEntry downYukawaMatrix i j

    carrierDHRYukawaFormulaPhysicalPromotionClosed :
      physicalDHRYukawaFormulaPromoted carrierDHRYukawaFormulaSurface
      ≡
      false

    u1PhaseChargeSelectionReceipt :
      U1PhaseChargeSelectionSymbolicIntertwinerReceipt

    u1PhaseChargeSelectionReceiptMatchesFiniteReceipt :
      u1PhaseChargeSelectionReceipt
      ≡
      FiniteNonIdentityYukawaDHRSymbolicActionReceipt.u1PhaseChargeSelectionReceipt
        finiteNonIdentitySymbolicActionReceipt

    u1PhaseChargeSelectionConstructed :
      Bool

    u1PhaseChargeSelectionConstructedIsTrue :
      u1PhaseChargeSelectionConstructed ≡ true

    u1PhysicalSectorRepresentationConstructed :
      Bool

    u1PhysicalSectorRepresentationConstructedMatchesReceipt :
      u1PhysicalSectorRepresentationConstructed
      ≡
      physicalU1SectorRepresentationConstructed
        u1PhaseChargeSelectionReceipt

    u1PhysicalSectorRepresentationConstructedIsFalse :
      u1PhysicalSectorRepresentationConstructed ≡ false

    su2DoubletShapeReceipt :
      SU2DoubletShapeSymbolicIntertwinerReceipt

    su2DoubletShapeReceiptMatchesFiniteReceipt :
      su2DoubletShapeReceipt
      ≡
      FiniteNonIdentityYukawaDHRSymbolicActionReceipt.su2DoubletShapeReceipt
        finiteNonIdentitySymbolicActionReceipt

    su2DoubletShapeCheckConstructed :
      Bool

    su2DoubletShapeCheckConstructedIsTrue :
      su2DoubletShapeCheckConstructed ≡ true

    su2PhysicalMatrixRepresentationConstructed :
      Bool

    su2PhysicalMatrixRepresentationConstructedMatchesReceipt :
      su2PhysicalMatrixRepresentationConstructed
      ≡
      physicalSU2MatrixRepresentationConstructed
        su2DoubletShapeReceipt

    su2PhysicalMatrixRepresentationConstructedIsFalse :
      su2PhysicalMatrixRepresentationConstructed ≡ false

    identitySectorActionExplicit :
      Bool

    identitySectorActionExplicitIsTrue :
      identitySectorActionExplicit ≡ true

    nonIdentitySymbolicSectorActionsConstructed :
      Bool

    nonIdentitySymbolicSectorActionsConstructedMatchesReceipt :
      nonIdentitySymbolicSectorActionsConstructed
      ≡
      nonIdentitySymbolicActionsConstructed
        finiteNonIdentitySymbolicActionReceipt

    nonIdentitySymbolicSectorActionsConstructedIsTrue :
      nonIdentitySymbolicSectorActionsConstructed ≡ true

    physicalNonIdentityDHRActionConstructed :
      Bool

    physicalNonIdentityDHRActionConstructedMatchesSymbolicReceipt :
      physicalNonIdentityDHRActionConstructed
      ≡
      physicalMatrixActionBeyondIdentityConstructed
        finiteNonIdentitySymbolicActionReceipt

    physicalNonIdentityDHRActionConstructedIsFalse :
      physicalNonIdentityDHRActionConstructed ≡ false

    exactFullSMCompatibility :
      Exact.YukawaDHRIntertwinerCompatibilityWitness

    exactFullSMCompatibilityIsCanonical :
      exactFullSMCompatibility
      ≡
      Exact.canonicalYukawaDHRIntertwinerCompatibilityWitness

    upYukawaMatrixAgreesWithCarrier :
      upYukawaMatrix
      ≡
      CKMD.yukawaUpMatrix ckmCarrierDerivedReceipt

    downYukawaMatrixAgreesWithCarrier :
      downYukawaMatrix
      ≡
      CKMD.yukawaDownMatrix ckmCarrierDerivedReceipt

    splittingFieldEigenbasisLedger :
      Exact.CKMSplittingFieldEigenbasisFailClosedLedger

    exactDHRActionUpCompatible :
      Exact.dhrAction exactFullSMCompatibility upYukawaMatrix
      ≡
      upYukawaMatrix

    exactDHRActionDownCompatible :
      Exact.dhrAction exactFullSMCompatibility downYukawaMatrix
      ≡
      downYukawaMatrix

    carrierIdentityActionAgreesWithExactOnUp :
      carrierActionIdentity upYukawaMatrix
      ≡
      Exact.dhrAction exactFullSMCompatibility upYukawaMatrix

    carrierIdentityActionAgreesWithExactOnDown :
      carrierActionIdentity downYukawaMatrix
      ≡
      Exact.dhrAction exactFullSMCompatibility downYukawaMatrix

    compatibilityBlockers :
      List YukawaDHRCompatibilityBlocker

    compatibilityBlockersAreCanonical :
      compatibilityBlockers ≡ canonicalYukawaDHRCompatibilityBlockers

    firstCompatibilityBlocker :
      YukawaDHRCompatibilityBlocker

    firstCompatibilityBlockerIsPhysicalFermionMass :
      firstCompatibilityBlocker ≡ missingPhysicalFermionMassReceipt

    physicalFermionMassReceiptsConstructed :
      Bool

    physicalFermionMassReceiptsConstructedIsFalse :
      physicalFermionMassReceiptsConstructed ≡ false

    absoluteHiggsScaleW4CalibrationConstructed :
      Bool

    absoluteHiggsScaleW4CalibrationConstructedIsFalse :
      absoluteHiggsScaleW4CalibrationConstructed ≡ false

    actualDHRSectorRepresentationsConstructed :
      Bool

    actualDHRSectorRepresentationsConstructedIsFalse :
      actualDHRSectorRepresentationsConstructed ≡ false

    physicalYukawaMatricesSupplied :
      Bool

    physicalYukawaMatricesSuppliedIsFalse :
      physicalYukawaMatricesSupplied ≡ false

    genericYukawaSplittingFieldEigenbasisConstructed :
      Bool

    genericYukawaSplittingFieldEigenbasisConstructedIsFalse :
      genericYukawaSplittingFieldEigenbasisConstructed ≡ false

    dhrActionBeyondIdentityConstructed :
      Bool

    dhrActionBeyondIdentityConstructedIsFalse :
      dhrActionBeyondIdentityConstructed ≡ false

    physicalYukawaDHRPromotionConstructed :
      Bool

    physicalYukawaDHRPromotionConstructedIsFalse :
      physicalYukawaDHRPromotionConstructed ≡ false

    receiptBoundary :
      List String

open YukawaDHRIntertwinerCompatibilityReceipt public

canonicalYukawaDHRIntertwinerCompatibility :
  YukawaDHRIntertwinerCompatibilityReceipt
canonicalYukawaDHRIntertwinerCompatibility = record
  { ckmCarrierDerivedReceipt = CKMD.canonicalCKMCarrierDerived
  ; carrierCKMMatrix =
      CKMD.ckmCarrierMatrix CKMD.canonicalCKMCarrierDerived
  ; carrierCKMMatrixIsDerived = refl
  ; carrierCKMMatrixIsIdentity = refl
  ; u1Compatibility = canonicalU1YukawaDHRIntertwinerCompatibility
  ; su2Compatibility = canonicalSU2YukawaDHRIntertwinerCompatibility
  ; su3Compatibility = canonicalSU3Depth9YukawaDHRIntertwinerCompatibility
  ; finiteNonIdentitySymbolicActionReceipt =
      canonicalFiniteNonIdentityYukawaDHRSymbolicActionReceipt
  ; carrierDHRYukawaFormulaSurface =
      canonicalCarrierDHRYukawaFormulaSurface
  ; carrierDHRYukawaFormulaSurfaceLabel =
      refl
  ; carrierDHRYukawaFormulaUpEntriesAgree =
      λ _ _ → refl
  ; carrierDHRYukawaFormulaDownEntriesAgree =
      λ _ _ → refl
  ; carrierDHRYukawaFormulaPhysicalPromotionClosed =
      refl
  ; u1PhaseChargeSelectionReceipt =
      canonicalU1PhaseChargeSelectionSymbolicIntertwinerReceipt
  ; u1PhaseChargeSelectionReceiptMatchesFiniteReceipt =
      refl
  ; u1PhaseChargeSelectionConstructed =
      phaseChargeSelectionConstructed
        canonicalU1PhaseChargeSelectionSymbolicIntertwinerReceipt
  ; u1PhaseChargeSelectionConstructedIsTrue =
      refl
  ; u1PhysicalSectorRepresentationConstructed =
      physicalU1SectorRepresentationConstructed
        canonicalU1PhaseChargeSelectionSymbolicIntertwinerReceipt
  ; u1PhysicalSectorRepresentationConstructedMatchesReceipt =
      refl
  ; u1PhysicalSectorRepresentationConstructedIsFalse =
      refl
  ; su2DoubletShapeReceipt =
      canonicalSU2DoubletShapeSymbolicIntertwinerReceipt
  ; su2DoubletShapeReceiptMatchesFiniteReceipt =
      refl
  ; su2DoubletShapeCheckConstructed =
      doubletShapeCheckConstructed
        canonicalSU2DoubletShapeSymbolicIntertwinerReceipt
  ; su2DoubletShapeCheckConstructedIsTrue =
      refl
  ; su2PhysicalMatrixRepresentationConstructed =
      physicalSU2MatrixRepresentationConstructed
        canonicalSU2DoubletShapeSymbolicIntertwinerReceipt
  ; su2PhysicalMatrixRepresentationConstructedMatchesReceipt =
      refl
  ; su2PhysicalMatrixRepresentationConstructedIsFalse =
      refl
  ; identitySectorActionExplicit = true
  ; identitySectorActionExplicitIsTrue = refl
  ; nonIdentitySymbolicSectorActionsConstructed =
      nonIdentitySymbolicActionsConstructed
        canonicalFiniteNonIdentityYukawaDHRSymbolicActionReceipt
  ; nonIdentitySymbolicSectorActionsConstructedMatchesReceipt = refl
  ; nonIdentitySymbolicSectorActionsConstructedIsTrue = refl
  ; physicalNonIdentityDHRActionConstructed =
      physicalMatrixActionBeyondIdentityConstructed
        canonicalFiniteNonIdentityYukawaDHRSymbolicActionReceipt
  ; physicalNonIdentityDHRActionConstructedMatchesSymbolicReceipt =
      refl
  ; physicalNonIdentityDHRActionConstructedIsFalse = refl
  ; exactFullSMCompatibility =
      Exact.canonicalYukawaDHRIntertwinerCompatibilityWitness
  ; exactFullSMCompatibilityIsCanonical = refl
  ; upYukawaMatrixAgreesWithCarrier = refl
  ; downYukawaMatrixAgreesWithCarrier = refl
  ; splittingFieldEigenbasisLedger =
      Exact.canonicalCKMSplittingFieldEigenbasisFailClosedLedger
  ; exactDHRActionUpCompatible = refl
  ; exactDHRActionDownCompatible = refl
  ; carrierIdentityActionAgreesWithExactOnUp = refl
  ; carrierIdentityActionAgreesWithExactOnDown = refl
  ; compatibilityBlockers =
      canonicalYukawaDHRCompatibilityBlockers
  ; compatibilityBlockersAreCanonical = refl
  ; firstCompatibilityBlocker =
      missingPhysicalFermionMassReceipt
  ; firstCompatibilityBlockerIsPhysicalFermionMass = refl
  ; physicalFermionMassReceiptsConstructed = false
  ; physicalFermionMassReceiptsConstructedIsFalse = refl
  ; absoluteHiggsScaleW4CalibrationConstructed = false
  ; absoluteHiggsScaleW4CalibrationConstructedIsFalse = refl
  ; actualDHRSectorRepresentationsConstructed = false
  ; actualDHRSectorRepresentationsConstructedIsFalse = refl
  ; physicalYukawaMatricesSupplied = false
  ; physicalYukawaMatricesSuppliedIsFalse = refl
  ; genericYukawaSplittingFieldEigenbasisConstructed = false
  ; genericYukawaSplittingFieldEigenbasisConstructedIsFalse = refl
  ; dhrActionBeyondIdentityConstructed = false
  ; dhrActionBeyondIdentityConstructedIsFalse = refl
  ; physicalYukawaDHRPromotionConstructed = false
  ; physicalYukawaDHRPromotionConstructedIsFalse = refl
  ; receiptBoundary =
      "Factorwise compatibility is recorded for the existing U(1), SU(2), and depth-9 color sector objects"
      ∷ "Identity-sector action coverage is explicit in the finite symbolic action receipt"
      ∷ "Finite symbolic non-identity sector actions are inhabited for the existing DHR atoms and preserve the canonical diagonal Yukawa matrices"
      ∷ "U(1) phase/charge-selection now has a finite receipt over canonical Q_L/u_R/d_R/H hypercharge primitives"
      ∷ "SU(2) doublet-shape now has a finite receipt over canonical Q_L and H doublets with u_R/d_R singlets"
      ∷ "The carrier formula surface records Y_ij = <rho_i, Phi_H * rho_j> as exact matrix-entry access on the canonical diagonal up/down Yukawa carriers"
      ∷ "That formula surface consumes the Higgs receipt plus the carrier-derived and unitarity CKM receipts, but keeps physical rho_i/rho_j endomorphisms, Phi_H operator semantics, and bra-ket pairing as false blockers"
      ∷ "The carrier action is the identity on the canonical diagonal Yukawa matrices already present in CKMExactWitnesses"
      ∷ "The full SM-sector compatibility receipt is consumed from the canonical exact witness chain"
      ∷ "The carrier-derived CKM matrix is threaded as the same concrete identity matrix used by the exact chain"
      ∷ "The exact DHR action socket is wired only in the identity case on the canonical up/down Yukawa matrices"
      ∷ "Physical fermion masses, generic splitting-field/eigenbasis data, absolute Higgs scale, actual DHR sector representations, physical Yukawa matrices, and physical non-identity DHR action remain exact blockers"
      ∷ "Actual DHR sector representations and physical Yukawa matrices are still required before any non-identity physical promotion"
      ∷ "No physical non-identity DHR action, splitting-field/eigenbasis lift, physical mass receipt, or physical Yukawa/DHR promotion is introduced"
      ∷ "No postulates, stubs, or external numerics are introduced here"
      ∷ []
  }

canonicalYukawaDHRIntertwinerKeepsPromotionClosed :
  physicalYukawaDHRPromotionConstructed
    canonicalYukawaDHRIntertwinerCompatibility
  ≡
  false
canonicalYukawaDHRIntertwinerKeepsPromotionClosed =
  refl

canonicalU1PhaseChargeSelectionIsInhabited :
  phaseChargeSelectionConstructed
    canonicalU1PhaseChargeSelectionSymbolicIntertwinerReceipt
  ≡
  true
canonicalU1PhaseChargeSelectionIsInhabited =
  refl

canonicalU1PhysicalSectorRepresentationStillBlocked :
  physicalU1SectorRepresentationConstructed
    canonicalU1PhaseChargeSelectionSymbolicIntertwinerReceipt
  ≡
  false
canonicalU1PhysicalSectorRepresentationStillBlocked =
  refl

canonicalSU2DoubletShapeCheckIsInhabited :
  doubletShapeCheckConstructed
    canonicalSU2DoubletShapeSymbolicIntertwinerReceipt
  ≡
  true
canonicalSU2DoubletShapeCheckIsInhabited =
  refl

canonicalSU2PhysicalMatrixRepresentationStillBlocked :
  physicalSU2MatrixRepresentationConstructed
    canonicalSU2DoubletShapeSymbolicIntertwinerReceipt
  ≡
  false
canonicalSU2PhysicalMatrixRepresentationStillBlocked =
  refl

canonicalYukawaDHRIntertwinerKeepsNonIdentityActionClosed :
  dhrActionBeyondIdentityConstructed
    canonicalYukawaDHRIntertwinerCompatibility
  ≡
  false
canonicalYukawaDHRIntertwinerKeepsNonIdentityActionClosed =
  refl

canonicalYukawaDHRActualSectorRepresentationsStillBlocked :
  actualDHRSectorRepresentationsConstructed
    canonicalYukawaDHRIntertwinerCompatibility
  ≡
  false
canonicalYukawaDHRActualSectorRepresentationsStillBlocked =
  refl

canonicalYukawaDHRPhysicalMatricesStillBlocked :
  physicalYukawaMatricesSupplied
    canonicalYukawaDHRIntertwinerCompatibility
  ≡
  false
canonicalYukawaDHRPhysicalMatricesStillBlocked =
  refl
