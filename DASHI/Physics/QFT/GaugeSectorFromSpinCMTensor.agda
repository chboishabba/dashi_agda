module DASHI.Physics.QFT.GaugeSectorFromSpinCMTensor where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.ConditionalGDHRSMPromotionReceipt as Conditional
import DASHI.Physics.QFT.FiniteDHRAbelianReconstructionReceipt as FiniteDHR
import DASHI.Physics.QFT.NonAbelianFusionFromSpin as NonAbelian

------------------------------------------------------------------------
-- Conditional DR compact-group surface for C_phys = C_CM boxtimes Rep(SU2).
--
-- This receipt records only the candidate readback requested by the finite
-- CM-character surface tensored with a supplied spin-sector Rep(SU2).  It
-- does not construct the full DHR category, apply the DR theorem internally,
-- identify SU(3)c, derive U(1)Y from the Z/4 factor, or reconstruct the exact
-- Standard Model gauge sector.

data PhysicalTensorFactor : Set where
  cmFiniteCharacterCategory :
    PhysicalTensorFactor

  repSU2SpinCategory :
    PhysicalTensorFactor

canonicalPhysicalTensorFactors :
  List PhysicalTensorFactor
canonicalPhysicalTensorFactors =
  cmFiniteCharacterCategory
  ∷ repSU2SpinCategory
  ∷ []

data PhysicalGaugeCandidateFactor : Set where
  finiteCMAbelianDualFactor :
    PhysicalGaugeCandidateFactor

  su2SpinCompactFactor :
    PhysicalGaugeCandidateFactor

canonicalPhysicalGaugeCandidateFactors :
  List PhysicalGaugeCandidateFactor
canonicalPhysicalGaugeCandidateFactors =
  finiteCMAbelianDualFactor
  ∷ su2SpinCompactFactor
  ∷ []

data SpinCMTensorOpenProblem : Set where
  openSU3cGapIdentification :
    SpinCMTensorOpenProblem

  openU1YFromZ4CandidateIdentification :
    SpinCMTensorOpenProblem

  openExactStandardModelReconstruction :
    SpinCMTensorOpenProblem

canonicalSpinCMTensorOpenProblems :
  List SpinCMTensorOpenProblem
canonicalSpinCMTensorOpenProblems =
  openSU3cGapIdentification
  ∷ openU1YFromZ4CandidateIdentification
  ∷ openExactStandardModelReconstruction
  ∷ []

data DRCompactGroupSurfaceStatus : Set where
  conditionalDRCompactGroupCandidate :
    DRCompactGroupSurfaceStatus

  exactDRCompactGroupReconstruction :
    DRCompactGroupSurfaceStatus

candidatePhysicalCategoryLabel : String
candidatePhysicalCategoryLabel =
  "C_phys = C_CM boxtimes Rep(SU2)"

candidatePhysicalGaugeGroupLabel : String
candidatePhysicalGaugeGroupLabel =
  "G_DHR,phys candidate = (Z/4 x Z/6 x Z/2) x SU2"

conditionalSpinSectorSU2LLabel : String
conditionalSpinSectorSU2LLabel =
  "SU2L is recorded as the conditional compact spin-sector factor from Rep(SU2)"

openSU3cGapLabel : String
openSU3cGapLabel =
  "SU3c is not identified by the C_CM boxtimes Rep(SU2) candidate surface"

openU1YFromZ4Label : String
openU1YFromZ4Label =
  "U1Y from the Z/4 CM-character candidate remains an open identification"

exactSMReconstructionFalseLabel : String
exactSMReconstructionFalseLabel =
  "Exact Standard Model reconstruction is false for this conditional candidate surface"

record SpinCMTensorPhysicalCategoryCandidate : Setω where
  field
    tensorFactors :
      List PhysicalTensorFactor

    tensorFactorsAreCanonical :
      tensorFactors ≡ canonicalPhysicalTensorFactors

    finiteCMReceipt :
      FiniteDHR.FiniteDHRAbelianReconstructionReceipt

    finiteCMCharacterGroup :
      String

    finiteCMCharacterGroupIsCanonical :
      finiteCMCharacterGroup
      ≡
      FiniteDHR.finiteAbelianDualGroupLabel

    spinSectorFactor :
      String

    spinSectorFactorIsRepSU2 :
      spinSectorFactor ≡ "Rep(SU2)"

    physicalCategory :
      String

    physicalCategoryIsCanonical :
      physicalCategory ≡ candidatePhysicalCategoryLabel

    cmSurfaceCardinality :
      Nat

    cmSurfaceCardinalityIsFortyEight :
      cmSurfaceCardinality ≡ 48

    cmSurfaceCardinalityIsProduct :
      cmSurfaceCardinality ≡ 4 * 6 * 2

open SpinCMTensorPhysicalCategoryCandidate public

canonicalSpinCMTensorPhysicalCategoryCandidate :
  SpinCMTensorPhysicalCategoryCandidate
canonicalSpinCMTensorPhysicalCategoryCandidate =
  record
    { tensorFactors =
        canonicalPhysicalTensorFactors
    ; tensorFactorsAreCanonical =
        refl
    ; finiteCMReceipt =
        FiniteDHR.canonicalFiniteDHRAbelianReconstructionReceipt
    ; finiteCMCharacterGroup =
        FiniteDHR.finiteAbelianDualGroupLabel
    ; finiteCMCharacterGroupIsCanonical =
        refl
    ; spinSectorFactor =
        "Rep(SU2)"
    ; spinSectorFactorIsRepSU2 =
        refl
    ; physicalCategory =
        candidatePhysicalCategoryLabel
    ; physicalCategoryIsCanonical =
        refl
    ; cmSurfaceCardinality =
        48
    ; cmSurfaceCardinalityIsFortyEight =
        refl
    ; cmSurfaceCardinalityIsProduct =
        refl
    }

record GaugeSectorFromSpinCMTensorReceipt : Setω where
  field
    physicalCategoryCandidate :
      SpinCMTensorPhysicalCategoryCandidate

    conditionalPromotionReceipt :
      Conditional.ConditionalGDHRSMPromotionReceipt

    nonAbelianFusionReceipt :
      NonAbelian.NonAbelianFusionFromSpinSectorReceipt

    nonAbelianFusionFromSpinSector :
      NonAbelian.nonAbelianFusionFromSpinSector nonAbelianFusionReceipt
      ≡
      true

    nonAbelianFusionKeepsExactGSMFalse :
      NonAbelian.exactGDHREqualsGSM nonAbelianFusionReceipt
      ≡
      false

    drCompactGroupSurfaceStatus :
      DRCompactGroupSurfaceStatus

    drCompactGroupSurfaceStatusIsConditionalCandidate :
      drCompactGroupSurfaceStatus ≡ conditionalDRCompactGroupCandidate

    candidateFactors :
      List PhysicalGaugeCandidateFactor

    candidateFactorsAreCanonical :
      candidateFactors ≡ canonicalPhysicalGaugeCandidateFactors

    gDHRPhysCandidate :
      String

    gDHRPhysCandidateIsCanonical :
      gDHRPhysCandidate ≡ candidatePhysicalGaugeGroupLabel

    su2LFromSpinSector :
      Bool

    su2LFromSpinSectorIsTrue :
      su2LFromSpinSector ≡ true

    su2LFromSpinSectorConditional :
      Bool

    su2LFromSpinSectorConditionalIsTrue :
      su2LFromSpinSectorConditional ≡ true

    su2LFromSpinSectorCondition :
      String

    su2LFromSpinSectorConditionIsCanonical :
      su2LFromSpinSectorCondition ≡ conditionalSpinSectorSU2LLabel

    su3cGapIdentified :
      Bool

    su3cGapIdentifiedIsFalse :
      su3cGapIdentified ≡ false

    su3cGapOpenProblem :
      String

    su3cGapOpenProblemIsCanonical :
      su3cGapOpenProblem ≡ openSU3cGapLabel

    u1yFromZ4Candidate :
      Bool

    u1yFromZ4CandidateIsFalse :
      u1yFromZ4Candidate ≡ false

    u1yFromZ4CandidateOpenProblem :
      String

    u1yFromZ4CandidateOpenProblemIsCanonical :
      u1yFromZ4CandidateOpenProblem ≡ openU1YFromZ4Label

    exactSMReconstruction :
      Bool

    exactSMReconstructionIsFalse :
      exactSMReconstruction ≡ false

    exactSMReconstructionBoundary :
      String

    exactSMReconstructionBoundaryIsCanonical :
      exactSMReconstructionBoundary ≡ exactSMReconstructionFalseLabel

    openProblems :
      List SpinCMTensorOpenProblem

    openProblemsAreCanonical :
      openProblems ≡ canonicalSpinCMTensorOpenProblems

    receiptBoundary :
      List String

open GaugeSectorFromSpinCMTensorReceipt public

canonicalGaugeSectorFromSpinCMTensorReceipt :
  GaugeSectorFromSpinCMTensorReceipt
canonicalGaugeSectorFromSpinCMTensorReceipt =
  record
    { physicalCategoryCandidate =
        canonicalSpinCMTensorPhysicalCategoryCandidate
    ; conditionalPromotionReceipt =
        Conditional.canonicalConditionalGDHRSMPromotionReceipt
    ; nonAbelianFusionReceipt =
        NonAbelian.canonicalNonAbelianFusionFromSpinSectorReceipt
    ; nonAbelianFusionFromSpinSector =
        NonAbelian.nonAbelianFusionFromSpinSectorConditionalTrue
    ; nonAbelianFusionKeepsExactGSMFalse =
        NonAbelian.nonAbelianFusionFromSpinKeepsExactGDHRGSMFalse
    ; drCompactGroupSurfaceStatus =
        conditionalDRCompactGroupCandidate
    ; drCompactGroupSurfaceStatusIsConditionalCandidate =
        refl
    ; candidateFactors =
        canonicalPhysicalGaugeCandidateFactors
    ; candidateFactorsAreCanonical =
        refl
    ; gDHRPhysCandidate =
        candidatePhysicalGaugeGroupLabel
    ; gDHRPhysCandidateIsCanonical =
        refl
    ; su2LFromSpinSector =
        true
    ; su2LFromSpinSectorIsTrue =
        refl
    ; su2LFromSpinSectorConditional =
        true
    ; su2LFromSpinSectorConditionalIsTrue =
        refl
    ; su2LFromSpinSectorCondition =
        conditionalSpinSectorSU2LLabel
    ; su2LFromSpinSectorConditionIsCanonical =
        refl
    ; su3cGapIdentified =
        false
    ; su3cGapIdentifiedIsFalse =
        refl
    ; su3cGapOpenProblem =
        openSU3cGapLabel
    ; su3cGapOpenProblemIsCanonical =
        refl
    ; u1yFromZ4Candidate =
        false
    ; u1yFromZ4CandidateIsFalse =
        refl
    ; u1yFromZ4CandidateOpenProblem =
        openU1YFromZ4Label
    ; u1yFromZ4CandidateOpenProblemIsCanonical =
        refl
    ; exactSMReconstruction =
        false
    ; exactSMReconstructionIsFalse =
        refl
    ; exactSMReconstructionBoundary =
        exactSMReconstructionFalseLabel
    ; exactSMReconstructionBoundaryIsCanonical =
        refl
    ; openProblems =
        canonicalSpinCMTensorOpenProblems
    ; openProblemsAreCanonical =
        refl
    ; receiptBoundary =
        "The physical category candidate is recorded as C_CM boxtimes Rep(SU2)"
        ∷ "The conditional DR compact-group candidate is (Z/4 x Z/6 x Z/2) x SU2"
        ∷ "su2LFromSpinSector is true only under the supplied Rep(SU2) spin-sector condition"
        ∷ "SU3c identification and U1Y-from-Z4 identification remain open"
        ∷ "Exact Standard Model reconstruction remains false"
        ∷ []
    }
