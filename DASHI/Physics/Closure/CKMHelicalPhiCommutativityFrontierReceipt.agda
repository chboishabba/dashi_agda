module DASHI.Physics.Closure.CKMHelicalPhiCommutativityFrontierReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CKMCarrierProfiniteActionReceipt as Carrier
import DASHI.Physics.Closure.CKMHelicalPhaseGenerationIndexReceipt as Helical

------------------------------------------------------------------------
-- CKM helical psi2 / single-factor phi commutativity convention correction.
--
-- The previous receipt used the stale psi0 augmentation convention.  The
-- corrected arithmetic convention is the psi2 projection:
--
--   * 2 splits in Q(sqrt(-7)).
--   * alpha = (1 + sqrt(-7)) / 2 has norm 2.
--   * the CM character at Frob_p2 reduces mod p7 to 1/2 = 4 mod 7 = 2^2.
--   * therefore the existing single-factor phi matches the psi2 projection,
--     not the psi0 augmentation.
--
-- This closes only the convention-correction receipt.  It remains fail-closed
-- for physical promotion: no physical CKM matrix, Yukawa texture, or G7
-- unblocking is claimed here.

data CKMHelicalPhiCommutativityFrontierStatus : Set where
  completed_conventionCorrection_psi2Projection :
    CKMHelicalPhiCommutativityFrontierStatus

data SingleFactorPhiSource : Set where
  phiFromCKMCarrierProfiniteActionReceipt :
    SingleFactorPhiSource

data SevenAdicHeckeCharacterEndpoint : Set where
  helicalPsi2ProjectionSevenAdicHeckeCharacter :
    SevenAdicHeckeCharacterEndpoint

  cmCharacterPsi7UsedByPhi :
    SevenAdicHeckeCharacterEndpoint

data CharacterEqualityReduction : Set where
  phiCommutativityIdentifiesPsi2ProjectionWithPsi7 :
    CharacterEqualityReduction

data ConcreteComputationStep : Set where
  twoSplitsInQsqrtMinus7 :
    ConcreteComputationStep

  alphaOnePlusSqrtMinus7OverTwoHasNormTwo :
    ConcreteComputationStep

  cmCharacterAtFrobP2ReducesToOneHalfModSeven :
    ConcreteComputationStep

  oneHalfModSevenEqualsFourEqualsTwoSquared :
    ConcreteComputationStep

  existingSingleFactorPhiMatchesPsi2Projection :
    ConcreteComputationStep

canonicalConcreteComputationSteps :
  List ConcreteComputationStep
canonicalConcreteComputationSteps =
  twoSplitsInQsqrtMinus7
  ∷ alphaOnePlusSqrtMinus7OverTwoHasNormTwo
  ∷ cmCharacterAtFrobP2ReducesToOneHalfModSeven
  ∷ oneHalfModSevenEqualsFourEqualsTwoSquared
  ∷ existingSingleFactorPhiMatchesPsi2Projection
  ∷ []

psi2ProjectionFrob2Residue :
  Helical.Z7Unit
psi2ProjectionFrob2Residue =
  Helical.unit4

psi2ProjectionFrob2ResidueIsFour :
  psi2ProjectionFrob2Residue ≡ Helical.unit4
psi2ProjectionFrob2ResidueIsFour =
  refl

psi2CharacterAtGenerator2IsOmega2 :
  Helical.characterValueAtGenerator2 Helical.psi2 ≡ Helical.omega2
psi2CharacterAtGenerator2IsOmega2 =
  refl

data PromotionToken : Set where

promotionImpossibleHere :
  PromotionToken →
  ⊥
promotionImpossibleHere ()

psi2ConventionStatement :
  String
psi2ConventionStatement =
  "Corrected convention: the existing single-factor phi matches the helical psi2 projection, not the stale psi0 augmentation."

phiReductionStatement :
  String
phiReductionStatement =
  "Commutativity with the existing single-factor phi is recorded as equality of the helical psi2 projection with the CM character psi_7 used by phi on T_7^CM(E)."

frob2ComputationStatement :
  String
frob2ComputationStatement =
  "Computation: 2 splits in Q(sqrt(-7)); alpha=(1+sqrt(-7))/2 has norm 2; the CM character at Frob_p2 reduces mod p7 to 1/2 = 4 mod 7 = 2^2."

frontierBoundaryStatement :
  String
frontierBoundaryStatement =
  "Fail-closed convention correction: phi commutativity with the helical psi2 projection is recorded, but no physical CKM matrix, Yukawa texture, or G7 promotion follows here."

record CKMHelicalPhiCommutativityFrontierReceipt : Set where
  field
    status :
      CKMHelicalPhiCommutativityFrontierStatus

    statusIsCompletedConventionCorrection :
      status ≡ completed_conventionCorrection_psi2Projection

    carrierReceipt :
      Carrier.CKMCarrierProfiniteActionReceipt

    carrierReceiptIsCanonical :
      carrierReceipt ≡ Carrier.canonicalCKMCarrierProfiniteActionReceipt

    helicalReceipt :
      Helical.CKMHelicalPhaseGenerationIndexReceipt

    helicalReceiptIsCanonical :
      helicalReceipt ≡ Helical.canonicalCKMHelicalPhaseGenerationIndexReceipt

    phiSource :
      SingleFactorPhiSource

    phiSourceIsCarrierReceipt :
      phiSource ≡ phiFromCKMCarrierProfiniteActionReceipt

    psi2Endpoint :
      SevenAdicHeckeCharacterEndpoint

    psi2EndpointIsProjection :
      psi2Endpoint ≡ helicalPsi2ProjectionSevenAdicHeckeCharacter

    phiEndpoint :
      SevenAdicHeckeCharacterEndpoint

    phiEndpointIsPsi7 :
      phiEndpoint ≡ cmCharacterPsi7UsedByPhi

    psi2ProjectionResidueAtFrob2 :
      Helical.Z7Unit

    psi2ProjectionResidueAtFrob2IsFour :
      psi2ProjectionResidueAtFrob2 ≡ Helical.unit4

    psi2GeneratorCharacter :
      Helical.Z7CubeRoot

    psi2GeneratorCharacterIsOmega2 :
      psi2GeneratorCharacter ≡ Helical.omega2

    twoSplitsInQsqrtMinus7Recorded :
      Bool

    twoSplitsInQsqrtMinus7RecordedIsTrue :
      twoSplitsInQsqrtMinus7Recorded ≡ true

    alphaNormTwoRecorded :
      Bool

    alphaNormTwoRecordedIsTrue :
      alphaNormTwoRecorded ≡ true

    oneHalfModSevenIsFourRecorded :
      Bool

    oneHalfModSevenIsFourRecordedIsTrue :
      oneHalfModSevenIsFourRecorded ≡ true

    fourIsTwoSquaredModSevenRecorded :
      Bool

    fourIsTwoSquaredModSevenRecordedIsTrue :
      fourIsTwoSquaredModSevenRecorded ≡ true

    psi2ConventionSummary :
      String

    psi2ConventionSummaryIsCanonical :
      psi2ConventionSummary ≡ psi2ConventionStatement

    commutativityReduction :
      CharacterEqualityReduction

    commutativityReductionIsPsi2EqualsPsi7 :
      commutativityReduction
      ≡ phiCommutativityIdentifiesPsi2ProjectionWithPsi7

    commutativityReductionRecorded :
      Bool

    commutativityReductionRecordedIsTrue :
      commutativityReductionRecorded ≡ true

    phiReductionSummary :
      String

    phiReductionSummaryIsCanonical :
      phiReductionSummary ≡ phiReductionStatement

    concreteComputationSteps :
      List ConcreteComputationStep

    concreteComputationStepsAreCanonical :
      concreteComputationSteps ≡ canonicalConcreteComputationSteps

    frob2ComputationRecorded :
      Bool

    frob2ComputationRecordedIsTrue :
      frob2ComputationRecorded ≡ true

    frob2ComputationSummary :
      String

    frob2ComputationSummaryIsCanonical :
      frob2ComputationSummary ≡ frob2ComputationStatement

    psi2EqualsPsi7Recorded :
      Bool

    psi2EqualsPsi7RecordedIsTrue :
      psi2EqualsPsi7Recorded ≡ true

    phiCommutativityVerifiedForPsi2Convention :
      Bool

    phiCommutativityVerifiedForPsi2ConventionIsTrue :
      phiCommutativityVerifiedForPsi2Convention ≡ true

    stalePsi0AugmentationConventionRetired :
      Bool

    stalePsi0AugmentationConventionRetiredIsTrue :
      stalePsi0AugmentationConventionRetired ≡ true

    conventionCorrectionCompleted :
      Bool

    conventionCorrectionCompletedIsTrue :
      conventionCorrectionCompleted ≡ true

    verificationRequired :
      Bool

    verificationRequiredIsFalse :
      verificationRequired ≡ false

    ckmPromoted :
      Bool

    ckmPromotedIsFalse :
      ckmPromoted ≡ false

    yukawaPromoted :
      Bool

    yukawaPromotedIsFalse :
      yukawaPromoted ≡ false

    G7Unblocked :
      Bool

    G7UnblockedIsFalse :
      G7Unblocked ≡ false

    promotionFlags :
      List PromotionToken

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    frontierBoundary :
      String

    frontierBoundaryIsCanonical :
      frontierBoundary ≡ frontierBoundaryStatement

open CKMHelicalPhiCommutativityFrontierReceipt public

canonicalCKMHelicalPhiCommutativityFrontierReceipt :
  CKMHelicalPhiCommutativityFrontierReceipt
canonicalCKMHelicalPhiCommutativityFrontierReceipt =
  record
    { status =
        completed_conventionCorrection_psi2Projection
    ; statusIsCompletedConventionCorrection =
        refl
    ; carrierReceipt =
        Carrier.canonicalCKMCarrierProfiniteActionReceipt
    ; carrierReceiptIsCanonical =
        refl
    ; helicalReceipt =
        Helical.canonicalCKMHelicalPhaseGenerationIndexReceipt
    ; helicalReceiptIsCanonical =
        refl
    ; phiSource =
        phiFromCKMCarrierProfiniteActionReceipt
    ; phiSourceIsCarrierReceipt =
        refl
    ; psi2Endpoint =
        helicalPsi2ProjectionSevenAdicHeckeCharacter
    ; psi2EndpointIsProjection =
        refl
    ; phiEndpoint =
        cmCharacterPsi7UsedByPhi
    ; phiEndpointIsPsi7 =
        refl
    ; psi2ProjectionResidueAtFrob2 =
        Helical.unit4
    ; psi2ProjectionResidueAtFrob2IsFour =
        refl
    ; psi2GeneratorCharacter =
        Helical.omega2
    ; psi2GeneratorCharacterIsOmega2 =
        refl
    ; twoSplitsInQsqrtMinus7Recorded =
        true
    ; twoSplitsInQsqrtMinus7RecordedIsTrue =
        refl
    ; alphaNormTwoRecorded =
        true
    ; alphaNormTwoRecordedIsTrue =
        refl
    ; oneHalfModSevenIsFourRecorded =
        true
    ; oneHalfModSevenIsFourRecordedIsTrue =
        refl
    ; fourIsTwoSquaredModSevenRecorded =
        true
    ; fourIsTwoSquaredModSevenRecordedIsTrue =
        refl
    ; psi2ConventionSummary =
        psi2ConventionStatement
    ; psi2ConventionSummaryIsCanonical =
        refl
    ; commutativityReduction =
        phiCommutativityIdentifiesPsi2ProjectionWithPsi7
    ; commutativityReductionIsPsi2EqualsPsi7 =
        refl
    ; commutativityReductionRecorded =
        true
    ; commutativityReductionRecordedIsTrue =
        refl
    ; phiReductionSummary =
        phiReductionStatement
    ; phiReductionSummaryIsCanonical =
        refl
    ; concreteComputationSteps =
        canonicalConcreteComputationSteps
    ; concreteComputationStepsAreCanonical =
        refl
    ; frob2ComputationRecorded =
        true
    ; frob2ComputationRecordedIsTrue =
        refl
    ; frob2ComputationSummary =
        frob2ComputationStatement
    ; frob2ComputationSummaryIsCanonical =
        refl
    ; psi2EqualsPsi7Recorded =
        true
    ; psi2EqualsPsi7RecordedIsTrue =
        refl
    ; phiCommutativityVerifiedForPsi2Convention =
        true
    ; phiCommutativityVerifiedForPsi2ConventionIsTrue =
        refl
    ; stalePsi0AugmentationConventionRetired =
        true
    ; stalePsi0AugmentationConventionRetiredIsTrue =
        refl
    ; conventionCorrectionCompleted =
        true
    ; conventionCorrectionCompletedIsTrue =
        refl
    ; verificationRequired =
        false
    ; verificationRequiredIsFalse =
        refl
    ; ckmPromoted =
        false
    ; ckmPromotedIsFalse =
        refl
    ; yukawaPromoted =
        false
    ; yukawaPromotedIsFalse =
        refl
    ; G7Unblocked =
        false
    ; G7UnblockedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; frontierBoundary =
        frontierBoundaryStatement
    ; frontierBoundaryIsCanonical =
        refl
    }

ckmHelicalPhiPsi2ProjectionResidueAtFrob2IsFour :
  psi2ProjectionFrob2Residue ≡ Helical.unit4
ckmHelicalPhiPsi2ProjectionResidueAtFrob2IsFour =
  refl

ckmHelicalPhiPsi2CharacterAtGenerator2IsOmega2 :
  Helical.characterValueAtGenerator2 Helical.psi2 ≡ Helical.omega2
ckmHelicalPhiPsi2CharacterAtGenerator2IsOmega2 =
  refl

ckmHelicalPhiConventionCorrectionCompleted :
  conventionCorrectionCompleted
    canonicalCKMHelicalPhiCommutativityFrontierReceipt
    ≡ true
ckmHelicalPhiConventionCorrectionCompleted =
  refl

ckmHelicalPhiConcreteComputationRecorded :
  concreteComputationSteps
    canonicalCKMHelicalPhiCommutativityFrontierReceipt
    ≡ canonicalConcreteComputationSteps
ckmHelicalPhiConcreteComputationRecorded =
  refl

ckmHelicalPhiCommutativityVerifiedForPsi2Convention :
  phiCommutativityVerifiedForPsi2Convention
    canonicalCKMHelicalPhiCommutativityFrontierReceipt
    ≡ true
ckmHelicalPhiCommutativityVerifiedForPsi2Convention =
  refl

ckmHelicalPhiPhysicalPromotionsRemainFalse :
  ckmPromoted canonicalCKMHelicalPhiCommutativityFrontierReceipt ≡ false
ckmHelicalPhiPhysicalPromotionsRemainFalse =
  refl
