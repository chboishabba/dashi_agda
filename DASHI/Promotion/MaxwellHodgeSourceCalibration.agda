module DASHI.Promotion.MaxwellHodgeSourceCalibration where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Constants.Registry as Registry
import DASHI.Promotion.ClassicalFieldObligations as Classical
import DASHI.Promotion.MaxwellExteriorCalculusAdapter as Exterior

------------------------------------------------------------------------
-- Maxwell Hodge/source calibration.
--
-- The exterior-calculus adapter constructs the homogeneous side
-- F = d A and d F = 0.  This module adds the next typed calibration
-- chain: metric/orientation, Hodge star, epsilon_0/mu_0 authority,
-- charge-current extraction, continuity, and empirical observables.
-- It is intentionally fail-closed: only the symbolic carrier is
-- constructed here; Hodge/source/current/empirical promotion remain
-- blocked by authority or proof requirements.

data CalibrationStatus : Set where
  constructed : CalibrationStatus
  authorityMissing : CalibrationStatus
  proofMissing : CalibrationStatus

data CalibrationInputName : Set where
  metricOrientationInput : CalibrationInputName
  hodgeStarInput : CalibrationInputName
  epsilon0Mu0AuthorityInput : CalibrationInputName
  chargeCurrentExtractionInput : CalibrationInputName
  continuityEquationCheck : CalibrationInputName
  empiricalObservableInput : CalibrationInputName

data MaxwellCalibrationObject : Set where
  lorentzMetricOrientationObject : MaxwellCalibrationObject
  hodgeStarTwoFormObject : MaxwellCalibrationObject
  epsilon0Mu0AuthorityObject : MaxwellCalibrationObject
  chargeCurrentExtractionObject : MaxwellCalibrationObject
  continuityEquationObject : MaxwellCalibrationObject
  empiricalObservableObject : MaxwellCalibrationObject

data NextMaxwellBlocker : Set where
  nextHodgeStarAuthority : NextMaxwellBlocker
  nextEpsilon0Mu0Authority : NextMaxwellBlocker
  nextChargeCurrentExtractionProof : NextMaxwellBlocker
  nextContinuityEquationProof : NextMaxwellBlocker
  nextEmpiricalObservableAuthority : NextMaxwellBlocker
  noMaxwellCalibrationBlocker : NextMaxwellBlocker

classifyCalibrationInput :
  CalibrationInputName → CalibrationStatus
classifyCalibrationInput metricOrientationInput = constructed
classifyCalibrationInput hodgeStarInput = authorityMissing
classifyCalibrationInput epsilon0Mu0AuthorityInput = authorityMissing
classifyCalibrationInput chargeCurrentExtractionInput = proofMissing
classifyCalibrationInput continuityEquationCheck = proofMissing
classifyCalibrationInput empiricalObservableInput = authorityMissing

calibrationObject :
  CalibrationInputName → MaxwellCalibrationObject
calibrationObject metricOrientationInput =
  lorentzMetricOrientationObject
calibrationObject hodgeStarInput =
  hodgeStarTwoFormObject
calibrationObject epsilon0Mu0AuthorityInput =
  epsilon0Mu0AuthorityObject
calibrationObject chargeCurrentExtractionInput =
  chargeCurrentExtractionObject
calibrationObject continuityEquationCheck =
  continuityEquationObject
calibrationObject empiricalObservableInput =
  empiricalObservableObject

nextBlockerForInput :
  CalibrationInputName → CalibrationStatus → NextMaxwellBlocker
nextBlockerForInput metricOrientationInput constructed =
  nextHodgeStarAuthority
nextBlockerForInput metricOrientationInput authorityMissing =
  nextHodgeStarAuthority
nextBlockerForInput metricOrientationInput proofMissing =
  nextHodgeStarAuthority
nextBlockerForInput hodgeStarInput constructed =
  nextEpsilon0Mu0Authority
nextBlockerForInput hodgeStarInput authorityMissing =
  nextHodgeStarAuthority
nextBlockerForInput hodgeStarInput proofMissing =
  nextHodgeStarAuthority
nextBlockerForInput epsilon0Mu0AuthorityInput constructed =
  nextChargeCurrentExtractionProof
nextBlockerForInput epsilon0Mu0AuthorityInput authorityMissing =
  nextEpsilon0Mu0Authority
nextBlockerForInput epsilon0Mu0AuthorityInput proofMissing =
  nextEpsilon0Mu0Authority
nextBlockerForInput chargeCurrentExtractionInput constructed =
  nextContinuityEquationProof
nextBlockerForInput chargeCurrentExtractionInput authorityMissing =
  nextChargeCurrentExtractionProof
nextBlockerForInput chargeCurrentExtractionInput proofMissing =
  nextChargeCurrentExtractionProof
nextBlockerForInput continuityEquationCheck constructed =
  nextEmpiricalObservableAuthority
nextBlockerForInput continuityEquationCheck authorityMissing =
  nextContinuityEquationProof
nextBlockerForInput continuityEquationCheck proofMissing =
  nextContinuityEquationProof
nextBlockerForInput empiricalObservableInput constructed =
  noMaxwellCalibrationBlocker
nextBlockerForInput empiricalObservableInput authorityMissing =
  nextEmpiricalObservableAuthority
nextBlockerForInput empiricalObservableInput proofMissing =
  nextEmpiricalObservableAuthority

record CalibrationInputRow : Set where
  field
    inputName : CalibrationInputName
    object : MaxwellCalibrationObject
    status : CalibrationStatus
    statusMatchesClassifier :
      status ≡ classifyCalibrationInput inputName
    sourceObligation : String
    requiredToken : String
    blocksHodgeSourcePromotion : Bool
    blocksHodgeSourcePromotionProof :
      blocksHodgeSourcePromotion ≡ true
    selectedNextBlocker : NextMaxwellBlocker
    selectedNextBlockerMatches :
      selectedNextBlocker ≡ nextBlockerForInput inputName status

open CalibrationInputRow public

metricOrientationRow : CalibrationInputRow
metricOrientationRow = record
  { inputName = metricOrientationInput
  ; object = calibrationObject metricOrientationInput
  ; status = constructed
  ; statusMatchesClassifier = refl
  ; sourceObligation =
      Classical.MaxwellHodgeObligation.metricCarrierRequired
        Classical.canonicalMaxwellHodgeObligation
  ; requiredToken =
      Classical.MaxwellHodgeObligation.orientationVolumeCarrierRequired
        Classical.canonicalMaxwellHodgeObligation
  ; blocksHodgeSourcePromotion = true
  ; blocksHodgeSourcePromotionProof = refl
  ; selectedNextBlocker = nextHodgeStarAuthority
  ; selectedNextBlockerMatches = refl
  }

hodgeStarRow : CalibrationInputRow
hodgeStarRow = record
  { inputName = hodgeStarInput
  ; object = calibrationObject hodgeStarInput
  ; status = authorityMissing
  ; statusMatchesClassifier = refl
  ; sourceObligation =
      Classical.MaxwellHodgeObligation.hodgeStarOnTwoFormsRequired
        Classical.canonicalMaxwellHodgeObligation
  ; requiredToken =
      "accepted metric/orientation/Hodge-star authority token"
  ; blocksHodgeSourcePromotion = true
  ; blocksHodgeSourcePromotionProof = refl
  ; selectedNextBlocker = nextHodgeStarAuthority
  ; selectedNextBlockerMatches = refl
  }

epsilon0Mu0AuthorityRow : CalibrationInputRow
epsilon0Mu0AuthorityRow = record
  { inputName = epsilon0Mu0AuthorityInput
  ; object = calibrationObject epsilon0Mu0AuthorityInput
  ; status = authorityMissing
  ; statusMatchesClassifier = refl
  ; sourceObligation =
      Classical.MaxwellHodgeObligation.epsilon0Mu0AuthorityRequired
        Classical.canonicalMaxwellHodgeObligation
  ; requiredToken =
      "accepted CODATA epsilon_0 and mu_0 value/unit/uncertainty receipt"
  ; blocksHodgeSourcePromotion = true
  ; blocksHodgeSourcePromotionProof = refl
  ; selectedNextBlocker = nextEpsilon0Mu0Authority
  ; selectedNextBlockerMatches = refl
  }

chargeCurrentExtractionRow : CalibrationInputRow
chargeCurrentExtractionRow = record
  { inputName = chargeCurrentExtractionInput
  ; object = calibrationObject chargeCurrentExtractionInput
  ; status = proofMissing
  ; statusMatchesClassifier = refl
  ; sourceObligation =
      Classical.MaxwellSourceCurrentObligation.sourceExtractionReceiptRequired
        Classical.canonicalMaxwellSourceCurrentObligation
  ; requiredToken =
      Classical.MaxwellSourceCurrentObligation.chargeCalibrationReceiptRequired
        Classical.canonicalMaxwellSourceCurrentObligation
  ; blocksHodgeSourcePromotion = true
  ; blocksHodgeSourcePromotionProof = refl
  ; selectedNextBlocker = nextChargeCurrentExtractionProof
  ; selectedNextBlockerMatches = refl
  }

continuityEquationRow : CalibrationInputRow
continuityEquationRow = record
  { inputName = continuityEquationCheck
  ; object = calibrationObject continuityEquationCheck
  ; status = proofMissing
  ; statusMatchesClassifier = refl
  ; sourceObligation =
      Classical.MaxwellSourceCurrentObligation.continuityEquationTarget
        Classical.canonicalMaxwellSourceCurrentObligation
  ; requiredToken =
      "proof that extracted current satisfies d J = 0 in the selected convention"
  ; blocksHodgeSourcePromotion = true
  ; blocksHodgeSourcePromotionProof = refl
  ; selectedNextBlocker = nextContinuityEquationProof
  ; selectedNextBlockerMatches = refl
  }

empiricalObservableRow : CalibrationInputRow
empiricalObservableRow = record
  { inputName = empiricalObservableInput
  ; object = calibrationObject empiricalObservableInput
  ; status = authorityMissing
  ; statusMatchesClassifier = refl
  ; sourceObligation =
      Classical.MaxwellFieldEquationPromotionObligation.empiricalObservableAdapterRequired
        Classical.canonicalMaxwellFieldEquationPromotionObligation
  ; requiredToken =
      "accepted field/flux/force observable provider and calibration receipt"
  ; blocksHodgeSourcePromotion = true
  ; blocksHodgeSourcePromotionProof = refl
  ; selectedNextBlocker = nextEmpiricalObservableAuthority
  ; selectedNextBlockerMatches = refl
  }

canonicalCalibrationRows : List CalibrationInputRow
canonicalCalibrationRows =
  metricOrientationRow
  ∷ hodgeStarRow
  ∷ epsilon0Mu0AuthorityRow
  ∷ chargeCurrentExtractionRow
  ∷ continuityEquationRow
  ∷ empiricalObservableRow
  ∷ []

canonicalConstructedRows : List CalibrationInputRow
canonicalConstructedRows =
  metricOrientationRow
  ∷ []

canonicalAuthorityMissingRows : List CalibrationInputRow
canonicalAuthorityMissingRows =
  hodgeStarRow
  ∷ epsilon0Mu0AuthorityRow
  ∷ empiricalObservableRow
  ∷ []

canonicalProofMissingRows : List CalibrationInputRow
canonicalProofMissingRows =
  chargeCurrentExtractionRow
  ∷ continuityEquationRow
  ∷ []

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

record MaxwellHodgeSourceCalibration : Set₁ where
  field
    sourceExteriorAdapter :
      Exterior.MaxwellExteriorCalculusAdapter
    sourceClassicalMaxwellObligation :
      Classical.MaxwellFieldEquationPromotionObligation
    sourceHodgeObligation :
      Classical.MaxwellHodgeObligation
    sourceCurrentObligation :
      Classical.MaxwellSourceCurrentObligation
    sourcePhysicsKnownInputs :
      Registry.PhysicsAdapterKnownInputsReferenceReceipt
    calibrationRows : List CalibrationInputRow
    constructedRows : List CalibrationInputRow
    authorityMissingRows : List CalibrationInputRow
    proofMissingRows : List CalibrationInputRow
    totalCalibrationInputCount : Nat
    totalCalibrationInputCountMatches :
      totalCalibrationInputCount ≡ listLength calibrationRows
    constructedInputCount : Nat
    constructedInputCountMatches :
      constructedInputCount ≡ listLength constructedRows
    authorityMissingInputCount : Nat
    authorityMissingInputCountMatches :
      authorityMissingInputCount ≡ listLength authorityMissingRows
    proofMissingInputCount : Nat
    proofMissingInputCountMatches :
      proofMissingInputCount ≡ listLength proofMissingRows
    consumedExteriorConstructedEquationCount : Nat
    consumedExteriorConstructedEquationCountMatches :
      consumedExteriorConstructedEquationCount ≡
      Exterior.MaxwellExteriorCalculusAdapter.constructedEquationCount
        sourceExteriorAdapter
    consumedExteriorConstructedEquationCountIs1 :
      consumedExteriorConstructedEquationCount ≡ 1
    homogeneousDFZeroStatus : CalibrationStatus
    homogeneousDFZeroStatusIsConstructed :
      homogeneousDFZeroStatus ≡ constructed
    homogeneousDFZeroProof :
      Exterior.d2
        (Exterior.CanonicalCurvatureConstruction.curvature
          (Exterior.MaxwellExteriorCalculusAdapter.curvatureConstruction
            sourceExteriorAdapter))
      ≡ Exterior.zeroThreeForm
    hodgePromotion : Bool
    hodgePromotionIsFalse : hodgePromotion ≡ false
    sourceCurrentPromotion : Bool
    sourceCurrentPromotionIsFalse : sourceCurrentPromotion ≡ false
    empiricalObservablePromotion : Bool
    empiricalObservablePromotionIsFalse :
      empiricalObservablePromotion ≡ false
    sourceEquationPromotion : Bool
    sourceEquationPromotionIsFalse :
      sourceEquationPromotion ≡ false
    maxwellFieldEquationPromotion : Bool
    maxwellFieldEquationPromotionIsFalse :
      maxwellFieldEquationPromotion ≡ false
    nextBlocker : NextMaxwellBlocker
    nextBlockerIsHodgeAuthority :
      nextBlocker ≡ nextHodgeStarAuthority

open MaxwellHodgeSourceCalibration public

canonicalMaxwellHodgeSourceCalibration :
  MaxwellHodgeSourceCalibration
canonicalMaxwellHodgeSourceCalibration = record
  { sourceExteriorAdapter =
      Exterior.canonicalMaxwellExteriorCalculusAdapter
  ; sourceClassicalMaxwellObligation =
      Classical.canonicalMaxwellFieldEquationPromotionObligation
  ; sourceHodgeObligation =
      Classical.canonicalMaxwellHodgeObligation
  ; sourceCurrentObligation =
      Classical.canonicalMaxwellSourceCurrentObligation
  ; sourcePhysicsKnownInputs =
      Registry.canonicalPhysicsAdapterKnownInputsReferenceReceipt
  ; calibrationRows =
      canonicalCalibrationRows
  ; constructedRows =
      canonicalConstructedRows
  ; authorityMissingRows =
      canonicalAuthorityMissingRows
  ; proofMissingRows =
      canonicalProofMissingRows
  ; totalCalibrationInputCount =
      6
  ; totalCalibrationInputCountMatches =
      refl
  ; constructedInputCount =
      1
  ; constructedInputCountMatches =
      refl
  ; authorityMissingInputCount =
      3
  ; authorityMissingInputCountMatches =
      refl
  ; proofMissingInputCount =
      2
  ; proofMissingInputCountMatches =
      refl
  ; consumedExteriorConstructedEquationCount =
      Exterior.MaxwellExteriorCalculusAdapter.constructedEquationCount
        Exterior.canonicalMaxwellExteriorCalculusAdapter
  ; consumedExteriorConstructedEquationCountMatches =
      refl
  ; consumedExteriorConstructedEquationCountIs1 =
      refl
  ; homogeneousDFZeroStatus =
      constructed
  ; homogeneousDFZeroStatusIsConstructed =
      refl
  ; homogeneousDFZeroProof =
      refl
  ; hodgePromotion =
      Classical.MaxwellHodgeObligation.hodgeEquationPromoted
        Classical.canonicalMaxwellHodgeObligation
  ; hodgePromotionIsFalse =
      Classical.MaxwellHodgeObligation.hodgeEquationPromotedProof
        Classical.canonicalMaxwellHodgeObligation
  ; sourceCurrentPromotion =
      Classical.MaxwellSourceCurrentObligation.sourceCurrentPromoted
        Classical.canonicalMaxwellSourceCurrentObligation
  ; sourceCurrentPromotionIsFalse =
      Classical.MaxwellSourceCurrentObligation.sourceCurrentPromotedProof
        Classical.canonicalMaxwellSourceCurrentObligation
  ; empiricalObservablePromotion =
      Exterior.HodgeSourceAuthorityBoundary.empiricalObservablePromoted
        Exterior.canonicalHodgeSourceAuthorityBoundary
  ; empiricalObservablePromotionIsFalse =
      Exterior.HodgeSourceAuthorityBoundary.empiricalObservablePromotedIsFalse
        Exterior.canonicalHodgeSourceAuthorityBoundary
  ; sourceEquationPromotion =
      Exterior.MaxwellExteriorCalculusAdapter.sourceEquationPromoted
        Exterior.canonicalMaxwellExteriorCalculusAdapter
  ; sourceEquationPromotionIsFalse =
      Exterior.MaxwellExteriorCalculusAdapter.sourceEquationPromotedIsFalse
        Exterior.canonicalMaxwellExteriorCalculusAdapter
  ; maxwellFieldEquationPromotion =
      Classical.MaxwellFieldEquationPromotionObligation.maxwellFieldEquationPromoted
        Classical.canonicalMaxwellFieldEquationPromotionObligation
  ; maxwellFieldEquationPromotionIsFalse =
      Classical.MaxwellFieldEquationPromotionObligation.maxwellFieldEquationPromotedProof
        Classical.canonicalMaxwellFieldEquationPromotionObligation
  ; nextBlocker =
      nextHodgeStarAuthority
  ; nextBlockerIsHodgeAuthority =
      refl
  }

canonicalMaxwellCalibrationInputCountIs6 :
  MaxwellHodgeSourceCalibration.totalCalibrationInputCount
    canonicalMaxwellHodgeSourceCalibration
  ≡ 6
canonicalMaxwellCalibrationInputCountIs6 = refl

canonicalMaxwellCalibrationConstructedCountIs1 :
  MaxwellHodgeSourceCalibration.constructedInputCount
    canonicalMaxwellHodgeSourceCalibration
  ≡ 1
canonicalMaxwellCalibrationConstructedCountIs1 = refl

canonicalMaxwellCalibrationAuthorityMissingCountIs3 :
  MaxwellHodgeSourceCalibration.authorityMissingInputCount
    canonicalMaxwellHodgeSourceCalibration
  ≡ 3
canonicalMaxwellCalibrationAuthorityMissingCountIs3 = refl

canonicalMaxwellCalibrationProofMissingCountIs2 :
  MaxwellHodgeSourceCalibration.proofMissingInputCount
    canonicalMaxwellHodgeSourceCalibration
  ≡ 2
canonicalMaxwellCalibrationProofMissingCountIs2 = refl

canonicalMaxwellCalibrationConsumedExteriorCountIs1 :
  MaxwellHodgeSourceCalibration.consumedExteriorConstructedEquationCount
    canonicalMaxwellHodgeSourceCalibration
  ≡ 1
canonicalMaxwellCalibrationConsumedExteriorCountIs1 = refl

canonicalMaxwellCalibrationHomogeneousDFZeroConstructed :
  MaxwellHodgeSourceCalibration.homogeneousDFZeroStatus
    canonicalMaxwellHodgeSourceCalibration
  ≡ constructed
canonicalMaxwellCalibrationHomogeneousDFZeroConstructed = refl

canonicalMaxwellCalibrationHomogeneousDFZeroProof :
  Exterior.d2
    (Exterior.CanonicalCurvatureConstruction.curvature
      Exterior.canonicalCurvatureConstruction)
  ≡ Exterior.zeroThreeForm
canonicalMaxwellCalibrationHomogeneousDFZeroProof = refl

canonicalMaxwellCalibrationHodgePromotionFalse :
  MaxwellHodgeSourceCalibration.hodgePromotion
    canonicalMaxwellHodgeSourceCalibration
  ≡ false
canonicalMaxwellCalibrationHodgePromotionFalse = refl

canonicalMaxwellCalibrationSourceCurrentPromotionFalse :
  MaxwellHodgeSourceCalibration.sourceCurrentPromotion
    canonicalMaxwellHodgeSourceCalibration
  ≡ false
canonicalMaxwellCalibrationSourceCurrentPromotionFalse = refl

canonicalMaxwellCalibrationEmpiricalObservablePromotionFalse :
  MaxwellHodgeSourceCalibration.empiricalObservablePromotion
    canonicalMaxwellHodgeSourceCalibration
  ≡ false
canonicalMaxwellCalibrationEmpiricalObservablePromotionFalse = refl

canonicalMaxwellCalibrationSourceEquationPromotionFalse :
  MaxwellHodgeSourceCalibration.sourceEquationPromotion
    canonicalMaxwellHodgeSourceCalibration
  ≡ false
canonicalMaxwellCalibrationSourceEquationPromotionFalse = refl

canonicalMaxwellCalibrationFieldEquationPromotionFalse :
  MaxwellHodgeSourceCalibration.maxwellFieldEquationPromotion
    canonicalMaxwellHodgeSourceCalibration
  ≡ false
canonicalMaxwellCalibrationFieldEquationPromotionFalse = refl

canonicalMaxwellCalibrationNextBlocker :
  MaxwellHodgeSourceCalibration.nextBlocker
    canonicalMaxwellHodgeSourceCalibration
  ≡ nextHodgeStarAuthority
canonicalMaxwellCalibrationNextBlocker = refl

canonicalHodgeStarInputClassifiedAuthorityMissing :
  classifyCalibrationInput hodgeStarInput ≡ authorityMissing
canonicalHodgeStarInputClassifiedAuthorityMissing = refl

canonicalChargeCurrentInputClassifiedProofMissing :
  classifyCalibrationInput chargeCurrentExtractionInput ≡ proofMissing
canonicalChargeCurrentInputClassifiedProofMissing = refl

canonicalEmpiricalObservableInputClassifiedAuthorityMissing :
  classifyCalibrationInput empiricalObservableInput ≡ authorityMissing
canonicalEmpiricalObservableInputClassifiedAuthorityMissing = refl
