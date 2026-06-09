module DASHI.Promotion.MaxwellHodgeSourceConservationObligations where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Promotion.ClassicalFieldObligations as Classical
import DASHI.Promotion.MaxwellExteriorCalculusAdapter as Exterior
import DASHI.Promotion.MaxwellHodgeSourceCalibration as Calibration

------------------------------------------------------------------------
-- Maxwell Hodge/source-current conservation obligations.
--
-- This module is a disjoint closure surface for the inhomogeneous
-- Maxwell lane.  It records the concrete missing authority/proof
-- obligations for *F, J, d * F = J, and conservation of J.  It does not
-- promote Maxwell: every promotion guard remains false.

data ConservationObligationName : Set where
  metricAuthorityObligation : ConservationObligationName
  orientationVolumeAuthorityObligation : ConservationObligationName
  hodgeStarAuthorityObligation : ConservationObligationName
  sourceCurrentJCarrierObligation : ConservationObligationName
  inhomogeneousDStarFEqualsJObligation : ConservationObligationName
  continuityDJZeroObligation : ConservationObligationName
  divergenceJZeroObligation : ConservationObligationName
  unitChargeCalibrationObligation : ConservationObligationName
  empiricalSourceObservableObligation : ConservationObligationName
  falseMaxwellPromotionObligation : ConservationObligationName

data ConservationObligationStatus : Set where
  authorityBlocked : ConservationObligationStatus
  proofBlocked : ConservationObligationStatus
  calibrationBlocked : ConservationObligationStatus
  empiricalBlocked : ConservationObligationStatus
  promotionFalseBlocked : ConservationObligationStatus

data ConservationBlocker : Set where
  metricHodgeAuthorityBlocker : ConservationBlocker
  sourceCurrentJProofBlocker : ConservationBlocker
  inhomogeneousEquationProofBlocker : ConservationBlocker
  sourceConservationProofBlocker : ConservationBlocker
  unitCalibrationAuthorityBlocker : ConservationBlocker
  empiricalCalibrationAuthorityBlocker : ConservationBlocker
  maxwellPromotionFalseBlocker : ConservationBlocker

classifyConservationObligation :
  ConservationObligationName → ConservationObligationStatus
classifyConservationObligation metricAuthorityObligation =
  authorityBlocked
classifyConservationObligation orientationVolumeAuthorityObligation =
  authorityBlocked
classifyConservationObligation hodgeStarAuthorityObligation =
  authorityBlocked
classifyConservationObligation sourceCurrentJCarrierObligation =
  proofBlocked
classifyConservationObligation inhomogeneousDStarFEqualsJObligation =
  proofBlocked
classifyConservationObligation continuityDJZeroObligation =
  proofBlocked
classifyConservationObligation divergenceJZeroObligation =
  proofBlocked
classifyConservationObligation unitChargeCalibrationObligation =
  calibrationBlocked
classifyConservationObligation empiricalSourceObservableObligation =
  empiricalBlocked
classifyConservationObligation falseMaxwellPromotionObligation =
  promotionFalseBlocked

blockerForConservationObligation :
  ConservationObligationName → ConservationBlocker
blockerForConservationObligation metricAuthorityObligation =
  metricHodgeAuthorityBlocker
blockerForConservationObligation orientationVolumeAuthorityObligation =
  metricHodgeAuthorityBlocker
blockerForConservationObligation hodgeStarAuthorityObligation =
  metricHodgeAuthorityBlocker
blockerForConservationObligation sourceCurrentJCarrierObligation =
  sourceCurrentJProofBlocker
blockerForConservationObligation inhomogeneousDStarFEqualsJObligation =
  inhomogeneousEquationProofBlocker
blockerForConservationObligation continuityDJZeroObligation =
  sourceConservationProofBlocker
blockerForConservationObligation divergenceJZeroObligation =
  sourceConservationProofBlocker
blockerForConservationObligation unitChargeCalibrationObligation =
  unitCalibrationAuthorityBlocker
blockerForConservationObligation empiricalSourceObservableObligation =
  empiricalCalibrationAuthorityBlocker
blockerForConservationObligation falseMaxwellPromotionObligation =
  maxwellPromotionFalseBlocker

record ConservationObligationRow : Set where
  field
    obligationName : ConservationObligationName
    status : ConservationObligationStatus
    statusMatchesClassifier :
      status ≡ classifyConservationObligation obligationName
    targetStatement : String
    requiredReceipt : String
    selectedBlocker : ConservationBlocker
    selectedBlockerMatches :
      selectedBlocker ≡
      blockerForConservationObligation obligationName
    blocksMaxwellPromotion : Bool
    blocksMaxwellPromotionProof :
      blocksMaxwellPromotion ≡ true

open ConservationObligationRow public

metricAuthorityRow : ConservationObligationRow
metricAuthorityRow = record
  { obligationName = metricAuthorityObligation
  ; status = authorityBlocked
  ; statusMatchesClassifier = refl
  ; targetStatement =
      "metric authority for Hodge star and codifferential"
  ; requiredReceipt =
      Classical.MaxwellHodgeObligation.metricCarrierRequired
        Classical.canonicalMaxwellHodgeObligation
  ; selectedBlocker = metricHodgeAuthorityBlocker
  ; selectedBlockerMatches = refl
  ; blocksMaxwellPromotion = true
  ; blocksMaxwellPromotionProof = refl
  }

orientationVolumeAuthorityRow : ConservationObligationRow
orientationVolumeAuthorityRow = record
  { obligationName = orientationVolumeAuthorityObligation
  ; status = authorityBlocked
  ; statusMatchesClassifier = refl
  ; targetStatement =
      "orientation and volume-form authority for Hodge convention"
  ; requiredReceipt =
      Classical.MaxwellHodgeObligation.orientationVolumeCarrierRequired
        Classical.canonicalMaxwellHodgeObligation
  ; selectedBlocker = metricHodgeAuthorityBlocker
  ; selectedBlockerMatches = refl
  ; blocksMaxwellPromotion = true
  ; blocksMaxwellPromotionProof = refl
  }

hodgeStarAuthorityRow : ConservationObligationRow
hodgeStarAuthorityRow = record
  { obligationName = hodgeStarAuthorityObligation
  ; status = authorityBlocked
  ; statusMatchesClassifier = refl
  ; targetStatement =
      "* F : two-form to two-form under selected metric convention"
  ; requiredReceipt =
      Classical.MaxwellHodgeObligation.hodgeStarOnTwoFormsRequired
        Classical.canonicalMaxwellHodgeObligation
  ; selectedBlocker = metricHodgeAuthorityBlocker
  ; selectedBlockerMatches = refl
  ; blocksMaxwellPromotion = true
  ; blocksMaxwellPromotionProof = refl
  }

sourceCurrentJCarrierRow : ConservationObligationRow
sourceCurrentJCarrierRow = record
  { obligationName = sourceCurrentJCarrierObligation
  ; status = proofBlocked
  ; statusMatchesClassifier = refl
  ; targetStatement =
      "J : source-current three-form extracted from charged matter"
  ; requiredReceipt =
      Classical.MaxwellSourceCurrentObligation.sourceExtractionReceiptRequired
        Classical.canonicalMaxwellSourceCurrentObligation
  ; selectedBlocker = sourceCurrentJProofBlocker
  ; selectedBlockerMatches = refl
  ; blocksMaxwellPromotion = true
  ; blocksMaxwellPromotionProof = refl
  }

inhomogeneousDStarFEqualsJRow : ConservationObligationRow
inhomogeneousDStarFEqualsJRow = record
  { obligationName = inhomogeneousDStarFEqualsJObligation
  ; status = proofBlocked
  ; statusMatchesClassifier = refl
  ; targetStatement =
      Classical.MaxwellFieldEquationPromotionObligation.inhomogeneousEquationTarget
        Classical.canonicalMaxwellFieldEquationPromotionObligation
  ; requiredReceipt =
      "proof or accepted authority receipt identifying d * F with J"
  ; selectedBlocker = inhomogeneousEquationProofBlocker
  ; selectedBlockerMatches = refl
  ; blocksMaxwellPromotion = true
  ; blocksMaxwellPromotionProof = refl
  }

continuityDJZeroRow : ConservationObligationRow
continuityDJZeroRow = record
  { obligationName = continuityDJZeroObligation
  ; status = proofBlocked
  ; statusMatchesClassifier = refl
  ; targetStatement =
      "d J = 0"
  ; requiredReceipt =
      Classical.MaxwellSourceCurrentObligation.continuityEquationTarget
        Classical.canonicalMaxwellSourceCurrentObligation
  ; selectedBlocker = sourceConservationProofBlocker
  ; selectedBlockerMatches = refl
  ; blocksMaxwellPromotion = true
  ; blocksMaxwellPromotionProof = refl
  }

divergenceJZeroRow : ConservationObligationRow
divergenceJZeroRow = record
  { obligationName = divergenceJZeroObligation
  ; status = proofBlocked
  ; statusMatchesClassifier = refl
  ; targetStatement =
      "div J = 0 / partial_mu J^mu = 0"
  ; requiredReceipt =
      "proof that the vector-current convention agrees with d J = 0"
  ; selectedBlocker = sourceConservationProofBlocker
  ; selectedBlockerMatches = refl
  ; blocksMaxwellPromotion = true
  ; blocksMaxwellPromotionProof = refl
  }

unitChargeCalibrationRow : ConservationObligationRow
unitChargeCalibrationRow = record
  { obligationName = unitChargeCalibrationObligation
  ; status = calibrationBlocked
  ; statusMatchesClassifier = refl
  ; targetStatement =
      "SI unit, epsilon_0/mu_0, and charge-current calibration binding"
  ; requiredReceipt =
      Classical.MaxwellSourceCurrentObligation.chargeCalibrationReceiptRequired
        Classical.canonicalMaxwellSourceCurrentObligation
  ; selectedBlocker = unitCalibrationAuthorityBlocker
  ; selectedBlockerMatches = refl
  ; blocksMaxwellPromotion = true
  ; blocksMaxwellPromotionProof = refl
  }

empiricalSourceObservableRow : ConservationObligationRow
empiricalSourceObservableRow = record
  { obligationName = empiricalSourceObservableObligation
  ; status = empiricalBlocked
  ; statusMatchesClassifier = refl
  ; targetStatement =
      "empirical source/field observable map for Maxwell comparison"
  ; requiredReceipt =
      Classical.MaxwellFieldEquationPromotionObligation.empiricalObservableAdapterRequired
        Classical.canonicalMaxwellFieldEquationPromotionObligation
  ; selectedBlocker = empiricalCalibrationAuthorityBlocker
  ; selectedBlockerMatches = refl
  ; blocksMaxwellPromotion = true
  ; blocksMaxwellPromotionProof = refl
  }

falseMaxwellPromotionRow : ConservationObligationRow
falseMaxwellPromotionRow = record
  { obligationName = falseMaxwellPromotionObligation
  ; status = promotionFalseBlocked
  ; statusMatchesClassifier = refl
  ; targetStatement =
      "Maxwell field-equation promotion remains false"
  ; requiredReceipt =
      "all Hodge, source-current, continuity, unit, and empirical blockers closed"
  ; selectedBlocker = maxwellPromotionFalseBlocker
  ; selectedBlockerMatches = refl
  ; blocksMaxwellPromotion = true
  ; blocksMaxwellPromotionProof = refl
  }

canonicalConservationRows : List ConservationObligationRow
canonicalConservationRows =
  metricAuthorityRow
  ∷ orientationVolumeAuthorityRow
  ∷ hodgeStarAuthorityRow
  ∷ sourceCurrentJCarrierRow
  ∷ inhomogeneousDStarFEqualsJRow
  ∷ continuityDJZeroRow
  ∷ divergenceJZeroRow
  ∷ unitChargeCalibrationRow
  ∷ empiricalSourceObservableRow
  ∷ falseMaxwellPromotionRow
  ∷ []

canonicalAuthorityBlockedRows : List ConservationObligationRow
canonicalAuthorityBlockedRows =
  metricAuthorityRow
  ∷ orientationVolumeAuthorityRow
  ∷ hodgeStarAuthorityRow
  ∷ []

canonicalProofBlockedRows : List ConservationObligationRow
canonicalProofBlockedRows =
  sourceCurrentJCarrierRow
  ∷ inhomogeneousDStarFEqualsJRow
  ∷ continuityDJZeroRow
  ∷ divergenceJZeroRow
  ∷ []

canonicalCalibrationBlockedRows : List ConservationObligationRow
canonicalCalibrationBlockedRows =
  unitChargeCalibrationRow
  ∷ []

canonicalEmpiricalBlockedRows : List ConservationObligationRow
canonicalEmpiricalBlockedRows =
  empiricalSourceObservableRow
  ∷ []

canonicalPromotionFalseRows : List ConservationObligationRow
canonicalPromotionFalseRows =
  falseMaxwellPromotionRow
  ∷ []

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

record MaxwellHodgeSourceConservationClosure : Set₁ where
  field
    sourceExteriorAdapter :
      Exterior.MaxwellExteriorCalculusAdapter
    sourceCalibration :
      Calibration.MaxwellHodgeSourceCalibration
    sourceClassicalMaxwellObligation :
      Classical.MaxwellFieldEquationPromotionObligation
    symbolicF : Exterior.TwoForm
    symbolicStarF : Exterior.TwoForm
    symbolicDStarF : Exterior.ThreeForm
    sourceCurrentJ : Exterior.ThreeForm
    continuityDJO : Exterior.FourForm
    inhomogeneousEquationTarget : String
    continuityEquationTarget : String
    divergenceEquationTarget : String
    rows : List ConservationObligationRow
    authorityBlockedRows : List ConservationObligationRow
    proofBlockedRows : List ConservationObligationRow
    calibrationBlockedRows : List ConservationObligationRow
    empiricalBlockedRows : List ConservationObligationRow
    promotionFalseRows : List ConservationObligationRow
    totalObligationCount : Nat
    totalObligationCountMatches :
      totalObligationCount ≡ listLength rows
    authorityBlockedCount : Nat
    authorityBlockedCountMatches :
      authorityBlockedCount ≡ listLength authorityBlockedRows
    proofBlockedCount : Nat
    proofBlockedCountMatches :
      proofBlockedCount ≡ listLength proofBlockedRows
    calibrationBlockedCount : Nat
    calibrationBlockedCountMatches :
      calibrationBlockedCount ≡ listLength calibrationBlockedRows
    empiricalBlockedCount : Nat
    empiricalBlockedCountMatches :
      empiricalBlockedCount ≡ listLength empiricalBlockedRows
    promotionFalseCount : Nat
    promotionFalseCountMatches :
      promotionFalseCount ≡ listLength promotionFalseRows
    sourceCurrentJIsCanonical :
      sourceCurrentJ ≡ Exterior.sourceCurrentThreeForm
    symbolicStarFIsAdapterHodgeTarget :
      symbolicStarF ≡
      Exterior.HodgeSourceAuthorityBoundary.symbolicHodgeTarget
        Exterior.canonicalHodgeSourceAuthorityBoundary
    symbolicDStarFIsAdapterBoundary :
      symbolicDStarF ≡
      Exterior.HodgeSourceAuthorityBoundary.symbolicDStarF
        Exterior.canonicalHodgeSourceAuthorityBoundary
    continuityDJOIsDSourceCurrent :
      continuityDJO ≡ Exterior.d3 sourceCurrentJ
    inhomogeneousTargetConnected :
      inhomogeneousEquationTarget ≡ "d * F = J"
    continuityTargetConnected :
      continuityEquationTarget ≡
      Classical.MaxwellSourceCurrentObligation.continuityEquationTarget
        Classical.canonicalMaxwellSourceCurrentObligation
    homogeneousOnlyConstructedCount : Nat
    homogeneousOnlyConstructedCountIs1 :
      homogeneousOnlyConstructedCount ≡ 1
    hodgePromotion : Bool
    hodgePromotionIsFalse : hodgePromotion ≡ false
    sourceCurrentPromotion : Bool
    sourceCurrentPromotionIsFalse :
      sourceCurrentPromotion ≡ false
    sourceEquationPromotion : Bool
    sourceEquationPromotionIsFalse :
      sourceEquationPromotion ≡ false
    conservationPromotion : Bool
    conservationPromotionIsFalse :
      conservationPromotion ≡ false
    maxwellFieldEquationPromotion : Bool
    maxwellFieldEquationPromotionIsFalse :
      maxwellFieldEquationPromotion ≡ false

open MaxwellHodgeSourceConservationClosure public

canonicalMaxwellHodgeSourceConservationClosure :
  MaxwellHodgeSourceConservationClosure
canonicalMaxwellHodgeSourceConservationClosure = record
  { sourceExteriorAdapter =
      Exterior.canonicalMaxwellExteriorCalculusAdapter
  ; sourceCalibration =
      Calibration.canonicalMaxwellHodgeSourceCalibration
  ; sourceClassicalMaxwellObligation =
      Classical.canonicalMaxwellFieldEquationPromotionObligation
  ; symbolicF =
      Exterior.canonicalCurvatureTwoForm
  ; symbolicStarF =
      Exterior.hodge2Symbolic Exterior.canonicalCurvatureTwoForm
  ; symbolicDStarF =
      Exterior.d2
        (Exterior.hodge2Symbolic Exterior.canonicalCurvatureTwoForm)
  ; sourceCurrentJ =
      Exterior.sourceCurrentThreeForm
  ; continuityDJO =
      Exterior.d3 Exterior.sourceCurrentThreeForm
  ; inhomogeneousEquationTarget =
      Classical.MaxwellFieldEquationPromotionObligation.inhomogeneousEquationTarget
        Classical.canonicalMaxwellFieldEquationPromotionObligation
  ; continuityEquationTarget =
      Classical.MaxwellSourceCurrentObligation.continuityEquationTarget
        Classical.canonicalMaxwellSourceCurrentObligation
  ; divergenceEquationTarget =
      "div J = 0 / partial_mu J^mu = 0"
  ; rows =
      canonicalConservationRows
  ; authorityBlockedRows =
      canonicalAuthorityBlockedRows
  ; proofBlockedRows =
      canonicalProofBlockedRows
  ; calibrationBlockedRows =
      canonicalCalibrationBlockedRows
  ; empiricalBlockedRows =
      canonicalEmpiricalBlockedRows
  ; promotionFalseRows =
      canonicalPromotionFalseRows
  ; totalObligationCount =
      10
  ; totalObligationCountMatches =
      refl
  ; authorityBlockedCount =
      3
  ; authorityBlockedCountMatches =
      refl
  ; proofBlockedCount =
      4
  ; proofBlockedCountMatches =
      refl
  ; calibrationBlockedCount =
      1
  ; calibrationBlockedCountMatches =
      refl
  ; empiricalBlockedCount =
      1
  ; empiricalBlockedCountMatches =
      refl
  ; promotionFalseCount =
      1
  ; promotionFalseCountMatches =
      refl
  ; sourceCurrentJIsCanonical =
      refl
  ; symbolicStarFIsAdapterHodgeTarget =
      refl
  ; symbolicDStarFIsAdapterBoundary =
      refl
  ; continuityDJOIsDSourceCurrent =
      refl
  ; inhomogeneousTargetConnected =
      refl
  ; continuityTargetConnected =
      refl
  ; homogeneousOnlyConstructedCount =
      Exterior.MaxwellExteriorCalculusAdapter.constructedEquationCount
        Exterior.canonicalMaxwellExteriorCalculusAdapter
  ; homogeneousOnlyConstructedCountIs1 =
      refl
  ; hodgePromotion =
      Calibration.MaxwellHodgeSourceCalibration.hodgePromotion
        Calibration.canonicalMaxwellHodgeSourceCalibration
  ; hodgePromotionIsFalse =
      Calibration.MaxwellHodgeSourceCalibration.hodgePromotionIsFalse
        Calibration.canonicalMaxwellHodgeSourceCalibration
  ; sourceCurrentPromotion =
      Calibration.MaxwellHodgeSourceCalibration.sourceCurrentPromotion
        Calibration.canonicalMaxwellHodgeSourceCalibration
  ; sourceCurrentPromotionIsFalse =
      Calibration.MaxwellHodgeSourceCalibration.sourceCurrentPromotionIsFalse
        Calibration.canonicalMaxwellHodgeSourceCalibration
  ; sourceEquationPromotion =
      Calibration.MaxwellHodgeSourceCalibration.sourceEquationPromotion
        Calibration.canonicalMaxwellHodgeSourceCalibration
  ; sourceEquationPromotionIsFalse =
      Calibration.MaxwellHodgeSourceCalibration.sourceEquationPromotionIsFalse
        Calibration.canonicalMaxwellHodgeSourceCalibration
  ; conservationPromotion =
      false
  ; conservationPromotionIsFalse =
      refl
  ; maxwellFieldEquationPromotion =
      Classical.MaxwellFieldEquationPromotionObligation.maxwellFieldEquationPromoted
        Classical.canonicalMaxwellFieldEquationPromotionObligation
  ; maxwellFieldEquationPromotionIsFalse =
      Classical.MaxwellFieldEquationPromotionObligation.maxwellFieldEquationPromotedProof
        Classical.canonicalMaxwellFieldEquationPromotionObligation
  }

canonicalConservationObligationCountIs10 :
  MaxwellHodgeSourceConservationClosure.totalObligationCount
    canonicalMaxwellHodgeSourceConservationClosure
  ≡ 10
canonicalConservationObligationCountIs10 = refl

canonicalConservationAuthorityBlockedCountIs3 :
  MaxwellHodgeSourceConservationClosure.authorityBlockedCount
    canonicalMaxwellHodgeSourceConservationClosure
  ≡ 3
canonicalConservationAuthorityBlockedCountIs3 = refl

canonicalConservationProofBlockedCountIs4 :
  MaxwellHodgeSourceConservationClosure.proofBlockedCount
    canonicalMaxwellHodgeSourceConservationClosure
  ≡ 4
canonicalConservationProofBlockedCountIs4 = refl

canonicalConservationCalibrationBlockedCountIs1 :
  MaxwellHodgeSourceConservationClosure.calibrationBlockedCount
    canonicalMaxwellHodgeSourceConservationClosure
  ≡ 1
canonicalConservationCalibrationBlockedCountIs1 = refl

canonicalConservationEmpiricalBlockedCountIs1 :
  MaxwellHodgeSourceConservationClosure.empiricalBlockedCount
    canonicalMaxwellHodgeSourceConservationClosure
  ≡ 1
canonicalConservationEmpiricalBlockedCountIs1 = refl

canonicalConservationPromotionFalseCountIs1 :
  MaxwellHodgeSourceConservationClosure.promotionFalseCount
    canonicalMaxwellHodgeSourceConservationClosure
  ≡ 1
canonicalConservationPromotionFalseCountIs1 = refl

canonicalSourceCurrentJIsSourceCurrentThreeForm :
  MaxwellHodgeSourceConservationClosure.sourceCurrentJ
    canonicalMaxwellHodgeSourceConservationClosure
  ≡ Exterior.sourceCurrentThreeForm
canonicalSourceCurrentJIsSourceCurrentThreeForm = refl

canonicalDStarFIsUnverified :
  MaxwellHodgeSourceConservationClosure.symbolicDStarF
    canonicalMaxwellHodgeSourceConservationClosure
  ≡ Exterior.unverifiedDStarFThreeForm
canonicalDStarFIsUnverified = refl

canonicalContinuityDJOIsContinuityFourForm :
  MaxwellHodgeSourceConservationClosure.continuityDJO
    canonicalMaxwellHodgeSourceConservationClosure
  ≡ Exterior.continuityFourForm
canonicalContinuityDJOIsContinuityFourForm = refl

canonicalContinuityTargetIsClassicalTarget :
  MaxwellHodgeSourceConservationClosure.continuityEquationTarget
    canonicalMaxwellHodgeSourceConservationClosure
  ≡
  Classical.MaxwellSourceCurrentObligation.continuityEquationTarget
    Classical.canonicalMaxwellSourceCurrentObligation
canonicalContinuityTargetIsClassicalTarget = refl

canonicalHomogeneousOnlyConstructedCountIs1 :
  MaxwellHodgeSourceConservationClosure.homogeneousOnlyConstructedCount
    canonicalMaxwellHodgeSourceConservationClosure
  ≡ 1
canonicalHomogeneousOnlyConstructedCountIs1 = refl

canonicalConservationHodgePromotionFalse :
  MaxwellHodgeSourceConservationClosure.hodgePromotion
    canonicalMaxwellHodgeSourceConservationClosure
  ≡ false
canonicalConservationHodgePromotionFalse = refl

canonicalConservationSourceCurrentPromotionFalse :
  MaxwellHodgeSourceConservationClosure.sourceCurrentPromotion
    canonicalMaxwellHodgeSourceConservationClosure
  ≡ false
canonicalConservationSourceCurrentPromotionFalse = refl

canonicalConservationSourceEquationPromotionFalse :
  MaxwellHodgeSourceConservationClosure.sourceEquationPromotion
    canonicalMaxwellHodgeSourceConservationClosure
  ≡ false
canonicalConservationSourceEquationPromotionFalse = refl

canonicalConservationPromotionFalse :
  MaxwellHodgeSourceConservationClosure.conservationPromotion
    canonicalMaxwellHodgeSourceConservationClosure
  ≡ false
canonicalConservationPromotionFalse = refl

canonicalConservationMaxwellFieldEquationPromotionFalse :
  MaxwellHodgeSourceConservationClosure.maxwellFieldEquationPromotion
    canonicalMaxwellHodgeSourceConservationClosure
  ≡ false
canonicalConservationMaxwellFieldEquationPromotionFalse = refl
