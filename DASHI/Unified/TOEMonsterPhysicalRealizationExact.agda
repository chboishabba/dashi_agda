module DASHI.Unified.TOEMonsterPhysicalRealizationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Unified.TOESectorRealizationExact
import DASHI.Unified.TOE369C3RealizationGraphExact as C3

record MonsterRecognitionFrontier : Set where
  field
    genericSimpleClassifierPaid : Bool
    genericIsotypicAssemblyPaid : Bool
    postRecognitionCopyCountPaid : Bool
    selectedCharacterFamily12Plus78Paid : Bool

    actualWeightTwoRestrictionPaid : Bool
    literalZetaRestrictionPaid : Bool
    actualSimpleClassifierInstantiationPaid : Bool
    actualWzetaIsotypicRecognitionPaid : Bool
    actualMultiplicity90Paid : Bool
    actualSzetaHomRecoveryPaid : Bool
    actualNormalizerActionPaid : Bool
    actual12Plus78ActionIntertwinerPaid : Bool

    sourceReceipt : String

currentMonsterRecognitionFrontier : MonsterRecognitionFrontier
currentMonsterRecognitionFrontier =
  record
    { genericSimpleClassifierPaid = true
    ; genericIsotypicAssemblyPaid = true
    ; postRecognitionCopyCountPaid = true
    ; selectedCharacterFamily12Plus78Paid = true
    ; actualWeightTwoRestrictionPaid = false
    ; literalZetaRestrictionPaid = false
    ; actualSimpleClassifierInstantiationPaid = false
    ; actualWzetaIsotypicRecognitionPaid = false
    ; actualMultiplicity90Paid = false
    ; actualSzetaHomRecoveryPaid = false
    ; actualNormalizerActionPaid = false
    ; actual12Plus78ActionIntertwinerPaid = false
    ; sourceReceipt =
        "Current Agda PR #1162 / companion Lean source: generic simple-source classification, generic semisimple/isotypic assembly and post-recognition copy-count are paid. The live same-object leaves are actual W_zeta restriction/classifier instantiation, W_zeta|E ~= H_zeta^n, n=90, S_zeta Hom recovery, normalizer action and the 12+78 same-action intertwiner."
    }

monsterPhysicalRealizationGrade : ValidationGrade
monsterPhysicalRealizationGrade = conjecturalStructural

monsterPhysicalObligations : List RealizationObligation
monsterPhysicalObligations =
  representationActionAgreement
  ∷ dynamicsEquivariance
  ∷ actionHamiltonianAgreement
  ∷ stressObservableAgreement
  ∷ scaleCalibrationAgreement
  ∷ empiricalSameObjectAttachment
  ∷ heldOutPredictionReceipt
  ∷ independentReplicationReceipt
  ∷ []

record MonsterPhysicalRealizationSocket : Set where
  field
    c3RepresentationEdge : C3.C3Edge
    recognitionFrontier : MonsterRecognitionFrontier
    attainedGrade : ValidationGrade
    unpaid : List RealizationObligation
    physicalStatePromotion : Bool
    physicalStatePromotionIsFalse : physicalStatePromotion ≡ false
    reading : String

canonicalMonsterPhysicalRealization : MonsterPhysicalRealizationSocket
canonicalMonsterPhysicalRealization =
  record
    { c3RepresentationEdge = C3.universalToMonsterCandidate
    ; recognitionFrontier = currentMonsterRecognitionFrontier
    ; attainedGrade = monsterPhysicalRealizationGrade
    ; unpaid = monsterPhysicalObligations
    ; physicalStatePromotion = false
    ; physicalStatePromotionIsFalse = refl
    ; reading =
        "HAM hypothesis retained: the universal physical state admits a Monster/VOA realization. Representation-level C3 structure is allowed to guide the hypothesis, but the physical lift is paid only by actual W_zeta same-action recognition followed by Hamiltonian/dynamics/action equivariance, stress/observable transport, calibration and experiment."
    }

cardinalityCannotPayPhysicalMonster :
  MonsterPhysicalRealizationSocket.physicalStatePromotion
    canonicalMonsterPhysicalRealization
  ≡ false
cardinalityCannotPayPhysicalMonster = refl
