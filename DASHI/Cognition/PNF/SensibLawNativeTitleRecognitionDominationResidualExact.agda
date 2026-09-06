module DASHI.Cognition.PNF.SensibLawNativeTitleRecognitionDominationResidualExact where

------------------------------------------------------------------------
-- NATIVE TITLE RECOGNITION / DOMINATION RESIDUAL
--
-- This owner does not declare Native Title legally invalid. It represents the
-- stronger critical question: what power relation survives after the doctrinal
-- correction? Court/statute propositions and critical interpretations remain
-- separately sourced in the companion atlas.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawNativeTitleRecognitionCriticalSourceAtlasExact as Sources
import DASHI.Cognition.PNF.SensibLawMaboTwoLegalOrderFibreExact as TwoOrder
import DASHI.Cognition.PNF.SensibLawMaboColonialSovereigntyCriticalResidualExact as Critical
import DASHI.Governance.NormativeCorrectionMaterialPersistenceExact as Persistence

------------------------------------------------------------------------
-- Coordinate factorisation.
------------------------------------------------------------------------

data NativeTitleRelationCoordinate : Set where
  antecedentIndigenousOrderExists
  commonLawRecognitionCondition
  crownSovereigntyPremise
  crownRadicalTitleArchitecture
  crownExtinguishmentPower
  statutoryFutureActValidation
  indigenousCessionStatus
  equalSovereignStanding
  landReturn
  materialRepair
  institutionalRelationTransformation
  : NativeTitleRelationCoordinate

data CoordinateState : Set where
  sourceBackedPresent
  sourceBackedAbsent
  criticalResidualOpen
  worldTruthUnresolved
  : CoordinateState

nativeTitleCoordinateState : NativeTitleRelationCoordinate → CoordinateState
nativeTitleCoordinateState antecedentIndigenousOrderExists = sourceBackedPresent
nativeTitleCoordinateState commonLawRecognitionCondition = sourceBackedPresent
nativeTitleCoordinateState crownSovereigntyPremise = sourceBackedPresent
nativeTitleCoordinateState crownRadicalTitleArchitecture = sourceBackedPresent
nativeTitleCoordinateState crownExtinguishmentPower = sourceBackedPresent
nativeTitleCoordinateState statutoryFutureActValidation = sourceBackedPresent
nativeTitleCoordinateState indigenousCessionStatus = worldTruthUnresolved
nativeTitleCoordinateState equalSovereignStanding = criticalResidualOpen
nativeTitleCoordinateState landReturn = criticalResidualOpen
nativeTitleCoordinateState materialRepair = criticalResidualOpen
nativeTitleCoordinateState institutionalRelationTransformation = criticalResidualOpen

cessionWorldTruthRemainsUnresolved :
  nativeTitleCoordinateState indigenousCessionStatus ≡ worldTruthUnresolved
cessionWorldTruthRemainsUnresolved = refl

------------------------------------------------------------------------
-- Attributed no-cession position is positive evidence of a POSITION, without
-- collapsing the world-state cession coordinate.
------------------------------------------------------------------------

record AttributedNonCessionPosition : Set where
  constructor attributed-non-cession-position
  field
    sourceReceipt : Sources.LayeredClaimReceipt
    isIndigenousSovereignPosition :
      Sources.layer sourceReceipt ≡ Sources.indigenousSovereignPosition
    positionDirectlySourced : Sources.sourceSaysThisDirectly sourceReceipt ≡ true
    municipalHoldingCreated : Bool
    municipalHoldingCreatedIsFalse : municipalHoldingCreated ≡ false
    cessionWorldTruthClosedByCitation : Bool
    cessionWorldTruthClosedByCitationIsFalse : cessionWorldTruthClosedByCitation ≡ false

open AttributedNonCessionPosition public

watsonCoeNonCessionReceipt : AttributedNonCessionPosition
watsonCoeNonCessionReceipt = attributed-non-cession-position
  Sources.watsonCoeNeverCededPosition
  refl
  refl
  false refl
  false refl

------------------------------------------------------------------------
-- Native Title can be both a major legal correction and an incomplete change
-- in the underlying relation.
------------------------------------------------------------------------

record NativeTitleInstitutionalRelationState : Set where
  constructor native-title-institutional-relation-state
  field
    doctrinalAdvance : Bool
    doctrinalAdvanceIsTrue : doctrinalAdvance ≡ true
    enlargedTerraNulliusRejected : Bool
    enlargedTerraNulliusRejectedIsTrue : enlargedTerraNulliusRejected ≡ true
    antecedentIndigenousOrderCreatedByRecognition : Bool
    antecedentIndigenousOrderCreatedByRecognitionIsFalse :
      antecedentIndigenousOrderCreatedByRecognition ≡ false
    recognitionConditionedByCommonLaw : Bool
    recognitionConditionedByCommonLawIsTrue : recognitionConditionedByCommonLaw ≡ true
    crownSovereigntyPremiseDisplaced : Bool
    crownSovereigntyPremiseDisplacedIsFalse : crownSovereigntyPremiseDisplaced ≡ false
    crownRadicalTitleArchitectureDisplaced : Bool
    crownRadicalTitleArchitectureDisplacedIsFalse :
      crownRadicalTitleArchitectureDisplaced ≡ false
    crownExtinguishmentPowerAbolished : Bool
    crownExtinguishmentPowerAbolishedIsFalse : crownExtinguishmentPowerAbolished ≡ false
    indigenousCessionProved : Bool
    indigenousCessionProvedIsFalse : indigenousCessionProved ≡ false
    equalSovereignRelationCreated : Bool
    equalSovereignRelationCreatedIsFalse : equalSovereignRelationCreated ≡ false
    landReturnCompleted : Bool
    landReturnCompletedIsFalse : landReturnCompleted ≡ false
    materialRepairCompleted : Bool
    materialRepairCompletedIsFalse : materialRepairCompleted ≡ false
    relationTransformationCompleted : Bool
    relationTransformationCompletedIsFalse : relationTransformationCompleted ≡ false
    criticalCharacterisation : String
    criticalCharacterisationIsCourtHolding : Bool
    criticalCharacterisationIsCourtHoldingIsFalse :
      criticalCharacterisationIsCourtHolding ≡ false

open NativeTitleInstitutionalRelationState public

currentNativeTitleInstitutionalRelationState : NativeTitleInstitutionalRelationState
currentNativeTitleInstitutionalRelationState = native-title-institutional-relation-state
  true refl
  true refl
  false refl
  true refl
  false refl
  false refl
  false refl
  false refl
  false refl
  false refl
  false refl
  false refl
  "DASHI/SensibLaw critical synthesis: a major doctrinal correction can coexist with a Crown-mediated recognition relation in which Crown sovereignty, radical title, extinguishment capacity and common-law legibility remain structurally privileged"
  false refl

------------------------------------------------------------------------
-- Existing owners pin the non-creation and non-repair sides.
------------------------------------------------------------------------

recognitionDoesNotCreateIndigenousOrder :
  TwoOrder.externalRecognitionCreatesOrder TwoOrder.indigenousOrderFibre ≡ false
recognitionDoesNotCreateIndigenousOrder = refl

nativeTitleRecognitionDoesNotProveSovereigntyRecognition :
  Critical.NativeTitleRecognitionProvesSovereigntyRecognition → ⊥
nativeTitleRecognitionDoesNotProveSovereigntyRecognition =
  Critical.nativeTitleDoesNotProveSovereigntyRecognition

nativeTitleRecognitionDoesNotRepairDispossession :
  Critical.NativeTitleRecognitionRepairsDispossession → ⊥
nativeTitleRecognitionDoesNotRepairDispossession =
  Critical.nativeTitleDoesNotRepairDispossessionByItself

maboCorrectionDoesNotEqualCompleteRepair :
  Persistence.legalCorrectionEqualsCompleteRepair
    Persistence.canonicalNormativeCorrectionMaterialPersistenceBoundary ≡ false
maboCorrectionDoesNotEqualCompleteRepair = refl

------------------------------------------------------------------------
-- Source-specific critical lenses remain source-owned.
------------------------------------------------------------------------

data RecognitionCriticalLens : Set where
  coulthardColonialRecognitionLens
  povinelliAuthenticityLegibilityLens
  moretonRobinsonPossessiveSovereigntyLens
  nicholsRecursiveDispossessionLens
  sensibLawInfantilisationLens
  : RecognitionCriticalLens

record RecognitionLensReceipt : Set where
  constructor recognition-lens-receipt
  field
    lens : RecognitionCriticalLens
    source : Sources.LayeredClaimReceipt
    sourceLayer : Sources.ClaimLayer
    sourceLayerMatches : Sources.layer source ≡ sourceLayer
    exactCombinedConclusionAuthoredBySource : Bool
    exactCombinedConclusionAuthoredBySourceIsFalse :
      exactCombinedConclusionAuthoredBySource ≡ false
    worldTruthAutomaticallyProved : Bool
    worldTruthAutomaticallyProvedIsFalse : worldTruthAutomaticallyProved ≡ false

open RecognitionLensReceipt public

coulthardLensReceipt : RecognitionLensReceipt
coulthardLensReceipt = recognition-lens-receipt
  coulthardColonialRecognitionLens
  Sources.coulthardRecognitionPowerArgument
  Sources.sourceCriticalTheory refl
  false refl false refl

povinelliLensReceipt : RecognitionLensReceipt
povinelliLensReceipt = recognition-lens-receipt
  povinelliAuthenticityLegibilityLens
  Sources.povinelliCunningRecognitionArgument
  Sources.sourceAnthropologicalTheory refl
  false refl false refl

moretonRobinsonLensReceipt : RecognitionLensReceipt
moretonRobinsonLensReceipt = recognition-lens-receipt
  moretonRobinsonPossessiveSovereigntyLens
  Sources.moretonRobinsonPossessiveWhiteSovereigntyArgument
  Sources.sourceCriticalTheory refl
  false refl false refl

nicholsLensReceipt : RecognitionLensReceipt
nicholsLensReceipt = recognition-lens-receipt
  nicholsRecursiveDispossessionLens
  Sources.nicholsRecursiveDispossessionArgument
  Sources.sourceCriticalTheory refl
  false refl false refl

sensibLawInfantilisationReceipt : RecognitionLensReceipt
sensibLawInfantilisationReceipt = recognition-lens-receipt
  sensibLawInfantilisationLens
  Sources.nativeTitleInfantilisationCriticalSynthesis
  Sources.dashCriticalSynthesis refl
  false refl false refl

------------------------------------------------------------------------
-- The strict critical conclusion.
------------------------------------------------------------------------

record NativeTitleCriticalBoundary : Set where
  constructor native-title-critical-boundary
  field
    NativeTitleWasMajorLegalAdvance : Bool
    NativeTitleWasMajorLegalAdvanceIsTrue : NativeTitleWasMajorLegalAdvance ≡ true
    NativeTitleLegallyOperativeWithinAustralianLaw : Bool
    NativeTitleLegallyOperativeWithinAustralianLawIsTrue :
      NativeTitleLegallyOperativeWithinAustralianLaw ≡ true
    NativeTitleExhaustsIndigenousSovereignty : Bool
    NativeTitleExhaustsIndigenousSovereigntyIsFalse :
      NativeTitleExhaustsIndigenousSovereignty ≡ false
    NativeTitleTransformsCrownIndigenousPowerRelationByItself : Bool
    NativeTitleTransformsCrownIndigenousPowerRelationByItselfIsFalse :
      NativeTitleTransformsCrownIndigenousPowerRelationByItself ≡ false
    NativeTitleRecognitionIsNeutralObserverOfCountry : Bool
    NativeTitleRecognitionIsNeutralObserverOfCountryIsFalse :
      NativeTitleRecognitionIsNeutralObserverOfCountry ≡ false
    commonLawRecognitionIsSameAsIndigenousSelfAuthority : Bool
    commonLawRecognitionIsSameAsIndigenousSelfAuthorityIsFalse :
      commonLawRecognitionIsSameAsIndigenousSelfAuthority ≡ false
    criticalInfantilisationLabelIsCourtHolding : Bool
    criticalInfantilisationLabelIsCourtHoldingIsFalse :
      criticalInfantilisationLabelIsCourtHolding ≡ false
    noCessionPositionIsSourceBacked : Bool
    noCessionPositionIsSourceBackedIsTrue : noCessionPositionIsSourceBacked ≡ true
    noCessionWorldTruthAdjudicatedByThisFile : Bool
    noCessionWorldTruthAdjudicatedByThisFileIsFalse :
      noCessionWorldTruthAdjudicatedByThisFile ≡ false

open NativeTitleCriticalBoundary public

canonicalNativeTitleCriticalBoundary : NativeTitleCriticalBoundary
canonicalNativeTitleCriticalBoundary = native-title-critical-boundary
  true refl
  true refl
  false refl
  false refl
  false refl
  false refl
  false refl
  true refl
  false refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data RecognitionImpliesEqualSovereignty : Set where
data MaboRejectsTerraNulliusImpliesCrownSovereigntyReviewed : Set where
data CommonLawRecognitionConstitutesIndigenousOrder : Set where
data DoctrinalAdvanceImpliesDecolonisation : Set where
data CriticalCritiqueErasesLegalGain : Set where
data NoCessionSourcePositionAdjudicatesWorldCessionTruth : Set where
data LegalOperabilityImpliesDecolonialAdequacy : Set where

recognitionDoesNotImplyEqualSovereignty : RecognitionImpliesEqualSovereignty → ⊥
recognitionDoesNotImplyEqualSovereignty ()

terraNulliusCorrectionDoesNotReviewCrownSovereigntyAcquisition :
  MaboRejectsTerraNulliusImpliesCrownSovereigntyReviewed → ⊥
terraNulliusCorrectionDoesNotReviewCrownSovereigntyAcquisition ()

commonLawRecognitionDoesNotConstituteIndigenousOrder :
  CommonLawRecognitionConstitutesIndigenousOrder → ⊥
commonLawRecognitionDoesNotConstituteIndigenousOrder ()

doctrinalAdvanceDoesNotEntailDecolonisation : DoctrinalAdvanceImpliesDecolonisation → ⊥
doctrinalAdvanceDoesNotEntailDecolonisation ()

critiqueDoesNotEraseLegalGain : CriticalCritiqueErasesLegalGain → ⊥
critiqueDoesNotEraseLegalGain ()

sourcePositionDoesNotAdjudicateCessionWorldTruth :
  NoCessionSourcePositionAdjudicatesWorldCessionTruth → ⊥
sourcePositionDoesNotAdjudicateCessionWorldTruth ()

legalOperabilityDoesNotProveDecolonialAdequacy :
  LegalOperabilityImpliesDecolonialAdequacy → ⊥
legalOperabilityDoesNotProveDecolonialAdequacy ()
