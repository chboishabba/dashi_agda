module DASHI.Moonshine.Base369MonsterSemanticRepresentationBidiFrontierExact where

open import DASHI.Core.Prelude

import DASHI.Moonshine.Base369Monster3BRepresentationBidiSearchExact as ThreeB
import DASHI.Moonshine.Monster3BFiniteStoneVonNeumannFrontierExact as Stone
import DASHI.Moonshine.Monster3BMultiplicityEvaluationExact as Actual
import DASHI.Moonshine.Base369Monster3BActualSectorRecognitionBidiExact as Base369Recognition
import DASHI.Moonshine.MonsterWeightTwoSemanticActionRealisationExact as WeightTwo
import DASHI.Foundations.Base369NestedUnitCompletionMonsterAssemblyExact as Nested
import DASHI.Foundations.Base369MonsterSemanticCoordinateSystemExact as Semantic
import DASHI.Foundations.Base369StableAlgebraicIdentityTowerExact as Stable
import DASHI.Foundations.Base369MonsterNamedIdentityRegistryExact as Registry

------------------------------------------------------------------------
-- SEMANTIC MONSTER / ACTUAL REPRESENTATION BIDI FRONTIER
--
-- Do not wait for one monolithic 196883-state identification.  The actual 3B
-- restriction can test named semantic components locally, while the global
-- weight-two/VOA lane constrains the full carrier and invariant conformal unit.
------------------------------------------------------------------------

SemanticConstituent : Set
SemanticConstituent = Nested.SemanticMonsterConstituent196883

SemanticBulk : Set
SemanticBulk = Registry.NamedMonsterDecisionState196830

SemanticResidual : Set
SemanticResidual = Nested.ModeBoundary53Stable

SemanticAppraisal : Set
SemanticAppraisal = Stable.Appraisal729

actualRestrictedHeisenbergDegree : Nat
actualRestrictedHeisenbergDegree = ThreeB.heisenbergFactor

actualRestrictedResidualDegree : Nat
actualRestrictedResidualDegree = ThreeB.invariantExcess

actualRestrictedMultiplicityDegree : Nat
actualRestrictedMultiplicityDegree = ThreeB.multiplicityFactor

heisenbergDegreeMatchesSemanticAppraisal :
  actualRestrictedHeisenbergDegree ≡ 729
heisenbergDegreeMatchesSemanticAppraisal = ThreeB.heisenbergFactorIs729

residualDegreeMatchesSemanticResidual :
  actualRestrictedResidualDegree ≡ 53
residualDegreeMatchesSemanticResidual = ThreeB.invariantExcessIs53

multiplicityDegreeIsNinety : actualRestrictedMultiplicityDegree ≡ 90
multiplicityDegreeIsNinety = ThreeB.multiplicityFactorIs90

------------------------------------------------------------------------
-- Typed action-level bridge payments.
------------------------------------------------------------------------

record AppraisalHeisenbergActionBridge : Set₁ where
  field
    HeisenbergRepresentationCarrier : Set
    appraisalCarrierIso : Stable.CarrierIso SemanticAppraisal HeisenbergRepresentationCarrier
    actualRestrictedCarrierIdentified : Set
    actualActionIntertwinesAppraisalCoordinates : Set
open AppraisalHeisenbergActionBridge public

record ResidualFiftyThreeActionBridge : Set₁ where
  field
    RestrictedResidualCarrier : Set
    residualCarrierIso : Stable.CarrierIso SemanticResidual RestrictedResidualCarrier
    central3BTraceSelectsResidual : Set
    residualActionStable : Set
    invariantLineRemovalAgreesWithLocal54To53 : Set
open ResidualFiftyThreeActionBridge public

record ConstituentTensorBridge : Set₁ where
  field
    appraisalBridge : AppraisalHeisenbergActionBridge
    MultiplicityCarrier90 : Set
    tensorConstituentCarrier : Set
    tensorCarrierIso :
      Stable.CarrierIso
        (SemanticAppraisal × MultiplicityCarrier90)
        tensorConstituentCarrier
    actual729By90ConstituentIdentified : Set
    tensorActionIntertwinesRestriction : Set
open ConstituentTensorBridge public

------------------------------------------------------------------------
-- The actual-sector -> Base369 compiler is already theorem-bearing once an
-- ActualZetaSectorRecognition is supplied.  It is not a further research leaf.
------------------------------------------------------------------------

record ActualRecognitionCompilerAvailable : Set₁ where
  field
    ActualSector : Set
    recognition : Actual.ActualZetaSectorRecognition ActualSector
    base369Recognition : Base369Recognition.ActualBase369SectorRecognition ActualSector
    compilerExact :
      base369Recognition
      ≡ Base369Recognition.composeActualRecognitionWithBase369 recognition

open ActualRecognitionCompilerAvailable public

compileActualRecognitionToBase369 :
  ∀ {ActualSector} →
  (recognition : Actual.ActualZetaSectorRecognition ActualSector) →
  ActualRecognitionCompilerAvailable
compileActualRecognitionToBase369 recognition = record
  { ActualSector = _
  ; recognition = recognition
  ; base369Recognition = Base369Recognition.composeActualRecognitionWithBase369 recognition
  ; compilerExact = refl
  }

------------------------------------------------------------------------
-- Consumer-first promotion ladder.
------------------------------------------------------------------------

data SemanticRepresentationLeaf : Set where
  replayActual3BRestriction
  prove729WitnessedIrreducibility
  prove729FixedCentralCharacterUniqueness
  constructActualZetaSectorRecognition
  composeActualRecognitionToBase369
  identify53ResidualAction
  identify729By90TensorConstituent
  realiseWeightTwoEndomorphisms
  identifyFullWeightTwoCarrier
  preserveMonsterConstituent
  intertwineSemanticCoordinates
  : SemanticRepresentationLeaf

data LeafStatus : Set where leafClosed leafOpen leafBlocked : LeafStatus

leafStatus : SemanticRepresentationLeaf → LeafStatus
leafStatus replayActual3BRestriction = leafOpen
leafStatus prove729WitnessedIrreducibility = leafClosed
leafStatus prove729FixedCentralCharacterUniqueness = leafOpen
leafStatus constructActualZetaSectorRecognition = leafBlocked
leafStatus composeActualRecognitionToBase369 = leafClosed
leafStatus identify53ResidualAction = leafBlocked
leafStatus identify729By90TensorConstituent = leafBlocked
leafStatus realiseWeightTwoEndomorphisms = leafOpen
leafStatus identifyFullWeightTwoCarrier = leafBlocked
leafStatus preserveMonsterConstituent = leafBlocked
leafStatus intertwineSemanticCoordinates = leafBlocked

stoneWitnessedIrreducibilityClosed :
  Stone.leafState Stone.proveWitnessedIrreducibility ≡ Stone.closed
stoneWitnessedIrreducibilityClosed = refl

base369RecognitionCompilerClosed :
  leafStatus composeActualRecognitionToBase369 ≡ leafClosed
base369RecognitionCompilerClosed = refl

------------------------------------------------------------------------
-- Dependency graph.
--
-- Local/restriction lane:
--   model irreducibility -> uniqueness
--   replay ---------------------------> actual zeta recognition
--                                         |
--                                         v
--                           owned Base369 recognition compiler
--                                         |
--                                         v
--                                729 x 90 tensor
--
-- Separately replay -> 53 residual audit.
--
-- Global/VOA lane:
--   End evaluation -> weight-two carrier -> constituent preservation.
------------------------------------------------------------------------

data Requires : SemanticRepresentationLeaf → SemanticRepresentationLeaf → Set where
  uniquenessNeedsIrreducibility :
    Requires prove729FixedCentralCharacterUniqueness prove729WitnessedIrreducibility
  recognitionNeedsReplay :
    Requires constructActualZetaSectorRecognition replayActual3BRestriction
  recognitionNeedsUniqueness :
    Requires constructActualZetaSectorRecognition prove729FixedCentralCharacterUniqueness
  tensorNeedsRecognition :
    Requires identify729By90TensorConstituent constructActualZetaSectorRecognition
  residualNeedsReplay : Requires identify53ResidualAction replayActual3BRestriction
  weightTwoNeedsEvaluation : Requires identifyFullWeightTwoCarrier realiseWeightTwoEndomorphisms
  constituentNeedsWeightTwo : Requires preserveMonsterConstituent identifyFullWeightTwoCarrier
  semanticNeedsRecognition : Requires intertwineSemanticCoordinates constructActualZetaSectorRecognition
  semanticNeedsResidual : Requires intertwineSemanticCoordinates identify53ResidualAction
  semanticNeedsConstituent : Requires intertwineSemanticCoordinates preserveMonsterConstituent

------------------------------------------------------------------------
-- Factorised terminal receipt.
------------------------------------------------------------------------

record SemanticMonsterRepresentationReceipt : Set₁ where
  field
    actual3BReplay : ThreeB.RestrictionReplayReceipt
    appraisalActionBridge : AppraisalHeisenbergActionBridge
    residualActionBridge : ResidualFiftyThreeActionBridge
    tensorBridge : ConstituentTensorBridge
    semanticConstituentBridge : Nested.MonsterConstituentSemanticBridge
    allNamedSemanticCoordinatesIntertwine : Set
open SemanticMonsterRepresentationReceipt public

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

data Shared729DegreeIdentifiesRepresentation : Set where
data Shared53DegreeIdentifiesResidual : Set where
data Fin196883BijectionProvesMonsterEquivariance : Set where
data ThreeBRestrictionAloneDeterminesGlobalAction : Set where
data SemanticCoordinateNamesDetermineCharacter : Set where
data CharacterEqualityChoosesActualBasisRecognition : Set where

shared729DoesNotIdentifyRepresentation : Shared729DegreeIdentifiesRepresentation → ⊥
shared729DoesNotIdentifyRepresentation ()

shared53DoesNotIdentifyResidual : Shared53DegreeIdentifiesResidual → ⊥
shared53DoesNotIdentifyResidual ()

plainBijectionDoesNotProveEquivariance : Fin196883BijectionProvesMonsterEquivariance → ⊥
plainBijectionDoesNotProveEquivariance ()

local3BDoesNotDetermineGlobalAction : ThreeBRestrictionAloneDeterminesGlobalAction → ⊥
local3BDoesNotDetermineGlobalAction ()

semanticNamesDoNotDetermineCharacter : SemanticCoordinateNamesDetermineCharacter → ⊥
semanticNamesDoNotDetermineCharacter ()

characterEqualityDoesNotChooseBasisRecognition :
  CharacterEqualityChoosesActualBasisRecognition → ⊥
characterEqualityDoesNotChooseBasisRecognition ()

record SemanticRepresentationBidiBoundary : Set where
  constructor semantic-representation-bidi-boundary
  field
    actual3BRestrictionProducerExists : Bool
    semantic729TargetNamed : Bool
    semantic53TargetNamed : Bool
    witnessed729IrreducibilityClosed : Bool
    fixedCentralCharacterUniquenessStillLive : Bool
    actualRecognitionStillNeedsReplayAndUniqueness : Bool
    base369RecognitionCompilerAlreadyOwned : Bool
    weightTwoActionEvaluationPaymentNamed : Bool
    terminalReceiptFactorised : Bool
    equalDimensionsCloseActionBridge : Bool
    characterEqualityAloneChoosesBasis : Bool
    localRestrictionAloneProvesGlobalMonsterAction : Bool

canonicalSemanticRepresentationBidiBoundary : SemanticRepresentationBidiBoundary
canonicalSemanticRepresentationBidiBoundary =
  semantic-representation-bidi-boundary
    true true true true true true true true true
    false false false
