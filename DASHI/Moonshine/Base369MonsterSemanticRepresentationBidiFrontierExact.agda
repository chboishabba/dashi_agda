module DASHI.Moonshine.Base369MonsterSemanticRepresentationBidiFrontierExact where

open import DASHI.Core.Prelude

import DASHI.Moonshine.Base369Monster3BRepresentationBidiSearchExact as ThreeB
import DASHI.Moonshine.MonsterWeightTwoSemanticActionRealisationExact as WeightTwo
import DASHI.Foundations.Base369NestedUnitCompletionMonsterAssemblyExact as Nested
import DASHI.Foundations.Base369MonsterSemanticCoordinateSystemExact as Semantic
import DASHI.Foundations.Base369StableAlgebraicIdentityTowerExact as Stable
import DASHI.Foundations.Base369MonsterNamedIdentityRegistryExact as Registry

------------------------------------------------------------------------
-- SEMANTIC MONSTER / ACTUAL REPRESENTATION BIDI FRONTIER
--
-- Cross-pollination principle:
-- do not wait for one monolithic 196883-state identification.  Use actual
-- representation-side discriminators already present in the 3B restriction
-- lane to test named semantic components one at a time.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Stable semantic constituent currently exposed by the named assembly.
------------------------------------------------------------------------

SemanticConstituent : Set
SemanticConstituent = Nested.SemanticMonsterConstituent196883

SemanticBulk : Set
SemanticBulk = Registry.NamedMonsterDecisionState196830

SemanticResidual : Set
SemanticResidual = Nested.ModeBoundary53Stable

SemanticAppraisal : Set
SemanticAppraisal = Stable.Appraisal729

------------------------------------------------------------------------
-- 2. Representation-side numerical discriminators already owned by the 3B
-- restriction lane.  They are receipts/targets, not carrier identifications.
------------------------------------------------------------------------

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
-- 3. Typed bridge payments.  Equal degrees do not discharge these fields.
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
-- 4. Consumer-first promotion ladder.
------------------------------------------------------------------------

data SemanticRepresentationLeaf : Set where
  replayActual3BRestriction
  identify729Action
  identify53ResidualAction
  identify729By90TensorConstituent
  attachBase369BulkCoordinates
  realiseWeightTwoEndomorphisms
  identifyFullWeightTwoCarrier
  preserveMonsterConstituent
  intertwineSemanticCoordinates
  : SemanticRepresentationLeaf

data LeafStatus : Set where leafClosed leafOpen leafBlocked : LeafStatus

leafStatus : SemanticRepresentationLeaf → LeafStatus
leafStatus replayActual3BRestriction = leafOpen
leafStatus identify729Action = leafBlocked
leafStatus identify53ResidualAction = leafBlocked
leafStatus identify729By90TensorConstituent = leafBlocked
leafStatus attachBase369BulkCoordinates = leafBlocked
leafStatus realiseWeightTwoEndomorphisms = leafOpen
leafStatus identifyFullWeightTwoCarrier = leafBlocked
leafStatus preserveMonsterConstituent = leafBlocked
leafStatus intertwineSemanticCoordinates = leafBlocked

------------------------------------------------------------------------
-- 5. Dependency graph: two independent upstream lanes can proceed in parallel.
--
-- Local/restriction lane:
--   replay -> 729 action -> tensor -> Base369 bulk
--          -> 53 residual -----------------^
--
-- Global/VOA lane:
--   End evaluation -> weight-two carrier -> constituent preservation
--
-- They meet only at semantic-coordinate intertwining.
------------------------------------------------------------------------

data Requires : SemanticRepresentationLeaf → SemanticRepresentationLeaf → Set where
  heisenbergNeedsReplay : Requires identify729Action replayActual3BRestriction
  residualNeedsReplay : Requires identify53ResidualAction replayActual3BRestriction
  tensorNeeds729 : Requires identify729By90TensorConstituent identify729Action
  bulkNeedsTensor : Requires attachBase369BulkCoordinates identify729By90TensorConstituent
  bulkNeedsResidual : Requires attachBase369BulkCoordinates identify53ResidualAction
  weightTwoNeedsEvaluation : Requires identifyFullWeightTwoCarrier realiseWeightTwoEndomorphisms
  constituentNeedsWeightTwo : Requires preserveMonsterConstituent identifyFullWeightTwoCarrier
  semanticNeedsBulk : Requires intertwineSemanticCoordinates attachBase369BulkCoordinates
  semanticNeedsConstituent : Requires intertwineSemanticCoordinates preserveMonsterConstituent

------------------------------------------------------------------------
-- 6. The terminal receipt is deliberately factorised.
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
-- 7. Why this is better than a cardinality-first global bijection.
------------------------------------------------------------------------

data Shared729DegreeIdentifiesRepresentation : Set where
data Shared53DegreeIdentifiesResidual : Set where
data Fin196883BijectionProvesMonsterEquivariance : Set where
data ThreeBRestrictionAloneDeterminesGlobalAction : Set where
\data SemanticCoordinateNamesDetermineCharacter : Set where

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

record SemanticRepresentationBidiBoundary : Set where
  constructor semantic-representation-bidi-boundary
  field
    actual3BRestrictionProducerExists : Bool
    semantic729TargetNamed : Bool
    semantic53TargetNamed : Bool
    weightTwoActionEvaluationPaymentNamed : Bool
    twoUpstreamLanesCanProceedIndependently : Bool
    terminalReceiptFactorised : Bool
    equalDimensionsCloseActionBridge : Bool
    localRestrictionAloneProvesGlobalMonsterAction : Bool

canonicalSemanticRepresentationBidiBoundary : SemanticRepresentationBidiBoundary
canonicalSemanticRepresentationBidiBoundary =
  semantic-representation-bidi-boundary
    true true true true true true false false
