module DASHI.Physics.QFT.DHRHexagonProofPlanSurface where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.G6CrossLaneCommutingTheorem as G6
import DASHI.Physics.Closure.G6CrossLaneCommutingTheoremFromKostant as G6K
import DASHI.Physics.QFT.DHRGaugeReceiptSurface as DHR
import DASHI.Physics.QFT.DHRHexagonObligation as Hexagon

------------------------------------------------------------------------
-- Proof plan / obstruction surface for the Paper 2 DHR hexagon lane.
--
-- The current tempting route is:
--
--   FactorVec lane-action commutation
--     -> DHR braiding
--     -> DHR naturality + hexagon
--
-- The first arrow is not available in the repo.  G6 has an official tracked
-- FactorVec commutation theorem, while the DHR side still has only target
-- sockets for localised endomorphisms, intertwiners, tensor product, unit,
-- and statistics-derived symmetry.  This module records the exact missing
-- primitive without promoting DR classification or gauge assignment.

data DHRHexagonProofPlanStatus : Set where
  proofPlanOnlyNoPromotion :
    DHRHexagonProofPlanStatus

data DHRHexagonFirstMissingPrimitive : Set where
  missingDHRToTrackedLaneActionFunctor :
    DHRHexagonFirstMissingPrimitive

  missingIntertwinerNaturalityForTrackedCommutation :
    DHRHexagonFirstMissingPrimitive

  missingDHRFusionTensorProductConstructor :
    DHRHexagonFirstMissingPrimitive

  missingStatisticsOperatorToBraidingComputation :
    DHRHexagonFirstMissingPrimitive

  missingAssociatorPentagonUnitFromTensorProduct :
    DHRHexagonFirstMissingPrimitive

canonicalDHRHexagonPrimitiveOrder :
  List DHRHexagonFirstMissingPrimitive
canonicalDHRHexagonPrimitiveOrder =
  missingDHRToTrackedLaneActionFunctor
  ∷ missingIntertwinerNaturalityForTrackedCommutation
  ∷ missingDHRFusionTensorProductConstructor
  ∷ missingStatisticsOperatorToBraidingComputation
  ∷ missingAssociatorPentagonUnitFromTensorProduct
  ∷ []

data DHRBridgeAdapterRequestField : Set where
  requiresDHRObjectToTrackedLaneMap :
    DHRBridgeAdapterRequestField

  requiresDHRLocalisedEndomorphismCarrierPredicateWitness :
    DHRBridgeAdapterRequestField

  requiresDHRLocalisedEndomorphismAssignedLanePreservationWitness :
    DHRBridgeAdapterRequestField

  requiresDHRLocalisedEndomorphismCrossLaneInvisibilityWitness :
    DHRBridgeAdapterRequestField

  requiresDHRIntertwinerTrackedCarrierAction :
    DHRBridgeAdapterRequestField

  requiresDHRIntertwinerTrackedCarrierPreservationWitness :
    DHRBridgeAdapterRequestField

  requiresDHRIntertwinerForeignLaneInvisibilityWitness :
    DHRBridgeAdapterRequestField

canonicalDHRBridgeAdapterRequestFields :
  List DHRBridgeAdapterRequestField
canonicalDHRBridgeAdapterRequestFields =
  requiresDHRObjectToTrackedLaneMap
  ∷ requiresDHRLocalisedEndomorphismCarrierPredicateWitness
  ∷ requiresDHRLocalisedEndomorphismAssignedLanePreservationWitness
  ∷ requiresDHRLocalisedEndomorphismCrossLaneInvisibilityWitness
  ∷ requiresDHRIntertwinerTrackedCarrierAction
  ∷ requiresDHRIntertwinerTrackedCarrierPreservationWitness
  ∷ requiresDHRIntertwinerForeignLaneInvisibilityWitness
  ∷ []

data DHRSectorLaneInvariantRequestField : Set where
  requiresSectorLaneInvariantRelation :
    DHRSectorLaneInvariantRequestField

  requiresSectorAssignedLane :
    DHRSectorLaneInvariantRequestField

  requiresSectorLaneRepresentation :
    DHRSectorLaneInvariantRequestField

  requiresCrossLaneInvisibility :
    DHRSectorLaneInvariantRequestField

  requiresLocalisedEndomorphismCarrierSemantics :
    DHRSectorLaneInvariantRequestField

  requiresLocalisedEndomorphismWitnessAdapterBoundary :
    DHRSectorLaneInvariantRequestField

  requiresLocalisedEndomorphismCarrierPredicateWitness :
    DHRSectorLaneInvariantRequestField

  requiresLocalisedEndomorphismAssignedLanePreservationWitness :
    DHRSectorLaneInvariantRequestField

  requiresLocalisedEndomorphismCrossLaneInvisibilityWitness :
    DHRSectorLaneInvariantRequestField

  requiresObjectLaneClassifier :
    DHRSectorLaneInvariantRequestField

  requiresClassifierInvariantEvidence :
    DHRSectorLaneInvariantRequestField

  requiresIntertwinerPreservesLaneInvariant :
    DHRSectorLaneInvariantRequestField

  requiresIntertwinerTrackedCarrierSemantics :
    DHRSectorLaneInvariantRequestField

  requiresIntertwinerWitnessAdapterBoundary :
    DHRSectorLaneInvariantRequestField

  requiresIntertwinerRepresentationAction :
    DHRSectorLaneInvariantRequestField

  requiresIntertwinerTrackedCarrierPreservationWitness :
    DHRSectorLaneInvariantRequestField

  requiresIntertwinerForeignLaneInvisibilityWitness :
    DHRSectorLaneInvariantRequestField

  requiresCarrierActionFromInvariant :
    DHRSectorLaneInvariantRequestField

canonicalDHRSectorLaneInvariantRequestFields :
  List DHRSectorLaneInvariantRequestField
canonicalDHRSectorLaneInvariantRequestFields =
  requiresSectorLaneInvariantRelation
  ∷ requiresSectorAssignedLane
  ∷ requiresSectorLaneRepresentation
  ∷ requiresCrossLaneInvisibility
  ∷ requiresLocalisedEndomorphismCarrierSemantics
  ∷ requiresLocalisedEndomorphismWitnessAdapterBoundary
  ∷ requiresLocalisedEndomorphismCarrierPredicateWitness
  ∷ requiresLocalisedEndomorphismAssignedLanePreservationWitness
  ∷ requiresLocalisedEndomorphismCrossLaneInvisibilityWitness
  ∷ requiresObjectLaneClassifier
  ∷ requiresClassifierInvariantEvidence
  ∷ requiresIntertwinerPreservesLaneInvariant
  ∷ requiresIntertwinerTrackedCarrierSemantics
  ∷ requiresIntertwinerWitnessAdapterBoundary
  ∷ requiresIntertwinerRepresentationAction
  ∷ requiresIntertwinerTrackedCarrierPreservationWitness
  ∷ requiresIntertwinerForeignLaneInvisibilityWitness
  ∷ requiresCarrierActionFromInvariant
  ∷ []

data DHRNondegenerateCarrierSemanticsExtensionField : Set where
  requiresSelectedNonemptyCarrierPredicate :
    DHRNondegenerateCarrierSemanticsExtensionField

  requiresGlobalForeignLaneActionIdentityOnSelectedCarrier :
    DHRNondegenerateCarrierSemanticsExtensionField

  requiresTrackedIntertwinerCarrierAction :
    DHRNondegenerateCarrierSemanticsExtensionField

  requiresTrackedCarrierActionPreservation :
    DHRNondegenerateCarrierSemanticsExtensionField

  requiresTrackedCarrierActionForeignLaneInvisibility :
    DHRNondegenerateCarrierSemanticsExtensionField

  requiresFinalNondegenerateSemanticsExternalInterface :
    DHRNondegenerateCarrierSemanticsExtensionField

canonicalDHRNondegenerateCarrierSemanticsExtensionFields :
  List DHRNondegenerateCarrierSemanticsExtensionField
canonicalDHRNondegenerateCarrierSemanticsExtensionFields =
  requiresSelectedNonemptyCarrierPredicate
  ∷ requiresGlobalForeignLaneActionIdentityOnSelectedCarrier
  ∷ requiresTrackedIntertwinerCarrierAction
  ∷ requiresTrackedCarrierActionPreservation
  ∷ requiresTrackedCarrierActionForeignLaneInvisibility
  ∷ requiresFinalNondegenerateSemanticsExternalInterface
  ∷ []

data DHRObjectToLaneBridgeRoute : Set where
  objectToLaneNotReadableFromLocalEndomorphism :
    DHRObjectToLaneBridgeRoute

  objectToLaneMayBeAdapterSuppliedFailClosed :
    DHRObjectToLaneBridgeRoute

  objectToLaneDownstreamOfPrimeLaneDHRClassification :
    DHRObjectToLaneBridgeRoute

data DHRIntertwinerCarrierActionBridgeRoute : Set where
  intertwinerCarrierActionNotReadableFromLocalIntertwiner :
    DHRIntertwinerCarrierActionBridgeRoute

  intertwinerCarrierActionMayBeAdapterSuppliedFailClosed :
    DHRIntertwinerCarrierActionBridgeRoute

  intertwinerCarrierActionDownstreamOfDRFibreFunctor :
    DHRIntertwinerCarrierActionBridgeRoute

data DHRSemanticBridgeFirstBlocker : Set where
  firstBlockerNoSectorLaneInvariantOnLocalisedEndomorphism :
    DHRSemanticBridgeFirstBlocker

  firstBlockerNoCarrierActionForDHRIntertwiner :
    DHRSemanticBridgeFirstBlocker

  firstBlockerPrimeLaneDHRClassificationStillConditional :
    DHRSemanticBridgeFirstBlocker

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

record DHRSectorRepresentationData
  (operator : G6.NontrivialTrackedLaneOperator)
  (ρ : DHR.LocalisedEndomorphism)
  (lane : G6.Lane) :
  Set where
  field
    representedSector :
      DHR.SuperselectionSector

    representedSectorMatchesEndomorphism :
      DHR.LocalisedEndomorphism.localisedSector ρ
      ≡
      representedSector

    representedLane :
      G6.Lane

    representedLaneMatchesClassifierLane :
      lane
      ≡
      representedLane

    sectorCarrierPredicate :
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      Bool

    assignedLaneActionPreservesCarrierPredicate :
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      sectorCarrierPredicate x ≡ true →
      sectorCarrierPredicate
        (G6.NontrivialTrackedLaneOperator.laneAction
          operator
          representedLane
          x)
      ≡
      true

    representationBoundary :
      List String

open DHRSectorRepresentationData public

record DHRCrossLaneInvisibilityEvidence
  (operator : G6.NontrivialTrackedLaneOperator)
  {ρ : DHR.LocalisedEndomorphism}
  {lane : G6.Lane}
  (representation : DHRSectorRepresentationData operator ρ lane) :
  Set where
  field
    invisibleAwayFromRepresentedLane :
      (otherLane : G6.Lane) →
      DHRSectorRepresentationData.representedLane representation ≢ otherLane →
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      DHRSectorRepresentationData.sectorCarrierPredicate representation x ≡ true →
      G6.NontrivialTrackedLaneOperator.laneAction
        operator
        otherLane
        x
      ≡
      x

    invisibilityBoundary :
      List String

open DHRCrossLaneInvisibilityEvidence public

record DHRSectorDefinition
  (operator : G6.NontrivialTrackedLaneOperator) :
  Set where
  field
    sector :
      DHR.SuperselectionSector

    assignedLane :
      G6.Lane

    representationUnderLaneTarget :
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      Bool

    assignedLaneActionPreservesRepresentation :
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      representationUnderLaneTarget x ≡ true →
      representationUnderLaneTarget
        (G6.NontrivialTrackedLaneOperator.laneAction
          operator
          assignedLane
          x)
      ≡
      true

    crossLaneInvisibilityTarget :
      (otherLane : G6.Lane) →
      assignedLane ≢ otherLane →
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      representationUnderLaneTarget x ≡ true →
      G6.NontrivialTrackedLaneOperator.laneAction
        operator
        otherLane
        x
      ≡
      x

    sectorDefinitionBoundary :
      List String

open DHRSectorDefinition public

record DHRSectorLaneInvariantRelation
  (operator : G6.NontrivialTrackedLaneOperator)
  (ρ : DHR.LocalisedEndomorphism)
  (lane : G6.Lane) :
  Set where
  field
    sectorDefinition :
      DHRSectorDefinition operator

    localizedSectorMatchesDefinition :
      DHR.LocalisedEndomorphism.localisedSector ρ
      ≡
      DHRSectorDefinition.sector sectorDefinition

    laneMatchesAssignedLane :
      lane
      ≡
      DHRSectorDefinition.assignedLane sectorDefinition

    endomorphismActsThroughAssignedRepresentationTarget :
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      DHRSectorDefinition.representationUnderLaneTarget
        sectorDefinition
        x
      ≡
      true

    crossLaneTrivialityVisibleToEndomorphismTarget :
      (otherLane : G6.Lane) →
      DHRSectorDefinition.assignedLane sectorDefinition ≢ otherLane →
      Bool

    invariantBoundary :
      List String

open DHRSectorLaneInvariantRelation public

record DHRSectorLaneClassifierEvidence
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω where
  field
    objectLaneClassifier :
      DHR.LocalisedEndomorphism →
      G6.Lane

    classifierInvariantEvidence :
      (ρ : DHR.LocalisedEndomorphism) →
      DHRSectorLaneInvariantRelation
        operator
        ρ
        (objectLaneClassifier ρ)

    downstreamObjectToLaneMap :
      DHR.LocalisedEndomorphism →
      G6.Lane

    downstreamObjectToLaneAgreesWithClassifier :
      (ρ : DHR.LocalisedEndomorphism) →
      downstreamObjectToLaneMap ρ
      ≡
      objectLaneClassifier ρ

    classifierConstructed :
      Bool

    classifierConstructedIsFalse :
      classifierConstructed ≡ false

    classifierBoundary :
      List String

open DHRSectorLaneClassifierEvidence public

record DHRTrackedIntertwinerCarrierAction
  (operator : G6.NontrivialTrackedLaneOperator)
  (ρ σ : DHR.LocalisedEndomorphism)
  (f : DHR.Intertwiner ρ σ)
  (ρLane σLane : G6.Lane)
  (ρInvariant : DHRSectorLaneInvariantRelation operator ρ ρLane)
  (σInvariant : DHRSectorLaneInvariantRelation operator σ σLane) :
  Set where
  field
    trackedCarrierAction :
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      Bool

    trackedCarrierActionPreservesRepresentation :
      (x y : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      DHRSectorDefinition.representationUnderLaneTarget
        (DHRSectorLaneInvariantRelation.sectorDefinition ρInvariant)
        x
      ≡
      true →
      trackedCarrierAction x y ≡ true →
      DHRSectorDefinition.representationUnderLaneTarget
        (DHRSectorLaneInvariantRelation.sectorDefinition σInvariant)
        y
      ≡
      true

    trackedCarrierActionSeesNoForeignLane :
      (otherLane : G6.Lane) →
      DHRSectorDefinition.assignedLane
        (DHRSectorLaneInvariantRelation.sectorDefinition ρInvariant)
      ≢
      otherLane →
      DHRSectorDefinition.assignedLane
        (DHRSectorLaneInvariantRelation.sectorDefinition σInvariant)
      ≢
      otherLane →
      Bool

    actionBoundary :
      List String

open DHRTrackedIntertwinerCarrierAction public

sectorLaneInvariantToLocalisedCarrierSemantics :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ : DHR.LocalisedEndomorphism) →
  (lane : G6.Lane) →
  DHRSectorLaneInvariantRelation operator ρ lane →
  Hexagon.LocalisedEndomorphismCarrierSemantics operator ρ lane
sectorLaneInvariantToLocalisedCarrierSemantics
  operator ρ lane invariant
  with DHRSectorLaneInvariantRelation.laneMatchesAssignedLane invariant
... | refl =
  record
    { semanticSector =
        DHRSectorDefinition.sector
          (DHRSectorLaneInvariantRelation.sectorDefinition invariant)
    ; semanticSectorMatchesLocalisedSector =
        DHRSectorLaneInvariantRelation.localizedSectorMatchesDefinition
          invariant
    ; carrierPredicate =
        DHRSectorDefinition.representationUnderLaneTarget
          (DHRSectorLaneInvariantRelation.sectorDefinition invariant)
    ; assignedLaneActionPreservesCarrier =
        DHRSectorDefinition.assignedLaneActionPreservesRepresentation
          (DHRSectorLaneInvariantRelation.sectorDefinition invariant)
    ; crossLaneActionInvisibleOnCarrier =
        DHRSectorDefinition.crossLaneInvisibilityTarget
          (DHRSectorLaneInvariantRelation.sectorDefinition invariant)
    ; carrierSemanticsBoundary =
        "Derived from an inhabited DHRSectorLaneInvariantRelation"
        ∷ "No DHR/DR classification or hexagon closure is promoted by this derivation"
        ∷ []
    }

sectorRepresentationDataToLocalisedCarrierSemantics :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ : DHR.LocalisedEndomorphism) →
  (lane : G6.Lane) →
  (representation : DHRSectorRepresentationData operator ρ lane) →
  DHRCrossLaneInvisibilityEvidence operator representation →
  Hexagon.LocalisedEndomorphismCarrierSemantics operator ρ lane
sectorRepresentationDataToLocalisedCarrierSemantics
  operator ρ lane representation invisibility
  with DHRSectorRepresentationData.representedLaneMatchesClassifierLane
        representation
... | refl =
  record
    { semanticSector =
        DHRSectorRepresentationData.representedSector representation
    ; semanticSectorMatchesLocalisedSector =
        DHRSectorRepresentationData.representedSectorMatchesEndomorphism
          representation
    ; carrierPredicate =
        DHRSectorRepresentationData.sectorCarrierPredicate representation
    ; assignedLaneActionPreservesCarrier =
        DHRSectorRepresentationData.assignedLaneActionPreservesCarrierPredicate
          representation
    ; crossLaneActionInvisibleOnCarrier =
        DHRCrossLaneInvisibilityEvidence.invisibleAwayFromRepresentedLane
          invisibility
    ; carrierSemanticsBoundary =
        "Derived from sector representation data plus cross-lane invisibility evidence"
        ∷ "This is a witness move only; it does not construct the representation data itself"
        ∷ []
    }

classifierEvidenceToLocalisedCarrierSemantics :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (classifier : DHRSectorLaneClassifierEvidence operator) →
  (ρ : DHR.LocalisedEndomorphism) →
  Hexagon.LocalisedEndomorphismCarrierSemantics
    operator
    ρ
    (DHRSectorLaneClassifierEvidence.objectLaneClassifier classifier ρ)
classifierEvidenceToLocalisedCarrierSemantics operator classifier ρ =
  sectorLaneInvariantToLocalisedCarrierSemantics
    operator
    ρ
    (DHRSectorLaneClassifierEvidence.objectLaneClassifier classifier ρ)
    (DHRSectorLaneClassifierEvidence.classifierInvariantEvidence
      classifier
      ρ)

trackedActionToIntertwinerCarrierSemantics :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ σ : DHR.LocalisedEndomorphism) →
  (f : DHR.Intertwiner ρ σ) →
  (ρLane σLane : G6.Lane) →
  (ρInvariant : DHRSectorLaneInvariantRelation operator ρ ρLane) →
  (σInvariant : DHRSectorLaneInvariantRelation operator σ σLane) →
  DHRTrackedIntertwinerCarrierAction
    operator
    ρ
    σ
    f
    ρLane
    σLane
    ρInvariant
    σInvariant →
  Hexagon.IntertwinerTrackedCarrierSemantics
    operator
    ρ
    σ
    f
    ρLane
    σLane
    (sectorLaneInvariantToLocalisedCarrierSemantics
      operator
      ρ
      ρLane
      ρInvariant)
    (sectorLaneInvariantToLocalisedCarrierSemantics
      operator
      σ
      σLane
      σInvariant)
trackedActionToIntertwinerCarrierSemantics
  operator ρ σ f ρLane σLane ρInvariant σInvariant action
  with DHRSectorLaneInvariantRelation.laneMatchesAssignedLane ρInvariant
     | DHRSectorLaneInvariantRelation.laneMatchesAssignedLane σInvariant
... | refl | refl =
  record
    { trackedCarrierAction =
        DHRTrackedIntertwinerCarrierAction.trackedCarrierAction action
    ; trackedCarrierActionPreservesSemantics =
        DHRTrackedIntertwinerCarrierAction.trackedCarrierActionPreservesRepresentation
          action
    ; trackedCarrierActionSeesNoForeignLane =
        DHRTrackedIntertwinerCarrierAction.trackedCarrierActionSeesNoForeignLane
          action
    ; trackedCarrierSemanticsBoundary =
        "Derived from an inhabited DHRTrackedIntertwinerCarrierAction over source and target sector-lane invariants"
        ∷ "This moves tracked-action evidence into the primitive Hexagon.IntertwinerTrackedCarrierSemantics surface without closing naturality or hexagon laws"
        ∷ []
    }

record DHRIntertwinerPreservesSectorLaneInvariantRelation
  (operator : G6.NontrivialTrackedLaneOperator)
  (ρ σ : DHR.LocalisedEndomorphism)
  (f : DHR.Intertwiner ρ σ)
  (ρLane σLane : G6.Lane)
  (ρInvariant : DHRSectorLaneInvariantRelation operator ρ ρLane)
  (σInvariant : DHRSectorLaneInvariantRelation operator σ σLane) :
  Set where
  field
    intertwinerRepresentationActionTarget :
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      Bool

    trackedCarrierActionEvidence :
      DHRTrackedIntertwinerCarrierAction
        operator
        ρ
        σ
        f
        ρLane
        σLane
        ρInvariant
        σInvariant

    sourceRepresentationPreservedTarget :
      (x y : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      DHRSectorDefinition.representationUnderLaneTarget
        (DHRSectorLaneInvariantRelation.sectorDefinition ρInvariant)
        x
      ≡
      true →
      intertwinerRepresentationActionTarget x y ≡ true →
      DHRSectorDefinition.representationUnderLaneTarget
        (DHRSectorLaneInvariantRelation.sectorDefinition σInvariant)
        y
      ≡
      true →
      Bool

    intertwinerSeesOnlyAssignedLaneTarget :
      (otherLane : G6.Lane) →
      DHRSectorDefinition.assignedLane
        (DHRSectorLaneInvariantRelation.sectorDefinition ρInvariant)
      ≢
      otherLane →
      DHRSectorDefinition.assignedLane
        (DHRSectorLaneInvariantRelation.sectorDefinition σInvariant)
      ≢
      otherLane →
      Bool

    preservationBoundary :
      List String

open DHRIntertwinerPreservesSectorLaneInvariantRelation public

record DHRNondegenerateCarrierSemanticsExtensionRequest
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω where
  field
    degenerateWitnessAvailable :
      (ρ : DHR.LocalisedEndomorphism) →
      (lane : G6.Lane) →
      Hexagon.DegenerateLocalisedEndomorphismCarrierSemanticsReceipt
        operator
        ρ
        lane

    g6TrackedLocalisedCarrierSemanticsAttemptTarget :
      (ρ : DHR.LocalisedEndomorphism) →
      (lane : G6.Lane) →
      Hexagon.G6TrackedLocalisedCarrierSemanticsAttempt operator ρ lane

    finalLocalisedSuppliedInterfaceAbsenceLedger :
      (ρ : DHR.LocalisedEndomorphism) →
      (lane : G6.Lane) →
      Hexagon.FinalNondegenerateLocalisedCarrierSuppliedInterfaceAbsenceLedger
        operator
        ρ
        lane

    exactExtensionFields :
      List DHRNondegenerateCarrierSemanticsExtensionField

    selectedCarrierPredicateTarget :
      (ρ : DHR.LocalisedEndomorphism) →
      G6.Lane →
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      Bool

    selectedCarrierNonemptyEvidenceTarget :
      (ρ : DHR.LocalisedEndomorphism) →
      (lane : G6.Lane) →
      Set

    globalForeignLaneActionIdentityTarget :
      (ρ : DHR.LocalisedEndomorphism) →
      (lane otherLane : G6.Lane) →
      lane ≢ otherLane →
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      selectedCarrierPredicateTarget ρ lane x ≡ true →
      G6.NontrivialTrackedLaneOperator.laneAction
        operator
        otherLane
        x
      ≡
      x

    trackedIntertwinerCarrierActionTarget :
      (ρ σ : DHR.LocalisedEndomorphism) →
      DHR.Intertwiner ρ σ →
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      Bool

    trackedCarrierActionPreservationTarget :
      (ρ σ : DHR.LocalisedEndomorphism) →
      (f : DHR.Intertwiner ρ σ) →
      (ρLane σLane : G6.Lane) →
      (x y : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      selectedCarrierPredicateTarget ρ ρLane x ≡ true →
      trackedIntertwinerCarrierActionTarget ρ σ f x y ≡ true →
      selectedCarrierPredicateTarget σ σLane y ≡ true

    trackedCarrierActionForeignLaneInvisibilityTarget :
      (ρ σ : DHR.LocalisedEndomorphism) →
      (f : DHR.Intertwiner ρ σ) →
      (ρLane σLane otherLane : G6.Lane) →
      ρLane ≢ otherLane →
      σLane ≢ otherLane →
      Bool

    nondegenerateLocalisedExternalInterfaceTarget :
      (ρ : DHR.LocalisedEndomorphism) →
      (lane : G6.Lane) →
      Hexagon.NondegenerateLocalisedEndomorphismCarrierSemanticsInterface
        operator
        ρ
        lane

    nondegenerateLocalisedExternalAdapterBoundaryTarget :
      (ρ : DHR.LocalisedEndomorphism) →
      (lane : G6.Lane) →
      Hexagon.LocalisedEndomorphismCarrierAdapterBoundary
        operator
        ρ
        lane
        (Hexagon.nondegenerateLocalisedInterfaceToCarrierSemantics
          operator
          ρ
          lane
          (nondegenerateLocalisedExternalInterfaceTarget ρ lane))

    nondegenerateIntertwinerExternalInterfaceTarget :
      (ρ σ : DHR.LocalisedEndomorphism) →
      (f : DHR.Intertwiner ρ σ) →
      (ρLane σLane : G6.Lane) →
      Hexagon.NondegenerateIntertwinerTrackedCarrierSemanticsInterface
        operator
        ρ
        σ
        f
        ρLane
        σLane
        (nondegenerateLocalisedExternalInterfaceTarget ρ ρLane)
        (nondegenerateLocalisedExternalInterfaceTarget σ σLane)

    conditionalIntertwinerInterfaceFromLocalInterfacesAvailable :
      Bool

    conditionalIntertwinerInterfaceFromLocalInterfacesAvailableIsTrue :
      conditionalIntertwinerInterfaceFromLocalInterfacesAvailable ≡ true

    nondegenerateIntertwinerExternalAdapterBoundaryTarget :
      (ρ σ : DHR.LocalisedEndomorphism) →
      (f : DHR.Intertwiner ρ σ) →
      (ρLane σLane : G6.Lane) →
      Hexagon.IntertwinerTrackedCarrierAdapterBoundary
        operator
        ρ
        σ
        f
        ρLane
        σLane
        (Hexagon.nondegenerateLocalisedInterfaceToCarrierSemantics
          operator
          ρ
          ρLane
          (nondegenerateLocalisedExternalInterfaceTarget ρ ρLane))
        (Hexagon.nondegenerateLocalisedInterfaceToCarrierSemantics
          operator
          σ
          σLane
          (nondegenerateLocalisedExternalInterfaceTarget σ σLane))
        (Hexagon.nondegenerateIntertwinerInterfaceToCarrierSemantics
          operator
          ρ
          σ
          f
          ρLane
          σLane
          (nondegenerateLocalisedExternalInterfaceTarget ρ ρLane)
          (nondegenerateLocalisedExternalInterfaceTarget σ σLane)
          (nondegenerateIntertwinerExternalInterfaceTarget
            ρ
            σ
            f
            ρLane
            σLane))

    degenerateWitnessConstructed :
      Bool

    degenerateWitnessConstructedIsTrue :
      degenerateWitnessConstructed ≡ true

    nondegenerateCarrierPredicateConstructed :
      Bool

    nondegenerateCarrierPredicateConstructedIsFalse :
      nondegenerateCarrierPredicateConstructed ≡ false

    globalForeignLaneActionIdentityConstructed :
      Bool

    globalForeignLaneActionIdentityConstructedIsFalse :
      globalForeignLaneActionIdentityConstructed ≡ false

    trackedCarrierActionConstructed :
      Bool

    trackedCarrierActionConstructedIsFalse :
      trackedCarrierActionConstructed ≡ false

    extensionRequestClosed :
      Bool

    extensionRequestClosedIsFalse :
      extensionRequestClosed ≡ false

    promotesDRClassification :
      Bool

    promotesDRClassificationIsFalse :
      promotesDRClassification ≡ false

    reconstructsGaugeAssignment :
      Bool

    reconstructsGaugeAssignmentIsFalse :
      reconstructsGaugeAssignment ≡ false

    extensionBoundary :
      List String

open DHRNondegenerateCarrierSemanticsExtensionRequest public

record DHRStructuralLocalisationBridge
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω where
  field
    localisedForeignLaneIdEvidenceTarget :
      (ρ : DHR.LocalisedEndomorphism) →
      (lane foreignLaneId : G6.Lane) →
      Hexagon.NondegenerateLocalisedEndomorphismCarrierSemanticsInterface
        operator
        ρ
        lane →
      lane ≢ foreignLaneId →
      Hexagon.LocalisedEndomorphismWithForeignLaneIdEvidence
        operator
        ρ
        lane
        foreignLaneId

    localisedForeignLaneIdAdapterBoundaryTarget :
      (ρ : DHR.LocalisedEndomorphism) →
      (lane foreignLaneId : G6.Lane) →
      (evidence :
        Hexagon.LocalisedEndomorphismWithForeignLaneIdEvidence
          operator
          ρ
          lane
          foreignLaneId) →
      Hexagon.LocalisedEndomorphismCarrierAdapterBoundary
        operator
        ρ
        lane
        (Hexagon.localisedForeignLaneCarrierSemantics evidence)

    nonemptyWitnessFromForeignLaneIdEvidenceTarget :
      (ρ : DHR.LocalisedEndomorphism) →
      (lane foreignLaneId : G6.Lane) →
      (evidence :
        Hexagon.LocalisedEndomorphismWithForeignLaneIdEvidence
          operator
          ρ
          lane
          foreignLaneId) →
      Hexagon.LocalisedEndomorphismNonemptyCarrierWitness
        operator
        ρ
        lane
        (Hexagon.localisedForeignLaneCarrierSemantics evidence)

    trackedIntertwinerForeignLaneIdAdapterTarget :
      (ρ σ : DHR.LocalisedEndomorphism) →
      (f : DHR.Intertwiner ρ σ) →
      (ρLane σLane foreignLaneId : G6.Lane) →
      (ρEvidence :
        Hexagon.LocalisedEndomorphismWithForeignLaneIdEvidence
          operator
          ρ
          ρLane
          foreignLaneId) →
      (σEvidence :
        Hexagon.LocalisedEndomorphismWithForeignLaneIdEvidence
          operator
          σ
          σLane
          foreignLaneId) →
      Hexagon.TrackedIntertwinerForeignLaneIdAdapter
        operator
        ρ
        σ
        f
        ρLane
        σLane
        foreignLaneId
        ρEvidence
        σEvidence

    localisedCarrierSemanticsDerivedFromSuppliedInterface :
      Bool

    localisedCarrierSemanticsDerivedFromSuppliedInterfaceIsTrue :
      localisedCarrierSemanticsDerivedFromSuppliedInterface ≡ true

    nonemptyWitnessDerivedFromSuppliedInterface :
      Bool

    nonemptyWitnessDerivedFromSuppliedInterfaceIsTrue :
      nonemptyWitnessDerivedFromSuppliedInterface ≡ true

    trackedIntertwinerAdapterDerivedFromSuppliedInterfaces :
      Bool

    trackedIntertwinerAdapterDerivedFromSuppliedInterfacesIsTrue :
      trackedIntertwinerAdapterDerivedFromSuppliedInterfaces ≡ true

    objectLaneClassifierConstructed :
      Bool

    objectLaneClassifierConstructedIsFalse :
      objectLaneClassifierConstructed ≡ false

    bridgeClosed :
      Bool

    bridgeClosedIsFalse :
      bridgeClosed ≡ false

    promotesDRClassification :
      Bool

    promotesDRClassificationIsFalse :
      promotesDRClassification ≡ false

    reconstructsGaugeAssignment :
      Bool

    reconstructsGaugeAssignmentIsFalse :
      reconstructsGaugeAssignment ≡ false

    closesSymmetricHexagon :
      Bool

    closesSymmetricHexagonIsFalse :
      closesSymmetricHexagon ≡ false

    structuralBridgeBoundary :
      List String

open DHRStructuralLocalisationBridge public

record DHRToG6TrackedLaneActionFunctorTarget : Setω where
  field
    objectMapTarget :
      DHR.LocalisedEndomorphism →
      G6.Lane

    actionCompatibilityTarget :
      (ρ : DHR.LocalisedEndomorphism) →
      Set

    intertwinerNaturalityTarget :
      (ρ σ : DHR.LocalisedEndomorphism) →
      DHR.Intertwiner ρ σ →
      Set

    tensorCompatibilityTarget :
      (ρ σ : DHR.LocalisedEndomorphism) →
      Set

    functorConstructed :
      Bool

    functorConstructedIsFalse :
      functorConstructed ≡ false

    targetBoundary :
      List String

open DHRToG6TrackedLaneActionFunctorTarget public

record DHRToG6TrackedLaneActionFunctorSubobligations
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω where
  field
    objectMap :
      DHR.LocalisedEndomorphism →
      G6.Lane

    objectAdmissibilityTarget :
      (ρ : DHR.LocalisedEndomorphism) →
      Set

    carrierRealisationTarget :
      DHR.LocalisedEndomorphism →
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      Set

    actionRealisationTarget :
      (ρ : DHR.LocalisedEndomorphism) →
      (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      carrierRealisationTarget ρ x →
      carrierRealisationTarget
        ρ
        (G6.NontrivialTrackedLaneOperator.laneAction
          operator
          (objectMap ρ)
          x)
      →
      Set

    intertwinerCarrierActionTarget :
      (ρ σ : DHR.LocalisedEndomorphism) →
      DHR.Intertwiner ρ σ →
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      Set

    intertwinerNaturalitySquareTarget :
      (ρ σ : DHR.LocalisedEndomorphism) →
      (f : DHR.Intertwiner ρ σ) →
      (x y : G6.NontrivialTrackedLaneOperator.Carrier operator) →
      intertwinerCarrierActionTarget ρ σ f x y →
      Set

    tensorLaneCompatibilityTarget :
      (ρ σ : DHR.LocalisedEndomorphism) →
      DHR.DHRCategoryPrimitiveSurface.tensorObjectTarget
        DHR.canonicalDHRCategoryPrimitiveSurface
        ρ
        σ →
      Set

    trackedCommutationAvailable :
      G6.G6TrackedCrossLaneCommutationTheorem operator

    objectMapConstructed :
      Bool

    objectMapConstructedIsFalse :
      objectMapConstructed ≡ false

    carrierRealisationConstructed :
      Bool

    carrierRealisationConstructedIsFalse :
      carrierRealisationConstructed ≡ false

    naturalitySquareConstructed :
      Bool

    naturalitySquareConstructedIsFalse :
      naturalitySquareConstructed ≡ false

    tensorCompatibilityConstructed :
      Bool

    tensorCompatibilityConstructedIsFalse :
      tensorCompatibilityConstructed ≡ false

    subobligationBoundary :
      List String

open DHRToG6TrackedLaneActionFunctorSubobligations public

record DHRBridgeAdapterRequest
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω where
  field
    subobligations :
      DHRToG6TrackedLaneActionFunctorSubobligations operator

    exactAdapterRequestFields :
      List DHRBridgeAdapterRequestField

    objectToLaneMapTarget :
      DHR.LocalisedEndomorphism →
      G6.Lane

    intertwinerCarrierActionTarget :
      (ρ σ : DHR.LocalisedEndomorphism) →
      DHR.Intertwiner ρ σ →
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      Set

    objectToLaneMapConstructed :
      Bool

    objectToLaneMapConstructedIsFalse :
      objectToLaneMapConstructed ≡ false

    intertwinerCarrierActionConstructed :
      Bool

    intertwinerCarrierActionConstructedIsFalse :
      intertwinerCarrierActionConstructed ≡ false

    dhrBridgeAdapterClosed :
      Bool

    dhrBridgeAdapterClosedIsFalse :
      dhrBridgeAdapterClosed ≡ false

    promotesDRClassification :
      Bool

    promotesDRClassificationIsFalse :
      promotesDRClassification ≡ false

    reconstructsGaugeAssignment :
      Bool

    reconstructsGaugeAssignmentIsFalse :
      reconstructsGaugeAssignment ≡ false

    adapterBoundary :
      List String

open DHRBridgeAdapterRequest public

record DHRSectorLaneInvariantAdapterRequest
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω where
  field
    exactInvariantRequestFields :
      List DHRSectorLaneInvariantRequestField

    inspectedLocalisedEndomorphismHasSector :
      Bool

    inspectedLocalisedEndomorphismHasSectorIsTrue :
      inspectedLocalisedEndomorphismHasSector ≡ true

    inspectedLocalisedEndomorphismHasLaneInvariant :
      Bool

    inspectedLocalisedEndomorphismHasLaneInvariantIsFalse :
      inspectedLocalisedEndomorphismHasLaneInvariant ≡ false

    inspectedIntertwinerHasCarrierAction :
      Bool

    inspectedIntertwinerHasCarrierActionIsFalse :
      inspectedIntertwinerHasCarrierAction ≡ false

    sectorLaneInvariantTarget :
      DHR.LocalisedEndomorphism →
      G6.Lane →
      Set

    sectorRepresentationDataTarget :
      (ρ : DHR.LocalisedEndomorphism) →
      (lane : G6.Lane) →
      DHRSectorRepresentationData operator ρ lane

    crossLaneInvisibilityEvidenceTarget :
      {ρ : DHR.LocalisedEndomorphism} →
      {lane : G6.Lane} →
      (representation : DHRSectorRepresentationData operator ρ lane) →
      DHRCrossLaneInvisibilityEvidence operator representation

    objectLaneClassifierTarget :
      DHR.LocalisedEndomorphism →
      G6.Lane

    localisedEndomorphismCarrierSemanticsTarget :
      (ρ : DHR.LocalisedEndomorphism) →
      Hexagon.LocalisedEndomorphismCarrierSemantics
        operator
        ρ
        (objectLaneClassifierTarget ρ)

    localisedEndomorphismWitnessAdapterBoundaryTarget :
      (ρ : DHR.LocalisedEndomorphism) →
      Hexagon.LocalisedEndomorphismCarrierAdapterBoundary
        operator
        ρ
        (objectLaneClassifierTarget ρ)
        (localisedEndomorphismCarrierSemanticsTarget ρ)

    objectLaneClassifierEvidenceSurface :
      DHRSectorLaneClassifierEvidence operator

    objectClassifierInvariantEvidenceTarget :
      (ρ : DHR.LocalisedEndomorphism) →
      sectorLaneInvariantTarget ρ (objectLaneClassifierTarget ρ)

    objectToLaneMapDownstreamTarget :
      DHR.LocalisedEndomorphism →
      G6.Lane

    objectToLaneMapDownstreamAgreesWithClassifierTarget :
      (ρ : DHR.LocalisedEndomorphism) →
      objectToLaneMapDownstreamTarget ρ
      ≡
      objectLaneClassifierTarget ρ

    intertwinerPreservesLaneInvariantTarget :
      (ρ σ : DHR.LocalisedEndomorphism) →
      DHR.Intertwiner ρ σ →
      sectorLaneInvariantTarget ρ (objectLaneClassifierTarget ρ) →
      sectorLaneInvariantTarget σ (objectLaneClassifierTarget σ) →
      Set

    trackedIntertwinerCarrierActionSurfaceTarget :
      (ρ σ : DHR.LocalisedEndomorphism) →
      (f : DHR.Intertwiner ρ σ) →
      (ρInvariant :
        DHRSectorLaneInvariantRelation
          operator
          ρ
          (objectLaneClassifierTarget ρ)) →
      (σInvariant :
        DHRSectorLaneInvariantRelation
          operator
          σ
          (objectLaneClassifierTarget σ)) →
      DHRTrackedIntertwinerCarrierAction
        operator
        ρ
        σ
        f
        (objectLaneClassifierTarget ρ)
        (objectLaneClassifierTarget σ)
        ρInvariant
        σInvariant

    intertwinerTrackedCarrierSemanticsTarget :
      (ρ σ : DHR.LocalisedEndomorphism) →
      (f : DHR.Intertwiner ρ σ) →
      Hexagon.IntertwinerTrackedCarrierSemantics
        operator
        ρ
        σ
        f
        (objectLaneClassifierTarget ρ)
        (objectLaneClassifierTarget σ)
        (localisedEndomorphismCarrierSemanticsTarget ρ)
        (localisedEndomorphismCarrierSemanticsTarget σ)

    intertwinerWitnessAdapterBoundaryTarget :
      (ρ σ : DHR.LocalisedEndomorphism) →
      (f : DHR.Intertwiner ρ σ) →
      Hexagon.IntertwinerTrackedCarrierAdapterBoundary
        operator
        ρ
        σ
        f
        (objectLaneClassifierTarget ρ)
        (objectLaneClassifierTarget σ)
        (localisedEndomorphismCarrierSemanticsTarget ρ)
        (localisedEndomorphismCarrierSemanticsTarget σ)
        (intertwinerTrackedCarrierSemanticsTarget ρ σ f)

    carrierActionFromInvariantTarget :
      (ρ σ : DHR.LocalisedEndomorphism) →
      DHR.Intertwiner ρ σ →
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      Set

    feedsObjectToLaneMap :
      Bool

    feedsObjectToLaneMapIsTrue :
      feedsObjectToLaneMap ≡ true

    feedsIntertwinerCarrierAction :
      Bool

    feedsIntertwinerCarrierActionIsTrue :
      feedsIntertwinerCarrierAction ≡ true

    carrierSemanticsConstructed :
      Bool

    carrierSemanticsConstructedIsFalse :
      carrierSemanticsConstructed ≡ false

    trackedCarrierSemanticsConstructed :
      Bool

    trackedCarrierSemanticsConstructedIsFalse :
      trackedCarrierSemanticsConstructed ≡ false

    invariantConstructed :
      Bool

    invariantConstructedIsFalse :
      invariantConstructed ≡ false

    adapterClosed :
      Bool

    adapterClosedIsFalse :
      adapterClosed ≡ false

    promotesDRClassification :
      Bool

    promotesDRClassificationIsFalse :
      promotesDRClassification ≡ false

    reconstructsGaugeAssignment :
      Bool

    reconstructsGaugeAssignmentIsFalse :
      reconstructsGaugeAssignment ≡ false

    invariantBoundary :
      List String

open DHRSectorLaneInvariantAdapterRequest public

record DHRSemanticBridgeNarrowing
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω where
  field
    dhrObjectToLaneTarget :
      DHR.LocalisedEndomorphism →
      G6.Lane

    dhrIntertwinerCarrierActionTarget :
      (ρ σ : DHR.LocalisedEndomorphism) →
      DHR.Intertwiner ρ σ →
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      G6.NontrivialTrackedLaneOperator.Carrier operator →
      Set

    primeLaneDHRClassification :
      DHR.PrimeLaneDHREndomorphismClassificationReceipt

    fullDHRBoxtimesDecomposition :
      DHR.FullDHRBoxtimesDecompositionReceipt

    tannakaReconstructionTarget :
      DHR.TannakaDHRReconstructionTarget

    sectorLaneInvariantAdapterRequest :
      DHRSectorLaneInvariantAdapterRequest operator

    carrierSemanticsAbsenceLedger :
      Hexagon.DHRCarrierSemanticsAbsenceLedger operator

    localEndomorphismCarriesLaneInvariant :
      Bool

    localEndomorphismCarriesLaneInvariantIsFalse :
      localEndomorphismCarriesLaneInvariant ≡ false

    localIntertwinerCarriesTrackedAction :
      Bool

    localIntertwinerCarriesTrackedActionIsFalse :
      localIntertwinerCarriesTrackedAction ≡ false

    adapterRouteAvailableAsRequest :
      Bool

    adapterRouteAvailableAsRequestIsTrue :
      adapterRouteAvailableAsRequest ≡ true

    adapterRouteConstructed :
      Bool

    adapterRouteConstructedIsFalse :
      adapterRouteConstructed ≡ false

    drClassificationRouteAvailableAsTarget :
      Bool

    drClassificationRouteAvailableAsTargetIsTrue :
      drClassificationRouteAvailableAsTarget ≡ true

    drClassificationRouteClosedHere :
      Bool

    drClassificationRouteClosedHereIsFalse :
      drClassificationRouteClosedHere ≡ false

    objectToLaneBridgeRoute :
      DHRObjectToLaneBridgeRoute

    objectToLaneBridgeRouteIsAdapterRequest :
      objectToLaneBridgeRoute
      ≡
      objectToLaneMayBeAdapterSuppliedFailClosed

    intertwinerCarrierActionBridgeRoute :
      DHRIntertwinerCarrierActionBridgeRoute

    intertwinerCarrierActionBridgeRouteIsAdapterRequest :
      intertwinerCarrierActionBridgeRoute
      ≡
      intertwinerCarrierActionMayBeAdapterSuppliedFailClosed

    firstBlocker :
      DHRSemanticBridgeFirstBlocker

    firstBlockerIsNoSectorLaneInvariant :
      firstBlocker
      ≡
      firstBlockerNoSectorLaneInvariantOnLocalisedEndomorphism

    bridgeClosed :
      Bool

    bridgeClosedIsFalse :
      bridgeClosed ≡ false

    promotesDRClassification :
      Bool

    promotesDRClassificationIsFalse :
      promotesDRClassification ≡ false

    reconstructsGaugeAssignment :
      Bool

    reconstructsGaugeAssignmentIsFalse :
      reconstructsGaugeAssignment ≡ false

    narrowingBoundary :
      List String

open DHRSemanticBridgeNarrowing public

postulate
  abstractDHRToG6ObjectMapTarget :
    DHR.LocalisedEndomorphism →
    G6.Lane

  abstractDHRToG6ActionCompatibilityTarget :
    (ρ : DHR.LocalisedEndomorphism) →
    Set

  abstractDHRToG6IntertwinerNaturalityTarget :
    (ρ σ : DHR.LocalisedEndomorphism) →
    DHR.Intertwiner ρ σ →
    Set

  abstractDHRToG6TensorCompatibilityTarget :
    (ρ σ : DHR.LocalisedEndomorphism) →
    Set

  abstractDHRToG6CarrierRealisationTarget :
    (operator : G6.NontrivialTrackedLaneOperator) →
    DHR.LocalisedEndomorphism →
    G6.NontrivialTrackedLaneOperator.Carrier operator →
    Set

  abstractDHRToG6ActionRealisationTarget :
    (operator : G6.NontrivialTrackedLaneOperator) →
    (ρ : DHR.LocalisedEndomorphism) →
    (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
    abstractDHRToG6CarrierRealisationTarget operator ρ x →
    abstractDHRToG6CarrierRealisationTarget
      operator
      ρ
      (G6.NontrivialTrackedLaneOperator.laneAction
        operator
        (abstractDHRToG6ObjectMapTarget ρ)
        x)
    →
    Set

  abstractDHRToG6IntertwinerCarrierActionTarget :
    (operator : G6.NontrivialTrackedLaneOperator) →
    (ρ σ : DHR.LocalisedEndomorphism) →
    DHR.Intertwiner ρ σ →
    G6.NontrivialTrackedLaneOperator.Carrier operator →
    G6.NontrivialTrackedLaneOperator.Carrier operator →
    Set

  abstractDHRToG6IntertwinerNaturalitySquareTarget :
    (operator : G6.NontrivialTrackedLaneOperator) →
    (ρ σ : DHR.LocalisedEndomorphism) →
    (f : DHR.Intertwiner ρ σ) →
    (x y : G6.NontrivialTrackedLaneOperator.Carrier operator) →
    abstractDHRToG6IntertwinerCarrierActionTarget operator ρ σ f x y →
    Set

  abstractDHRToG6TensorLaneCompatibilityTarget :
    (operator : G6.NontrivialTrackedLaneOperator) →
    (ρ σ : DHR.LocalisedEndomorphism) →
    DHR.DHRCategoryPrimitiveSurface.tensorObjectTarget
      DHR.canonicalDHRCategoryPrimitiveSurface
      ρ
      σ →
    Set

  abstractDHRSectorLaneInvariantObjectClassifierTarget :
    DHR.LocalisedEndomorphism →
    G6.Lane

  abstractDHRSectorRepresentationDataTarget :
    (operator : G6.NontrivialTrackedLaneOperator) →
    (ρ : DHR.LocalisedEndomorphism) →
    (lane : G6.Lane) →
    DHRSectorRepresentationData operator ρ lane

  abstractDHRCrossLaneInvisibilityEvidenceTarget :
    (operator : G6.NontrivialTrackedLaneOperator) →
    {ρ : DHR.LocalisedEndomorphism} →
    {lane : G6.Lane} →
    (representation : DHRSectorRepresentationData operator ρ lane) →
    DHRCrossLaneInvisibilityEvidence operator representation

  abstractDHRLocalisedEndomorphismCarrierSemanticsTarget :
    (operator : G6.NontrivialTrackedLaneOperator) →
    (ρ : DHR.LocalisedEndomorphism) →
    Hexagon.LocalisedEndomorphismCarrierSemantics
      operator
      ρ
      (abstractDHRSectorLaneInvariantObjectClassifierTarget ρ)

  abstractDHRSectorLaneInvariantClassifierEvidenceTarget :
    (operator : G6.NontrivialTrackedLaneOperator) →
    (ρ : DHR.LocalisedEndomorphism) →
    DHRSectorLaneInvariantRelation
      operator
      ρ
      (abstractDHRSectorLaneInvariantObjectClassifierTarget ρ)

  abstractDHRSectorLaneInvariantObjectMapDownstreamTarget :
    DHR.LocalisedEndomorphism →
    G6.Lane

  abstractDHRSectorLaneInvariantObjectMapAgreesTarget :
    (ρ : DHR.LocalisedEndomorphism) →
    abstractDHRSectorLaneInvariantObjectMapDownstreamTarget ρ
    ≡
    abstractDHRSectorLaneInvariantObjectClassifierTarget ρ

  abstractDHRSectorLaneClassifierEvidenceTarget :
    (operator : G6.NontrivialTrackedLaneOperator) →
    DHRSectorLaneClassifierEvidence operator

  abstractDHRTrackedIntertwinerCarrierActionSurfaceTarget :
    (operator : G6.NontrivialTrackedLaneOperator) →
    (ρ σ : DHR.LocalisedEndomorphism) →
    (f : DHR.Intertwiner ρ σ) →
    (ρInvariant :
      DHRSectorLaneInvariantRelation
        operator
        ρ
        (abstractDHRSectorLaneInvariantObjectClassifierTarget ρ)) →
    (σInvariant :
      DHRSectorLaneInvariantRelation
        operator
        σ
        (abstractDHRSectorLaneInvariantObjectClassifierTarget σ)) →
    DHRTrackedIntertwinerCarrierAction
      operator
      ρ
      σ
      f
      (abstractDHRSectorLaneInvariantObjectClassifierTarget ρ)
      (abstractDHRSectorLaneInvariantObjectClassifierTarget σ)
      ρInvariant
      σInvariant

  abstractDHRIntertwinerTrackedCarrierSemanticsTarget :
    (operator : G6.NontrivialTrackedLaneOperator) →
    (ρ σ : DHR.LocalisedEndomorphism) →
    (f : DHR.Intertwiner ρ σ) →
    Hexagon.IntertwinerTrackedCarrierSemantics
      operator
      ρ
      σ
      f
      (abstractDHRSectorLaneInvariantObjectClassifierTarget ρ)
      (abstractDHRSectorLaneInvariantObjectClassifierTarget σ)
      (abstractDHRLocalisedEndomorphismCarrierSemanticsTarget operator ρ)
      (abstractDHRLocalisedEndomorphismCarrierSemanticsTarget operator σ)

  abstractDHRCarrierActionFromSectorLaneInvariantTarget :
    (operator : G6.NontrivialTrackedLaneOperator) →
    (ρ σ : DHR.LocalisedEndomorphism) →
    DHR.Intertwiner ρ σ →
    G6.NontrivialTrackedLaneOperator.Carrier operator →
    G6.NontrivialTrackedLaneOperator.Carrier operator →
    Set

  abstractDHRSelectedCarrierPredicateTarget :
    (operator : G6.NontrivialTrackedLaneOperator) →
    DHR.LocalisedEndomorphism →
    G6.Lane →
    G6.NontrivialTrackedLaneOperator.Carrier operator →
    Bool

  abstractDHRSelectedCarrierNonemptyEvidenceTarget :
    (operator : G6.NontrivialTrackedLaneOperator) →
    DHR.LocalisedEndomorphism →
    G6.Lane →
    Set

  abstractDHRGlobalForeignLaneActionIdentityTarget :
    (operator : G6.NontrivialTrackedLaneOperator) →
    (ρ : DHR.LocalisedEndomorphism) →
    (lane otherLane : G6.Lane) →
    lane ≢ otherLane →
    (x : G6.NontrivialTrackedLaneOperator.Carrier operator) →
    abstractDHRSelectedCarrierPredicateTarget operator ρ lane x ≡ true →
    G6.NontrivialTrackedLaneOperator.laneAction
      operator
      otherLane
      x
    ≡
    x

  abstractDHRTrackedIntertwinerCarrierActionBoolTarget :
    (operator : G6.NontrivialTrackedLaneOperator) →
    (ρ σ : DHR.LocalisedEndomorphism) →
    DHR.Intertwiner ρ σ →
    G6.NontrivialTrackedLaneOperator.Carrier operator →
    G6.NontrivialTrackedLaneOperator.Carrier operator →
    Bool

  abstractDHRTrackedCarrierActionPreservationTarget :
    (operator : G6.NontrivialTrackedLaneOperator) →
    (ρ σ : DHR.LocalisedEndomorphism) →
    (f : DHR.Intertwiner ρ σ) →
    (ρLane σLane : G6.Lane) →
    (x y : G6.NontrivialTrackedLaneOperator.Carrier operator) →
    abstractDHRSelectedCarrierPredicateTarget operator ρ ρLane x ≡ true →
    abstractDHRTrackedIntertwinerCarrierActionBoolTarget
      operator
      ρ
      σ
      f
      x
      y
    ≡
    true →
    abstractDHRSelectedCarrierPredicateTarget operator σ σLane y ≡ true

  abstractDHRTrackedCarrierActionForeignLaneInvisibilityTarget :
    (operator : G6.NontrivialTrackedLaneOperator) →
    (ρ σ : DHR.LocalisedEndomorphism) →
    (f : DHR.Intertwiner ρ σ) →
    (ρLane σLane otherLane : G6.Lane) →
    ρLane ≢ otherLane →
    σLane ≢ otherLane →
    Bool

  abstractDHRNondegenerateLocalisedExternalInterfaceTarget :
    (operator : G6.NontrivialTrackedLaneOperator) →
    (ρ : DHR.LocalisedEndomorphism) →
    (lane : G6.Lane) →
    Hexagon.NondegenerateLocalisedEndomorphismCarrierSemanticsInterface
      operator
      ρ
      lane

  abstractDHRNondegenerateIntertwinerExternalInterfaceTarget :
    (operator : G6.NontrivialTrackedLaneOperator) →
    (ρ σ : DHR.LocalisedEndomorphism) →
    (f : DHR.Intertwiner ρ σ) →
    (ρLane σLane : G6.Lane) →
    Hexagon.NondegenerateIntertwinerTrackedCarrierSemanticsInterface
      operator
      ρ
      σ
      f
      ρLane
      σLane
      (abstractDHRNondegenerateLocalisedExternalInterfaceTarget
        operator
        ρ
        ρLane)
      (abstractDHRNondegenerateLocalisedExternalInterfaceTarget
        operator
        σ
        σLane)

concreteDHRIntertwinerPreservesSectorLaneInvariantTarget :
  (operator : G6.NontrivialTrackedLaneOperator) →
  (ρ σ : DHR.LocalisedEndomorphism) →
  DHR.Intertwiner ρ σ →
  DHRSectorLaneInvariantRelation
    operator
    ρ
    (abstractDHRSectorLaneInvariantObjectClassifierTarget ρ) →
  DHRSectorLaneInvariantRelation
    operator
    σ
    (abstractDHRSectorLaneInvariantObjectClassifierTarget σ) →
  Set
concreteDHRIntertwinerPreservesSectorLaneInvariantTarget
  operator ρ σ f ρInvariant σInvariant =
  DHRIntertwinerPreservesSectorLaneInvariantRelation
    operator
    ρ
    σ
    f
    (abstractDHRSectorLaneInvariantObjectClassifierTarget ρ)
    (abstractDHRSectorLaneInvariantObjectClassifierTarget σ)
    ρInvariant
    σInvariant

canonicalDHRToG6TrackedLaneActionFunctorTarget :
  DHRToG6TrackedLaneActionFunctorTarget
canonicalDHRToG6TrackedLaneActionFunctorTarget =
  record
    { objectMapTarget =
        abstractDHRToG6ObjectMapTarget
    ; actionCompatibilityTarget =
        abstractDHRToG6ActionCompatibilityTarget
    ; intertwinerNaturalityTarget =
        abstractDHRToG6IntertwinerNaturalityTarget
    ; tensorCompatibilityTarget =
        abstractDHRToG6TensorCompatibilityTarget
    ; functorConstructed =
        false
    ; functorConstructedIsFalse =
        refl
    ; targetBoundary =
        "This target would map DHR LocalisedEndomorphism objects to tracked G6 lanes"
        ∷ "It would prove that DHR intertwiners are natural for the tracked FactorVec lane-action commutation"
        ∷ "It would prove tensor compatibility before any FactorVec associativity proof can be read as a DHR hexagon"
        ∷ "No such functor is constructed here"
        ∷ []
    }

canonicalDHRToG6TrackedLaneActionFunctorSubobligations :
  DHRToG6TrackedLaneActionFunctorSubobligations
    (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
      (G6K.G6TrackedKostantRoute.officialTrackedTheorem
        G6K.canonicalG6TrackedKostantRoute))
canonicalDHRToG6TrackedLaneActionFunctorSubobligations =
  record
    { objectMap =
        abstractDHRToG6ObjectMapTarget
    ; objectAdmissibilityTarget =
        abstractDHRToG6ActionCompatibilityTarget
    ; carrierRealisationTarget =
        abstractDHRToG6CarrierRealisationTarget
          (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
            (G6K.G6TrackedKostantRoute.officialTrackedTheorem
              G6K.canonicalG6TrackedKostantRoute))
    ; actionRealisationTarget =
        abstractDHRToG6ActionRealisationTarget
          (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
            (G6K.G6TrackedKostantRoute.officialTrackedTheorem
              G6K.canonicalG6TrackedKostantRoute))
    ; intertwinerCarrierActionTarget =
        abstractDHRToG6IntertwinerCarrierActionTarget
          (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
            (G6K.G6TrackedKostantRoute.officialTrackedTheorem
              G6K.canonicalG6TrackedKostantRoute))
    ; intertwinerNaturalitySquareTarget =
        abstractDHRToG6IntertwinerNaturalitySquareTarget
          (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
            (G6K.G6TrackedKostantRoute.officialTrackedTheorem
              G6K.canonicalG6TrackedKostantRoute))
    ; tensorLaneCompatibilityTarget =
        abstractDHRToG6TensorLaneCompatibilityTarget
          (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
            (G6K.G6TrackedKostantRoute.officialTrackedTheorem
              G6K.canonicalG6TrackedKostantRoute))
    ; trackedCommutationAvailable =
        G6K.G6TrackedKostantRoute.trackedActionCommutation
          G6K.canonicalG6TrackedKostantRoute
    ; objectMapConstructed =
        false
    ; objectMapConstructedIsFalse =
        refl
    ; carrierRealisationConstructed =
        false
    ; carrierRealisationConstructedIsFalse =
        refl
    ; naturalitySquareConstructed =
        false
    ; naturalitySquareConstructedIsFalse =
        refl
    ; tensorCompatibilityConstructed =
        false
    ; tensorCompatibilityConstructedIsFalse =
        refl
    ; subobligationBoundary =
        "The tracked G6 theorem supplies lane actions on its official carrier"
        ∷ "A DHR bridge still needs an object map from LocalisedEndomorphism to G6.Lane"
        ∷ "It also needs a carrier realisation of each DHR object inside the tracked G6 carrier"
        ∷ "Each DHR Intertwiner must act on the tracked carrier before a naturality square can be stated as a proof"
        ∷ "Tensor compatibility must compare the DHR tensor-object socket with the mapped G6 lane action"
        ∷ "These are target subobligations only; no functor is constructed"
        ∷ []
    }

canonicalDHRBridgeAdapterRequest :
  DHRBridgeAdapterRequest
    (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
      (G6K.G6TrackedKostantRoute.officialTrackedTheorem
        G6K.canonicalG6TrackedKostantRoute))
canonicalDHRBridgeAdapterRequest =
  record
    { subobligations =
        canonicalDHRToG6TrackedLaneActionFunctorSubobligations
    ; exactAdapterRequestFields =
        canonicalDHRBridgeAdapterRequestFields
    ; objectToLaneMapTarget =
        DHRToG6TrackedLaneActionFunctorSubobligations.objectMap
          canonicalDHRToG6TrackedLaneActionFunctorSubobligations
    ; intertwinerCarrierActionTarget =
        DHRToG6TrackedLaneActionFunctorSubobligations.intertwinerCarrierActionTarget
          canonicalDHRToG6TrackedLaneActionFunctorSubobligations
    ; objectToLaneMapConstructed =
        false
    ; objectToLaneMapConstructedIsFalse =
        refl
    ; intertwinerCarrierActionConstructed =
        false
    ; intertwinerCarrierActionConstructedIsFalse =
        refl
    ; dhrBridgeAdapterClosed =
        false
    ; dhrBridgeAdapterClosedIsFalse =
        refl
    ; promotesDRClassification =
        false
    ; promotesDRClassificationIsFalse =
        refl
    ; reconstructsGaugeAssignment =
        false
    ; reconstructsGaugeAssignmentIsFalse =
        refl
    ; adapterBoundary =
        "Exact adapter request field 1: objectToLaneMap : DHR.LocalisedEndomorphism -> G6.Lane"
        ∷ "Exact adapter request field 2: intertwinerCarrierAction : (rho sigma : DHR.LocalisedEndomorphism) -> DHR.Intertwiner rho sigma -> Carrier -> Carrier -> Set"
        ∷ "The existing lane-dimension and DHR gauge surfaces do not supply a semantic object-to-lane map"
        ∷ "The tracked G6 carrier action is available, but no DHR Intertwiner action on that carrier is constructed"
        ∷ "This request is fail-closed and does not promote DR classification or gauge reconstruction"
        ∷ []
    }

canonicalDHRSectorLaneInvariantAdapterRequest :
  DHRSectorLaneInvariantAdapterRequest
    (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
      (G6K.G6TrackedKostantRoute.officialTrackedTheorem
        G6K.canonicalG6TrackedKostantRoute))
canonicalDHRSectorLaneInvariantAdapterRequest =
  record
    { exactInvariantRequestFields =
        canonicalDHRSectorLaneInvariantRequestFields
    ; inspectedLocalisedEndomorphismHasSector =
        true
    ; inspectedLocalisedEndomorphismHasSectorIsTrue =
        refl
    ; inspectedLocalisedEndomorphismHasLaneInvariant =
        false
    ; inspectedLocalisedEndomorphismHasLaneInvariantIsFalse =
        refl
    ; inspectedIntertwinerHasCarrierAction =
        false
    ; inspectedIntertwinerHasCarrierActionIsFalse =
        refl
    ; sectorLaneInvariantTarget =
        DHRSectorLaneInvariantRelation
          (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
            (G6K.G6TrackedKostantRoute.officialTrackedTheorem
              G6K.canonicalG6TrackedKostantRoute))
    ; sectorRepresentationDataTarget =
        abstractDHRSectorRepresentationDataTarget
          (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
            (G6K.G6TrackedKostantRoute.officialTrackedTheorem
              G6K.canonicalG6TrackedKostantRoute))
    ; crossLaneInvisibilityEvidenceTarget =
        abstractDHRCrossLaneInvisibilityEvidenceTarget
          (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
            (G6K.G6TrackedKostantRoute.officialTrackedTheorem
              G6K.canonicalG6TrackedKostantRoute))
    ; objectLaneClassifierTarget =
        abstractDHRSectorLaneInvariantObjectClassifierTarget
    ; localisedEndomorphismCarrierSemanticsTarget =
        abstractDHRLocalisedEndomorphismCarrierSemanticsTarget
          (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
            (G6K.G6TrackedKostantRoute.officialTrackedTheorem
              G6K.canonicalG6TrackedKostantRoute))
    ; localisedEndomorphismWitnessAdapterBoundaryTarget =
        λ ρ →
          Hexagon.localisedEndomorphismCarrierAdapterBoundaryFromSemantics
            (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
              (G6K.G6TrackedKostantRoute.officialTrackedTheorem
                G6K.canonicalG6TrackedKostantRoute))
            ρ
            (abstractDHRSectorLaneInvariantObjectClassifierTarget ρ)
            (abstractDHRLocalisedEndomorphismCarrierSemanticsTarget
              (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
                (G6K.G6TrackedKostantRoute.officialTrackedTheorem
                  G6K.canonicalG6TrackedKostantRoute))
              ρ)
    ; objectLaneClassifierEvidenceSurface =
        abstractDHRSectorLaneClassifierEvidenceTarget
          (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
            (G6K.G6TrackedKostantRoute.officialTrackedTheorem
              G6K.canonicalG6TrackedKostantRoute))
    ; objectClassifierInvariantEvidenceTarget =
        abstractDHRSectorLaneInvariantClassifierEvidenceTarget
          (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
            (G6K.G6TrackedKostantRoute.officialTrackedTheorem
              G6K.canonicalG6TrackedKostantRoute))
    ; objectToLaneMapDownstreamTarget =
        abstractDHRSectorLaneInvariantObjectMapDownstreamTarget
    ; objectToLaneMapDownstreamAgreesWithClassifierTarget =
        abstractDHRSectorLaneInvariantObjectMapAgreesTarget
    ; intertwinerPreservesLaneInvariantTarget =
        concreteDHRIntertwinerPreservesSectorLaneInvariantTarget
          (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
            (G6K.G6TrackedKostantRoute.officialTrackedTheorem
              G6K.canonicalG6TrackedKostantRoute))
    ; trackedIntertwinerCarrierActionSurfaceTarget =
        abstractDHRTrackedIntertwinerCarrierActionSurfaceTarget
          (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
            (G6K.G6TrackedKostantRoute.officialTrackedTheorem
              G6K.canonicalG6TrackedKostantRoute))
    ; intertwinerTrackedCarrierSemanticsTarget =
        abstractDHRIntertwinerTrackedCarrierSemanticsTarget
          (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
            (G6K.G6TrackedKostantRoute.officialTrackedTheorem
              G6K.canonicalG6TrackedKostantRoute))
    ; intertwinerWitnessAdapterBoundaryTarget =
        λ ρ σ f →
          Hexagon.intertwinerTrackedCarrierAdapterBoundaryFromSemantics
            (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
              (G6K.G6TrackedKostantRoute.officialTrackedTheorem
                G6K.canonicalG6TrackedKostantRoute))
            ρ
            σ
            f
            (abstractDHRSectorLaneInvariantObjectClassifierTarget ρ)
            (abstractDHRSectorLaneInvariantObjectClassifierTarget σ)
            (abstractDHRLocalisedEndomorphismCarrierSemanticsTarget
              (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
                (G6K.G6TrackedKostantRoute.officialTrackedTheorem
                  G6K.canonicalG6TrackedKostantRoute))
              ρ)
            (abstractDHRLocalisedEndomorphismCarrierSemanticsTarget
              (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
                (G6K.G6TrackedKostantRoute.officialTrackedTheorem
                  G6K.canonicalG6TrackedKostantRoute))
              σ)
            (abstractDHRIntertwinerTrackedCarrierSemanticsTarget
              (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
                (G6K.G6TrackedKostantRoute.officialTrackedTheorem
                  G6K.canonicalG6TrackedKostantRoute))
              ρ
              σ
              f)
    ; carrierActionFromInvariantTarget =
        abstractDHRCarrierActionFromSectorLaneInvariantTarget
          (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
            (G6K.G6TrackedKostantRoute.officialTrackedTheorem
              G6K.canonicalG6TrackedKostantRoute))
    ; feedsObjectToLaneMap =
        true
    ; feedsObjectToLaneMapIsTrue =
        refl
    ; feedsIntertwinerCarrierAction =
        true
    ; feedsIntertwinerCarrierActionIsTrue =
        refl
    ; carrierSemanticsConstructed =
        false
    ; carrierSemanticsConstructedIsFalse =
        refl
    ; trackedCarrierSemanticsConstructed =
        false
    ; trackedCarrierSemanticsConstructedIsFalse =
        refl
    ; invariantConstructed =
        false
    ; invariantConstructedIsFalse =
        refl
    ; adapterClosed =
        false
    ; adapterClosedIsFalse =
        refl
    ; promotesDRClassification =
        false
    ; promotesDRClassificationIsFalse =
        refl
    ; reconstructsGaugeAssignment =
        false
    ; reconstructsGaugeAssignmentIsFalse =
        refl
    ; invariantBoundary =
        "Inspection result: DHR.LocalisedEndomorphism has localisedSector, localisationRegion, endomorphismAction, and localisation targets, but no lane invariant"
        ∷ "Inspection result: DHR.Intertwiner has supportRegion, arrowCarrier, intertwining law target, and unitary transport target, but no tracked G6 carrier action"
        ∷ "Narrowed relation: DHRSectorDefinition records sector, assignedLane, representationUnderLaneTarget, and crossLaneInvisibilityTarget on the tracked G6 carrier"
        ∷ "Narrowed record surface: DHRSectorRepresentationData separates sector/lane/predicate data from DHRCrossLaneInvisibilityEvidence"
        ∷ "Primitive obligation surface: Hexagon.LocalisedEndomorphismCarrierSemantics packages the carrier predicate, assigned-lane preservation, and cross-lane invisibility for each DHR object"
        ∷ "Witness adapter boundary: Hexagon.LocalisedEndomorphismCarrierAdapterBoundary carries only the DHR.LocalisedEndomorphism sector/action witnesses plus the requested carrier semantics"
        ∷ "Narrowed classifier surface: DHRSectorLaneClassifierEvidence packages objectLaneClassifier with per-object invariant evidence and downstream map agreement"
        ∷ "Narrowed intertwiner surface: DHRTrackedIntertwinerCarrierAction packages the tracked carrier relation and preservation of source/target sector predicates"
        ∷ "Primitive obligation surface: Hexagon.IntertwinerTrackedCarrierSemantics packages the tracked carrier action against source and target LocalisedEndomorphismCarrierSemantics"
        ∷ "Witness adapter boundary: Hexagon.IntertwinerTrackedCarrierAdapterBoundary carries only the DHR.Intertwiner arrow-carrier and unitary-transport sockets plus the tracked carrier semantics"
        ∷ "Smallest request: inhabit DHRSectorLaneInvariantRelation for each LocalisedEndomorphism and an object classifier carrying evidence of that invariant"
        ∷ "The classifier feeds objectToLaneMap by definitional agreement, not by DR promotion or Standard Model gauge reconstruction"
        ∷ "Intertwiner preservation now explicitly requests an action on the sector representation and invisibility under non-assigned lanes"
        ∷ "This surface requests the invariant only; it does not construct the invariant, close the adapter, or promote DHR/DR/hexagon claims"
        ∷ []
    }

canonicalDHRSemanticBridgeNarrowing :
  DHRSemanticBridgeNarrowing
    (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
      (G6K.G6TrackedKostantRoute.officialTrackedTheorem
        G6K.canonicalG6TrackedKostantRoute))
canonicalDHRSemanticBridgeNarrowing =
  record
    { dhrObjectToLaneTarget =
        abstractDHRToG6ObjectMapTarget
    ; dhrIntertwinerCarrierActionTarget =
        abstractDHRToG6IntertwinerCarrierActionTarget
          (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
            (G6K.G6TrackedKostantRoute.officialTrackedTheorem
              G6K.canonicalG6TrackedKostantRoute))
    ; primeLaneDHRClassification =
        DHR.canonicalPrimeLaneDHREndomorphismClassificationReceipt
    ; fullDHRBoxtimesDecomposition =
        DHR.canonicalFullDHRBoxtimesDecompositionReceipt
    ; tannakaReconstructionTarget =
        DHR.canonicalTannakaDHRReconstructionTarget
    ; sectorLaneInvariantAdapterRequest =
        canonicalDHRSectorLaneInvariantAdapterRequest
    ; carrierSemanticsAbsenceLedger =
        Hexagon.dhrCarrierSemanticsAbsenceLedgerFromG6
          (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
            (G6K.G6TrackedKostantRoute.officialTrackedTheorem
              G6K.canonicalG6TrackedKostantRoute))
    ; localEndomorphismCarriesLaneInvariant =
        false
    ; localEndomorphismCarriesLaneInvariantIsFalse =
        refl
    ; localIntertwinerCarriesTrackedAction =
        false
    ; localIntertwinerCarriesTrackedActionIsFalse =
        refl
    ; adapterRouteAvailableAsRequest =
        true
    ; adapterRouteAvailableAsRequestIsTrue =
        refl
    ; adapterRouteConstructed =
        false
    ; adapterRouteConstructedIsFalse =
        refl
    ; drClassificationRouteAvailableAsTarget =
        true
    ; drClassificationRouteAvailableAsTargetIsTrue =
        refl
    ; drClassificationRouteClosedHere =
        false
    ; drClassificationRouteClosedHereIsFalse =
        refl
    ; objectToLaneBridgeRoute =
        objectToLaneMayBeAdapterSuppliedFailClosed
    ; objectToLaneBridgeRouteIsAdapterRequest =
        refl
    ; intertwinerCarrierActionBridgeRoute =
        intertwinerCarrierActionMayBeAdapterSuppliedFailClosed
    ; intertwinerCarrierActionBridgeRouteIsAdapterRequest =
        refl
    ; firstBlocker =
        firstBlockerNoSectorLaneInvariantOnLocalisedEndomorphism
    ; firstBlockerIsNoSectorLaneInvariant =
        refl
    ; bridgeClosed =
        false
    ; bridgeClosedIsFalse =
        refl
    ; promotesDRClassification =
        false
    ; promotesDRClassificationIsFalse =
        refl
    ; reconstructsGaugeAssignment =
        false
    ; reconstructsGaugeAssignmentIsFalse =
        refl
    ; narrowingBoundary =
        "LocalisedEndomorphism exposes sector, region, action, and localisation targets, but no inhabited sector-lane invariant or lane classifier"
        ∷ "Intertwiner exposes a support region, observable arrow carrier, and law targets, but no action on the tracked G6 carrier"
        ∷ "Absence ledger result: DHR object semantics is first blocked by the missing carrier predicate; assigned-lane predicate preservation is blocked behind that predicate"
        ∷ "Absence ledger result: G6 tracked locality is available only as tracked-prime and outside-basis coordinate preservation, not the global foreign-lane action identity required by the DHR carrier semantics record"
        ∷ "Absence ledger result: DHR intertwiner semantics is first blocked by the missing tracked carrier action, with tracked preservation and foreign-lane invisibility behind that action"
        ∷ "The narrowed first primitives are assigned lane, representation under that lane, cross-lane invisibility, and intertwiner representation action"
        ∷ "The DR/prime-lane classification route exists only as conditional targets: prime-lane DHR classification, boxtimes decomposition, and Tannaka reconstruction"
        ∷ "Therefore objectToLaneMap can be supplied as an explicit fail-closed adapter now, or derived later from the DR classification route once that route is inhabited"
        ∷ "This narrowing constructs neither adapter field and does not close the DHR bridge, DR classification, gauge reconstruction, or symmetric hexagon"
        ∷ []
    }

canonicalDHRNondegenerateCarrierSemanticsExtensionRequest :
  DHRNondegenerateCarrierSemanticsExtensionRequest
    (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
      (G6K.G6TrackedKostantRoute.officialTrackedTheorem
        G6K.canonicalG6TrackedKostantRoute))
canonicalDHRNondegenerateCarrierSemanticsExtensionRequest =
  record
    { degenerateWitnessAvailable =
        Hexagon.degenerateLocalisedEndomorphismCarrierSemanticsReceipt
          (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
            (G6K.G6TrackedKostantRoute.officialTrackedTheorem
              G6K.canonicalG6TrackedKostantRoute))
    ; g6TrackedLocalisedCarrierSemanticsAttemptTarget =
        Hexagon.g6TrackedLocalisedCarrierSemanticsAttempt
          (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
            (G6K.G6TrackedKostantRoute.officialTrackedTheorem
              G6K.canonicalG6TrackedKostantRoute))
    ; finalLocalisedSuppliedInterfaceAbsenceLedger =
        Hexagon.finalNondegenerateLocalisedCarrierSuppliedInterfaceAbsenceLedger
          (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
            (G6K.G6TrackedKostantRoute.officialTrackedTheorem
              G6K.canonicalG6TrackedKostantRoute))
    ; exactExtensionFields =
        canonicalDHRNondegenerateCarrierSemanticsExtensionFields
    ; selectedCarrierPredicateTarget =
        abstractDHRSelectedCarrierPredicateTarget
          (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
            (G6K.G6TrackedKostantRoute.officialTrackedTheorem
              G6K.canonicalG6TrackedKostantRoute))
    ; selectedCarrierNonemptyEvidenceTarget =
        abstractDHRSelectedCarrierNonemptyEvidenceTarget
          (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
            (G6K.G6TrackedKostantRoute.officialTrackedTheorem
              G6K.canonicalG6TrackedKostantRoute))
    ; globalForeignLaneActionIdentityTarget =
        abstractDHRGlobalForeignLaneActionIdentityTarget
          (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
            (G6K.G6TrackedKostantRoute.officialTrackedTheorem
              G6K.canonicalG6TrackedKostantRoute))
    ; trackedIntertwinerCarrierActionTarget =
        abstractDHRTrackedIntertwinerCarrierActionBoolTarget
          (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
            (G6K.G6TrackedKostantRoute.officialTrackedTheorem
              G6K.canonicalG6TrackedKostantRoute))
    ; trackedCarrierActionPreservationTarget =
        abstractDHRTrackedCarrierActionPreservationTarget
          (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
            (G6K.G6TrackedKostantRoute.officialTrackedTheorem
              G6K.canonicalG6TrackedKostantRoute))
    ; trackedCarrierActionForeignLaneInvisibilityTarget =
        abstractDHRTrackedCarrierActionForeignLaneInvisibilityTarget
          (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
            (G6K.G6TrackedKostantRoute.officialTrackedTheorem
              G6K.canonicalG6TrackedKostantRoute))
    ; nondegenerateLocalisedExternalInterfaceTarget =
        abstractDHRNondegenerateLocalisedExternalInterfaceTarget
          (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
            (G6K.G6TrackedKostantRoute.officialTrackedTheorem
              G6K.canonicalG6TrackedKostantRoute))
    ; nondegenerateLocalisedExternalAdapterBoundaryTarget =
        λ ρ lane →
          Hexagon.nondegenerateLocalisedInterfaceToAdapterBoundary
            (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
              (G6K.G6TrackedKostantRoute.officialTrackedTheorem
                G6K.canonicalG6TrackedKostantRoute))
            ρ
            lane
            (abstractDHRNondegenerateLocalisedExternalInterfaceTarget
              (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
                (G6K.G6TrackedKostantRoute.officialTrackedTheorem
                  G6K.canonicalG6TrackedKostantRoute))
              ρ
              lane)
    ; nondegenerateIntertwinerExternalInterfaceTarget =
        λ ρ σ f ρLane σLane →
          Hexagon.targetSelectedNondegenerateIntertwinerTrackedCarrierSemanticsInterface
            (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
              (G6K.G6TrackedKostantRoute.officialTrackedTheorem
                G6K.canonicalG6TrackedKostantRoute))
            ρ
            σ
            f
            ρLane
            σLane
            (abstractDHRNondegenerateLocalisedExternalInterfaceTarget
              (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
                (G6K.G6TrackedKostantRoute.officialTrackedTheorem
                  G6K.canonicalG6TrackedKostantRoute))
              ρ
              ρLane)
            (abstractDHRNondegenerateLocalisedExternalInterfaceTarget
              (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
                (G6K.G6TrackedKostantRoute.officialTrackedTheorem
                  G6K.canonicalG6TrackedKostantRoute))
              σ
              σLane)
    ; conditionalIntertwinerInterfaceFromLocalInterfacesAvailable =
        true
    ; conditionalIntertwinerInterfaceFromLocalInterfacesAvailableIsTrue =
        refl
    ; nondegenerateIntertwinerExternalAdapterBoundaryTarget =
        λ ρ σ f ρLane σLane →
          Hexagon.nondegenerateIntertwinerInterfaceToAdapterBoundary
            (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
              (G6K.G6TrackedKostantRoute.officialTrackedTheorem
                G6K.canonicalG6TrackedKostantRoute))
            ρ
            σ
            f
            ρLane
            σLane
            (abstractDHRNondegenerateLocalisedExternalInterfaceTarget
              (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
                (G6K.G6TrackedKostantRoute.officialTrackedTheorem
                  G6K.canonicalG6TrackedKostantRoute))
              ρ
              ρLane)
            (abstractDHRNondegenerateLocalisedExternalInterfaceTarget
              (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
                (G6K.G6TrackedKostantRoute.officialTrackedTheorem
                  G6K.canonicalG6TrackedKostantRoute))
              σ
              σLane)
            (Hexagon.targetSelectedNondegenerateIntertwinerTrackedCarrierSemanticsInterface
              (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
                (G6K.G6TrackedKostantRoute.officialTrackedTheorem
                  G6K.canonicalG6TrackedKostantRoute))
              ρ
              σ
              f
              ρLane
              σLane
              (abstractDHRNondegenerateLocalisedExternalInterfaceTarget
                (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
                  (G6K.G6TrackedKostantRoute.officialTrackedTheorem
                    G6K.canonicalG6TrackedKostantRoute))
                ρ
                ρLane)
              (abstractDHRNondegenerateLocalisedExternalInterfaceTarget
                (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
                  (G6K.G6TrackedKostantRoute.officialTrackedTheorem
                    G6K.canonicalG6TrackedKostantRoute))
                σ
                σLane))
    ; degenerateWitnessConstructed =
        true
    ; degenerateWitnessConstructedIsTrue =
        refl
    ; nondegenerateCarrierPredicateConstructed =
        false
    ; nondegenerateCarrierPredicateConstructedIsFalse =
        refl
    ; globalForeignLaneActionIdentityConstructed =
        false
    ; globalForeignLaneActionIdentityConstructedIsFalse =
        refl
    ; trackedCarrierActionConstructed =
        false
    ; trackedCarrierActionConstructedIsFalse =
        refl
    ; extensionRequestClosed =
        false
    ; extensionRequestClosedIsFalse =
        refl
    ; promotesDRClassification =
        false
    ; promotesDRClassificationIsFalse =
        refl
    ; reconstructsGaugeAssignment =
        false
    ; reconstructsGaugeAssignmentIsFalse =
        refl
    ; extensionBoundary =
        "Degenerate witness available: Hexagon.degenerateEmptyLocalisedEndomorphismCarrierSemantics uses the empty carrier predicate"
        ∷ "That witness is intentionally non-promoting and does not provide a nonempty fixed-point subset"
        ∷ "G6 tracked attempt available: the nontrivial tracked witness gives a nonempty all-carrier predicate, but not a DHR sector-specific predicate"
        ∷ "Final localised ledger available: sector-specific nonempty carrier predicate, global foreign-lane identity, and selected-predicate lane-action preservation remain supplied-interface obligations"
        ∷ "Conditional intertwiner interface available: once source and target nondegenerate local interfaces are supplied, the target-selected carrier action supplies the primitive IntertwinerTrackedCarrierSemanticsInterface"
        ∷ "Precise extension field 1: selected nonempty carrier predicate on the G6 tracked carrier for each DHR object and lane"
        ∷ "Precise extension field 2: global foreign-lane action identity on that selected carrier, not only tracked-prime coordinate locality"
        ∷ "Precise extension field 3: tracked DHR Intertwiner carrier action with preservation and foreign-lane invisibility evidence"
        ∷ "Final fallback interface: supply Hexagon.NondegenerateLocalisedEndomorphismCarrierSemanticsInterface and Hexagon.NondegenerateIntertwinerTrackedCarrierSemanticsInterface, then consume them through the existing Hexagon adapter constructors"
        ∷ "This extension request keeps the DHR bridge, DR classification, gauge assignment, and symmetric hexagon closed flags false"
        ∷ []
    }

canonicalDHRStructuralLocalisationBridge :
  DHRStructuralLocalisationBridge
    (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
      (G6K.G6TrackedKostantRoute.officialTrackedTheorem
        G6K.canonicalG6TrackedKostantRoute))
canonicalDHRStructuralLocalisationBridge =
  record
    { localisedForeignLaneIdEvidenceTarget =
        λ ρ lane foreignLaneId external lane≢foreign →
          Hexagon.localisedEndomorphismWithForeignLaneIdEvidenceFromInterface
            (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
              (G6K.G6TrackedKostantRoute.officialTrackedTheorem
                G6K.canonicalG6TrackedKostantRoute))
            ρ
            lane
            foreignLaneId
            external
            lane≢foreign
    ; localisedForeignLaneIdAdapterBoundaryTarget =
        λ ρ lane foreignLaneId evidence →
          Hexagon.localisedEndomorphismWithForeignLaneIdToAdapterBoundary
            (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
              (G6K.G6TrackedKostantRoute.officialTrackedTheorem
                G6K.canonicalG6TrackedKostantRoute))
            ρ
            lane
            foreignLaneId
            evidence
    ; nonemptyWitnessFromForeignLaneIdEvidenceTarget =
        λ _ _ _ evidence →
          Hexagon.localisedForeignLaneNonemptyWitness evidence
    ; trackedIntertwinerForeignLaneIdAdapterTarget =
        λ ρ σ f ρLane σLane foreignLaneId ρEvidence σEvidence →
          Hexagon.targetSelectedTrackedIntertwinerForeignLaneIdAdapter
            (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
              (G6K.G6TrackedKostantRoute.officialTrackedTheorem
                G6K.canonicalG6TrackedKostantRoute))
            ρ
            σ
            f
            ρLane
            σLane
            foreignLaneId
            ρEvidence
            σEvidence
    ; localisedCarrierSemanticsDerivedFromSuppliedInterface =
        true
    ; localisedCarrierSemanticsDerivedFromSuppliedInterfaceIsTrue =
        refl
    ; nonemptyWitnessDerivedFromSuppliedInterface =
        true
    ; nonemptyWitnessDerivedFromSuppliedInterfaceIsTrue =
        refl
    ; trackedIntertwinerAdapterDerivedFromSuppliedInterfaces =
        true
    ; trackedIntertwinerAdapterDerivedFromSuppliedInterfacesIsTrue =
        refl
    ; objectLaneClassifierConstructed =
        false
    ; objectLaneClassifierConstructedIsFalse =
        refl
    ; bridgeClosed =
        false
    ; bridgeClosedIsFalse =
        refl
    ; promotesDRClassification =
        false
    ; promotesDRClassificationIsFalse =
        refl
    ; reconstructsGaugeAssignment =
        false
    ; reconstructsGaugeAssignmentIsFalse =
        refl
    ; closesSymmetricHexagon =
        false
    ; closesSymmetricHexagonIsFalse =
        refl
    ; structuralBridgeBoundary =
        "Derived structural localisation bridge: a supplied nondegenerate localised interface now yields local carrier semantics, a nonempty carrier witness, and named foreignLaneId fixed-witness evidence"
        ∷ "The bridge also derives a target-selected tracked intertwiner foreignLaneId adapter from source and target localised foreignLaneId evidence"
        ∷ "The derivation is conditional on supplied interfaces and lane inequality evidence; it does not construct an object-lane classifier from DHR alone"
        ∷ "DHR naturality, fusion, braiding, symmetric hexagon, DR classification, and gauge reconstruction remain open"
        ∷ []
    }

record DHRPrimitiveImplementationAttemptSummary
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω where
  field
    exactClassifierIrreducibilityRecord :
      Hexagon.DHRExactClassifierIrreducibilityRecord operator

    concreteNonemptySectorWitness :
      (ρ : DHR.LocalisedEndomorphism) →
      (lane : G6.Lane) →
      Hexagon.DHRConcreteNonemptySectorWitness operator ρ lane

    targetSelectedTrackedIntertwinerAction :
      (ρ σ : DHR.LocalisedEndomorphism) →
      (f : DHR.Intertwiner ρ σ) →
      (ρLane σLane : G6.Lane) →
      Hexagon.DHRConcreteTrackedIntertwinerActionPrimitive
        operator
        ρ
        σ
        f
        ρLane
        σLane
        (concreteNonemptySectorWitness ρ ρLane)
        (concreteNonemptySectorWitness σ σLane)

    concreteNonemptySectorWitnessConstructed :
      Bool

    concreteNonemptySectorWitnessConstructedIsTrue :
      concreteNonemptySectorWitnessConstructed ≡ true

    targetSelectedTrackedIntertwinerActionConstructed :
      Bool

    targetSelectedTrackedIntertwinerActionConstructedIsTrue :
      targetSelectedTrackedIntertwinerActionConstructed ≡ true

    superselectionSectorConstructorsConstructed :
      Bool

    superselectionSectorConstructorsConstructedIsFalse :
      superselectionSectorConstructorsConstructed ≡ false

    assignedLaneClassifierEvidenceConstructed :
      Bool

    assignedLaneClassifierEvidenceConstructedIsFalse :
      assignedLaneClassifierEvidenceConstructed ≡ false

    foreignLaneIdentityConstructed :
      Bool

    foreignLaneIdentityConstructedIsFalse :
      foreignLaneIdentityConstructed ≡ false

    dhrNaturalityConstructed :
      Bool

    dhrNaturalityConstructedIsFalse :
      dhrNaturalityConstructed ≡ false

    closesSymmetricHexagon :
      Bool

    closesSymmetricHexagonIsFalse :
      closesSymmetricHexagon ≡ false

    primitiveAttemptBoundary :
      List String

open DHRPrimitiveImplementationAttemptSummary public

canonicalDHRPrimitiveImplementationAttemptSummary :
  DHRPrimitiveImplementationAttemptSummary
    (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
      (G6K.G6TrackedKostantRoute.officialTrackedTheorem
        G6K.canonicalG6TrackedKostantRoute))
canonicalDHRPrimitiveImplementationAttemptSummary =
  record
    { exactClassifierIrreducibilityRecord =
        Hexagon.dhrExactClassifierIrreducibilityRecord
          (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
            (G6K.G6TrackedKostantRoute.officialTrackedTheorem
              G6K.canonicalG6TrackedKostantRoute))
    ; concreteNonemptySectorWitness =
        Hexagon.dhrConcreteNonemptySectorWitness
          (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
            (G6K.G6TrackedKostantRoute.officialTrackedTheorem
              G6K.canonicalG6TrackedKostantRoute))
    ; targetSelectedTrackedIntertwinerAction =
        λ ρ σ f ρLane σLane →
          Hexagon.targetSelectedDHRConcreteTrackedIntertwinerActionPrimitive
            (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
              (G6K.G6TrackedKostantRoute.officialTrackedTheorem
                G6K.canonicalG6TrackedKostantRoute))
            ρ
            σ
            f
            ρLane
            σLane
            (Hexagon.dhrConcreteNonemptySectorWitness
              (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
                (G6K.G6TrackedKostantRoute.officialTrackedTheorem
                  G6K.canonicalG6TrackedKostantRoute))
              ρ
              ρLane)
            (Hexagon.dhrConcreteNonemptySectorWitness
              (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
                (G6K.G6TrackedKostantRoute.officialTrackedTheorem
                  G6K.canonicalG6TrackedKostantRoute))
              σ
              σLane)
    ; concreteNonemptySectorWitnessConstructed =
        true
    ; concreteNonemptySectorWitnessConstructedIsTrue =
        refl
    ; targetSelectedTrackedIntertwinerActionConstructed =
        true
    ; targetSelectedTrackedIntertwinerActionConstructedIsTrue =
        refl
    ; superselectionSectorConstructorsConstructed =
        false
    ; superselectionSectorConstructorsConstructedIsFalse =
        refl
    ; assignedLaneClassifierEvidenceConstructed =
        false
    ; assignedLaneClassifierEvidenceConstructedIsFalse =
        refl
    ; foreignLaneIdentityConstructed =
        false
    ; foreignLaneIdentityConstructedIsFalse =
        refl
    ; dhrNaturalityConstructed =
        false
    ; dhrNaturalityConstructedIsFalse =
        refl
    ; closesSymmetricHexagon =
        false
    ; closesSymmetricHexagonIsFalse =
        refl
    ; primitiveAttemptBoundary =
        "Implemented primitive attempt: DHRPrimitiveSectorClass names four lane classes, but DHR.SuperselectionSector constructors remain absent"
        ∷ "Implemented primitive attempt: each LocalisedEndomorphism now has a concrete G6 nonempty all-carrier witness for a chosen lane"
        ∷ "Implemented primitive attempt: foreign-lane identity is represented as an explicit structural field target, not inferred from coordinate locality"
        ∷ "Implemented primitive attempt: a target-selected tracked intertwiner carrier action is available as a carrier-level primitive"
        ∷ "Fail-closed blocker: assigned lane classifier evidence still needs sector constructors, a sector-to-lane predicate, a sector-specific nonempty carrier predicate, foreign-lane identity, and irreducibility input"
        ∷ "No DHR naturality square, DR classification, gauge reconstruction, or symmetric hexagon closure is promoted"
        ∷ []
    }

record DHRHexagonProofPlanSurface : Setω where
  field
    status :
      DHRHexagonProofPlanStatus

    dhrHexagonObligation :
      Hexagon.DHRHexagonObligation

    dhrFailClosedCoherenceReceipt :
      Hexagon.DHRHexagonFailClosedCoherenceReceipt

    dhrFullTransportHexagonClosed :
      Hexagon.DHRHexagonFailClosedCoherenceReceipt.fullTransportDRHexagonClosed
        dhrFailClosedCoherenceReceipt
      ≡
      false

    dhrCategoryPrimitives :
      DHR.DHRCategoryPrimitiveSurface

    dhrPrimitiveCategoryLawsProved :
      Bool

    dhrPrimitiveCategoryLawsProvedIsFalse :
      dhrPrimitiveCategoryLawsProved ≡ false

    g6TrackedRoute :
      G6K.G6TrackedKostantRoute

    g6TrackedRoutePromoted :
      G6K.G6TrackedKostantRoute.trackedRoutePromoted g6TrackedRoute ≡ true

    g6TrackedCommutationAvailable :
      G6.G6TrackedCrossLaneCommutationTheorem
        (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
          (G6K.G6TrackedKostantRoute.officialTrackedTheorem g6TrackedRoute))

    dhrToG6FunctorTarget :
      DHRToG6TrackedLaneActionFunctorTarget

    dhrToG6FunctorSubobligations :
      DHRToG6TrackedLaneActionFunctorSubobligations
        (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
          (G6K.G6TrackedKostantRoute.officialTrackedTheorem g6TrackedRoute))

    dhrBridgeAdapterRequest :
      DHRBridgeAdapterRequest
        (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
          (G6K.G6TrackedKostantRoute.officialTrackedTheorem g6TrackedRoute))

    dhrSemanticBridgeNarrowing :
      DHRSemanticBridgeNarrowing
        (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
          (G6K.G6TrackedKostantRoute.officialTrackedTheorem g6TrackedRoute))

    dhrNondegenerateCarrierSemanticsExtensionRequest :
      DHRNondegenerateCarrierSemanticsExtensionRequest
        (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
          (G6K.G6TrackedKostantRoute.officialTrackedTheorem g6TrackedRoute))

    dhrStructuralLocalisationBridge :
      DHRStructuralLocalisationBridge
        (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
          (G6K.G6TrackedKostantRoute.officialTrackedTheorem g6TrackedRoute))

    dhrPrimitiveImplementationAttemptSummary :
      DHRPrimitiveImplementationAttemptSummary
        (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
          (G6K.G6TrackedKostantRoute.officialTrackedTheorem g6TrackedRoute))

    dhrObjectToLaneClassifierIrreducibilityLedger :
      Hexagon.DHRObjectToLaneClassifierIrreducibilityLedger
        (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
          (G6K.G6TrackedKostantRoute.officialTrackedTheorem g6TrackedRoute))

    dhrBridgeAdapterClosed :
      Bool

    dhrBridgeAdapterClosedIsFalse :
      dhrBridgeAdapterClosed ≡ false

    firstMissingPrimitive :
      DHRHexagonFirstMissingPrimitive

    firstMissingPrimitiveIsObjectFunctor :
      firstMissingPrimitive ≡ missingDHRToTrackedLaneActionFunctor

    canCloseUnitCoherenceDefinitionalNow :
      Bool

    canCloseUnitCoherenceDefinitionalNowIsFalse :
      canCloseUnitCoherenceDefinitionalNow ≡ false

    canCloseHexagonFromG6Now :
      Bool

    canCloseHexagonFromG6NowIsFalse :
      canCloseHexagonFromG6Now ≡ false

    promotesDRClassification :
      Bool

    promotesDRClassificationIsFalse :
      promotesDRClassification ≡ false

    reconstructsGaugeAssignment :
      Bool

    reconstructsGaugeAssignmentIsFalse :
      reconstructsGaugeAssignment ≡ false

    proofPlan :
      List String

    failClosedBoundary :
      List String

open DHRHexagonProofPlanSurface public

canonicalDHRHexagonProofPlanSurface :
  DHRHexagonProofPlanSurface
canonicalDHRHexagonProofPlanSurface =
  record
    { status =
        proofPlanOnlyNoPromotion
    ; dhrHexagonObligation =
        Hexagon.canonicalDHRHexagonObligation
    ; dhrFailClosedCoherenceReceipt =
        Hexagon.canonicalDHRHexagonFailClosedCoherenceReceipt
    ; dhrFullTransportHexagonClosed =
        Hexagon.canonicalDHRHexagonFullTransportStillOpen
    ; dhrCategoryPrimitives =
        DHR.canonicalDHRCategoryPrimitiveSurface
    ; dhrPrimitiveCategoryLawsProved =
        DHR.DHRCategoryPrimitiveSurface.primitiveCategoryLawsProved
          DHR.canonicalDHRCategoryPrimitiveSurface
    ; dhrPrimitiveCategoryLawsProvedIsFalse =
        DHR.DHRCategoryPrimitiveSurface.primitiveCategoryLawsProvedIsFalse
          DHR.canonicalDHRCategoryPrimitiveSurface
    ; g6TrackedRoute =
        G6K.canonicalG6TrackedKostantRoute
    ; g6TrackedRoutePromoted =
        G6K.G6TrackedKostantRoute.trackedRoutePromotedIsTrue
          G6K.canonicalG6TrackedKostantRoute
    ; g6TrackedCommutationAvailable =
        G6K.G6TrackedKostantRoute.trackedActionCommutation
          G6K.canonicalG6TrackedKostantRoute
    ; dhrToG6FunctorTarget =
        canonicalDHRToG6TrackedLaneActionFunctorTarget
    ; dhrToG6FunctorSubobligations =
        canonicalDHRToG6TrackedLaneActionFunctorSubobligations
    ; dhrBridgeAdapterRequest =
        canonicalDHRBridgeAdapterRequest
    ; dhrSemanticBridgeNarrowing =
        canonicalDHRSemanticBridgeNarrowing
    ; dhrNondegenerateCarrierSemanticsExtensionRequest =
        canonicalDHRNondegenerateCarrierSemanticsExtensionRequest
    ; dhrStructuralLocalisationBridge =
        canonicalDHRStructuralLocalisationBridge
    ; dhrPrimitiveImplementationAttemptSummary =
        canonicalDHRPrimitiveImplementationAttemptSummary
    ; dhrObjectToLaneClassifierIrreducibilityLedger =
        Hexagon.dhrObjectToLaneClassifierIrreducibilityLedger
          (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
            (G6K.G6TrackedKostantRoute.officialTrackedTheorem
              G6K.canonicalG6TrackedKostantRoute))
    ; dhrBridgeAdapterClosed =
        false
    ; dhrBridgeAdapterClosedIsFalse =
        refl
    ; firstMissingPrimitive =
        missingDHRToTrackedLaneActionFunctor
    ; firstMissingPrimitiveIsObjectFunctor =
        refl
    ; canCloseUnitCoherenceDefinitionalNow =
        false
    ; canCloseUnitCoherenceDefinitionalNowIsFalse =
        refl
    ; canCloseHexagonFromG6Now =
        false
    ; canCloseHexagonFromG6NowIsFalse =
        refl
    ; promotesDRClassification =
        false
    ; promotesDRClassificationIsFalse =
        refl
    ; reconstructsGaugeAssignment =
        false
    ; reconstructsGaugeAssignmentIsFalse =
        refl
    ; proofPlan =
        "Step 1: choose the object-to-lane route: explicit fail-closed adapter now, or wait for inhabited prime-lane DHR classification and DR reconstruction"
        ∷ "Step 1a0: record the degenerate empty LocalisedEndomorphismCarrierSemantics witness, then refuse to treat it as a nonempty sector realisation"
        ∷ "Step 1a0b: consume supplied nondegenerate localised interfaces as structural foreignLaneId evidence with a nonempty selected carrier witness"
        ∷ "Step 1a0c: use the concrete G6 nontrivial carrier witness and target-selected tracked action as primitive attempts, while recording exact classifier irreducibility"
        ∷ "Step 1a: satisfy DHRBridgeAdapterRequest by providing object-to-lane and intertwiner carrier action fields"
        ∷ "Step 1b: extend that adapter to carrier realisation, action realisation, naturality-square, and tensor-lane compatibility fields"
        ∷ "Step 2: prove intertwiners are natural for the tracked G6 FactorVec lane-action commutation"
        ∷ "Step 3: construct the DHR tensor product and unit object, then prove unit and pentagon coherence"
        ∷ "Step 4: compute the DHR statistics operator as the braiding and prove left/right hexagon plus involutivity"
        ∷ "Current receipt: DHRHexagonFailClosedCoherenceReceipt records unit, braiding, and hexagon targets but keeps fullTransportDRHexagonClosed false"
        ∷ []
    ; failClosedBoundary =
        "G6 tracked FactorVec commutation is available, but it is not yet a DHR braiding"
        ∷ "The DHR category primitive surface still reports primitiveCategoryLawsProved = false"
        ∷ "A degenerate empty LocalisedEndomorphismCarrierSemantics witness is available, but it selects no tracked carrier point"
        ∷ "A supplied nondegenerate localised interface now derives a nonempty selected carrier witness and named foreignLaneId fixed-witness evidence, but the interface itself remains external"
        ∷ "A concrete all-carrier nonempty sector witness and target-selected tracked action are available, but they are not sector-specific classifier evidence"
        ∷ "A constant canonical-lane candidate map exists, but the final irreducibility ledger rejects it as classifier evidence because no sector-to-lane predicate or sector-specific carrier predicate is supplied"
        ∷ "The DHR semantic bridge narrowing defines the carrier-level sector-lane invariant relation but has no classifier evidence or tracked carrier action on Intertwiner"
        ∷ "Unit coherence is not definitional yet because no concrete DHR tensor unit or tensor product is exposed"
        ∷ "Braiding naturality is not closed because no DHR object-to-lane map, intertwiner carrier action, or naturality square is constructed"
        ∷ "The symmetric hexagon is not closed because left/right hexagon targets are sockets, not proof fields"
        ∷ "No DR classification, gauge assignment, terminal claim, W3/W4/W5, or Clay flag is promoted"
        ∷ []
    }

canonicalDHRHexagonProofPlanFirstMissing :
  DHRHexagonProofPlanSurface.firstMissingPrimitive
    canonicalDHRHexagonProofPlanSurface
  ≡
  missingDHRToTrackedLaneActionFunctor
canonicalDHRHexagonProofPlanFirstMissing =
  refl

canonicalDHRHexagonProofPlanNoDRPromotion :
  DHRHexagonProofPlanSurface.promotesDRClassification
    canonicalDHRHexagonProofPlanSurface
  ≡
  false
canonicalDHRHexagonProofPlanNoDRPromotion =
  refl

canonicalDHRHexagonProofPlanNoGaugeReconstruction :
  DHRHexagonProofPlanSurface.reconstructsGaugeAssignment
    canonicalDHRHexagonProofPlanSurface
  ≡
  false
canonicalDHRHexagonProofPlanNoGaugeReconstruction =
  refl

canonicalDHRHexagonProofPlanFullTransportStillOpen :
  DHRHexagonProofPlanSurface.dhrFullTransportHexagonClosed
    canonicalDHRHexagonProofPlanSurface
  ≡
  Hexagon.canonicalDHRHexagonFullTransportStillOpen
canonicalDHRHexagonProofPlanFullTransportStillOpen =
  refl

canonicalDHRSemanticBridgeFirstBlocker :
  DHRSemanticBridgeNarrowing.firstBlocker
    canonicalDHRSemanticBridgeNarrowing
  ≡
  firstBlockerNoSectorLaneInvariantOnLocalisedEndomorphism
canonicalDHRSemanticBridgeFirstBlocker =
  refl

canonicalDHRSemanticBridgeObjectRouteIsAdapterRequest :
  DHRSemanticBridgeNarrowing.objectToLaneBridgeRoute
    canonicalDHRSemanticBridgeNarrowing
  ≡
  objectToLaneMayBeAdapterSuppliedFailClosed
canonicalDHRSemanticBridgeObjectRouteIsAdapterRequest =
  refl

canonicalDHRSemanticBridgeIntertwinerRouteIsAdapterRequest :
  DHRSemanticBridgeNarrowing.intertwinerCarrierActionBridgeRoute
    canonicalDHRSemanticBridgeNarrowing
  ≡
  intertwinerCarrierActionMayBeAdapterSuppliedFailClosed
canonicalDHRSemanticBridgeIntertwinerRouteIsAdapterRequest =
  refl

canonicalDHRSemanticBridgeStillOpen :
  DHRSemanticBridgeNarrowing.bridgeClosed
    canonicalDHRSemanticBridgeNarrowing
  ≡
  false
canonicalDHRSemanticBridgeStillOpen =
  refl

canonicalDHRCarrierSemanticsFirstBlockerIsPredicate :
  Hexagon.DHRCarrierSemanticsAbsenceLedger.localCarrierSemanticsFirstMissingPiece
    (DHRSemanticBridgeNarrowing.carrierSemanticsAbsenceLedger
      canonicalDHRSemanticBridgeNarrowing)
  ≡
  Hexagon.carrierPredicateMissing
canonicalDHRCarrierSemanticsFirstBlockerIsPredicate =
  refl

canonicalDHRCarrierSemanticsForeignLaneIdentityStillMissing :
  Hexagon.DHRCarrierSemanticsAbsenceLedger.foreignLaneGlobalActionIdentitySupplied
    (DHRSemanticBridgeNarrowing.carrierSemanticsAbsenceLedger
      canonicalDHRSemanticBridgeNarrowing)
  ≡
  false
canonicalDHRCarrierSemanticsForeignLaneIdentityStillMissing =
  refl

canonicalDHRIntertwinerCarrierSemanticsFirstBlockerIsAction :
  Hexagon.DHRCarrierSemanticsAbsenceLedger.intertwinerCarrierSemanticsFirstMissingPiece
    (DHRSemanticBridgeNarrowing.carrierSemanticsAbsenceLedger
      canonicalDHRSemanticBridgeNarrowing)
  ≡
  Hexagon.trackedCarrierActionMissing
canonicalDHRIntertwinerCarrierSemanticsFirstBlockerIsAction =
  refl

canonicalDHRClassifierCandidateTargetsMaxwellLane :
  (ρ : DHR.LocalisedEndomorphism) →
  Hexagon.DHRObjectToLaneClassifierIrreducibilityLedger.candidateCanonicalLaneClassifier
    (DHRHexagonProofPlanSurface.dhrObjectToLaneClassifierIrreducibilityLedger
      canonicalDHRHexagonProofPlanSurface)
    ρ
  ≡
  G6.maxwellLane
canonicalDHRClassifierCandidateTargetsMaxwellLane =
  Hexagon.DHRObjectToLaneClassifierIrreducibilityLedger.candidateClassifierTargetsMaxwellLane
    (DHRHexagonProofPlanSurface.dhrObjectToLaneClassifierIrreducibilityLedger
      canonicalDHRHexagonProofPlanSurface)

canonicalDHREvidencedClassifierStillOpen :
  Hexagon.DHRObjectToLaneClassifierIrreducibilityLedger.evidencedObjectToLaneClassifierConstructed
    (DHRHexagonProofPlanSurface.dhrObjectToLaneClassifierIrreducibilityLedger
      canonicalDHRHexagonProofPlanSurface)
  ≡
  false
canonicalDHREvidencedClassifierStillOpen =
  refl

canonicalDHRClassifierFirstMissingSectorToLanePredicate :
  Hexagon.DHRObjectToLaneClassifierIrreducibilityLedger.firstMissingPiece
    (DHRHexagonProofPlanSurface.dhrObjectToLaneClassifierIrreducibilityLedger
      canonicalDHRHexagonProofPlanSurface)
  ≡
  Hexagon.missingSectorToCanonicalLanePredicate
canonicalDHRClassifierFirstMissingSectorToLanePredicate =
  refl

------------------------------------------------------------------------
-- Named DHRSuperselectionSector/sectorLane supply surface.

record DHRUserSuppliedSectorLanePrimitiveProgress
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω where
  field
    dhrSuperselectionSectorLaneSupplyLedger :
      Hexagon.DHRSuperselectionSectorLaneSupplyAbsenceLedger operator

    suppliedSectorLaneNaturalityHexagonWiring :
      Hexagon.DHRSuppliedSectorLaneNaturalityHexagonWiring operator

    dhrSuperselectionSectorTarget :
      Set

    dhrSuperselectionSectorTargetIsPrimitive :
      dhrSuperselectionSectorTarget
      ≡
      Hexagon.DHRSuperselectionSector

    sectorLaneSupplyInterfaceTarget :
      DHR.LocalisedEndomorphism →
      Set₁

    sectorLaneSupplyInterfaceTargetIsCanonical :
      (ρ : DHR.LocalisedEndomorphism) →
      sectorLaneSupplyInterfaceTarget ρ
      ≡
      Hexagon.DHRSuperselectionSectorLaneSupply operator ρ

    consumesSuppliedSectorLaneInterface :
      Bool

    consumesSuppliedSectorLaneInterfaceIsTrue :
      consumesSuppliedSectorLaneInterface ≡ true

    wiresTrackedIntertwinerActionFromSuppliedInterfaces :
      Bool

    wiresTrackedIntertwinerActionFromSuppliedInterfacesIsTrue :
      wiresTrackedIntertwinerActionFromSuppliedInterfaces ≡ true

    constructsSectorLaneInterfaceInternally :
      Bool

    constructsSectorLaneInterfaceInternallyIsFalse :
      constructsSectorLaneInterfaceInternally ≡ false

    constructsForeignLaneIdentityInternally :
      Bool

    constructsForeignLaneIdentityInternallyIsFalse :
      constructsForeignLaneIdentityInternally ≡ false

    closesBraidingNaturality :
      Bool

    closesBraidingNaturalityIsFalse :
      closesBraidingNaturality ≡ false

    closesDHRBridge :
      Bool

    closesDHRBridgeIsFalse :
      closesDHRBridge ≡ false

    closesSymmetricHexagon :
      Bool

    closesSymmetricHexagonIsFalse :
      closesSymmetricHexagon ≡ false

    userSuppliedSectorLaneProgressBoundary :
      List String

open DHRUserSuppliedSectorLanePrimitiveProgress public

canonicalDHRUserSuppliedSectorLanePrimitiveProgress :
  DHRUserSuppliedSectorLanePrimitiveProgress
    (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
      (G6K.G6TrackedKostantRoute.officialTrackedTheorem
        G6K.canonicalG6TrackedKostantRoute))
canonicalDHRUserSuppliedSectorLanePrimitiveProgress =
  record
    { dhrSuperselectionSectorLaneSupplyLedger =
        Hexagon.dhrSuperselectionSectorLaneSupplyAbsenceLedger
          (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
            (G6K.G6TrackedKostantRoute.officialTrackedTheorem
              G6K.canonicalG6TrackedKostantRoute))
    ; suppliedSectorLaneNaturalityHexagonWiring =
        Hexagon.dhrSuppliedSectorLaneNaturalityHexagonWiring
          (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
            (G6K.G6TrackedKostantRoute.officialTrackedTheorem
              G6K.canonicalG6TrackedKostantRoute))
    ; dhrSuperselectionSectorTarget =
        Hexagon.DHRSuperselectionSector
    ; dhrSuperselectionSectorTargetIsPrimitive =
        refl
    ; sectorLaneSupplyInterfaceTarget =
        Hexagon.DHRSuperselectionSectorLaneSupply
          (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
            (G6K.G6TrackedKostantRoute.officialTrackedTheorem
              G6K.canonicalG6TrackedKostantRoute))
    ; sectorLaneSupplyInterfaceTargetIsCanonical =
        λ _ → refl
    ; consumesSuppliedSectorLaneInterface =
        true
    ; consumesSuppliedSectorLaneInterfaceIsTrue =
        refl
    ; wiresTrackedIntertwinerActionFromSuppliedInterfaces =
        true
    ; wiresTrackedIntertwinerActionFromSuppliedInterfacesIsTrue =
        refl
    ; constructsSectorLaneInterfaceInternally =
        false
    ; constructsSectorLaneInterfaceInternallyIsFalse =
        refl
    ; constructsForeignLaneIdentityInternally =
        false
    ; constructsForeignLaneIdentityInternallyIsFalse =
        refl
    ; closesBraidingNaturality =
        false
    ; closesBraidingNaturalityIsFalse =
        refl
    ; closesDHRBridge =
        false
    ; closesDHRBridgeIsFalse =
        refl
    ; closesSymmetricHexagon =
        false
    ; closesSymmetricHexagonIsFalse =
        refl
    ; userSuppliedSectorLaneProgressBoundary =
        "Proof-plan surface now names the exact user-supplied DHRSuperselectionSector/sectorPrimaryLane interface consumed by the hexagon obligation module"
        ∷ "The interface includes nonempty selected carrier and foreign-lane identity evidence, but this module does not construct those fields internally"
        ∷ "Supplied source and target interfaces wire a target-selected tracked Intertwiner carrier action"
        ∷ "Braiding naturality, DHR bridge closure, and symmetric hexagon promotion remain false"
        ∷ []
    }

canonicalDHRUserSuppliedSectorLaneProgressConsumesInterface :
  consumesSuppliedSectorLaneInterface
    canonicalDHRUserSuppliedSectorLanePrimitiveProgress
  ≡
  true
canonicalDHRUserSuppliedSectorLaneProgressConsumesInterface =
  refl

canonicalDHRUserSuppliedSectorLaneProgressDoesNotCloseHexagon :
  closesSymmetricHexagon
    canonicalDHRUserSuppliedSectorLanePrimitiveProgress
  ≡
  false
canonicalDHRUserSuppliedSectorLaneProgressDoesNotCloseHexagon =
  refl

canonicalDHRUserSuppliedSectorLaneProgressWiresTrackedAction :
  wiresTrackedIntertwinerActionFromSuppliedInterfaces
    canonicalDHRUserSuppliedSectorLanePrimitiveProgress
  ≡
  true
canonicalDHRUserSuppliedSectorLaneProgressWiresTrackedAction =
  refl

canonicalDHRUserSuppliedSectorLaneProgressNaturalityStillOpen :
  closesBraidingNaturality
    canonicalDHRUserSuppliedSectorLanePrimitiveProgress
  ≡
  false
canonicalDHRUserSuppliedSectorLaneProgressNaturalityStillOpen =
  refl

------------------------------------------------------------------------
-- u6 arbitrary-sector selected foreign-identity packaging plan.

record DHRArbitrarySectorSelectedForeignIdentityPackagingPlan
  (operator : G6.NontrivialTrackedLaneOperator) :
  Setω where
  field
    packagingReceipt :
      Hexagon.DHRArbitrarySectorSelectedForeignIdentityPackagingReceipt
        operator

    fieldLattice :
      Hexagon.DHRArbitrarySectorForeignIdentityFieldLattice operator

    selectedPredicateIdentityPackaged :
      Bool

    selectedPredicateIdentityPackagedIsTrue :
      selectedPredicateIdentityPackaged ≡ true

    arbitrarySectorLaneSupplyRouted :
      Bool

    arbitrarySectorLaneSupplyRoutedIsTrue :
      arbitrarySectorLaneSupplyRouted ≡ true

    repoGlobalForeignLaneIdentityTheoremSupplied :
      Bool

    repoGlobalForeignLaneIdentityTheoremSuppliedIsFalse :
      repoGlobalForeignLaneIdentityTheoremSupplied ≡ false

    firstResidual :
      Hexagon.DHRArbitrarySectorForeignIdentityFieldLatticeResidual

    firstResidualIsExplicitForeignIdentityWitness :
      firstResidual
      ≡
      Hexagon.residualGlobalForeignLaneIdentityRequiresExplicitWitness

    downstreamAQFTDRBlockers :
      List Hexagon.DHRArbitrarySectorClassificationDownstreamBlocker

    arbitrarySectorClassificationPromoted :
      Bool

    arbitrarySectorClassificationPromotedIsFalse :
      arbitrarySectorClassificationPromoted ≡ false

    promotesDRClassification :
      Bool

    promotesDRClassificationIsFalse :
      promotesDRClassification ≡ false

    packagingPlanBoundary :
      List String

open DHRArbitrarySectorSelectedForeignIdentityPackagingPlan public

canonicalDHRArbitrarySectorSelectedForeignIdentityPackagingPlan :
  DHRArbitrarySectorSelectedForeignIdentityPackagingPlan
    (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
      (G6K.G6TrackedKostantRoute.officialTrackedTheorem
        G6K.canonicalG6TrackedKostantRoute))
canonicalDHRArbitrarySectorSelectedForeignIdentityPackagingPlan =
  record
    { packagingReceipt =
        Hexagon.canonicalDHRArbitrarySectorSelectedForeignIdentityPackagingReceipt
          (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
            (G6K.G6TrackedKostantRoute.officialTrackedTheorem
              G6K.canonicalG6TrackedKostantRoute))
    ; fieldLattice =
        Hexagon.canonicalDHRArbitrarySectorForeignIdentityFieldLattice
          (G6.G6OfficialTrackedCrossLaneCommutingTheorem.officialTrackedOperator
            (G6K.G6TrackedKostantRoute.officialTrackedTheorem
              G6K.canonicalG6TrackedKostantRoute))
    ; selectedPredicateIdentityPackaged =
        true
    ; selectedPredicateIdentityPackagedIsTrue =
        refl
    ; arbitrarySectorLaneSupplyRouted =
        true
    ; arbitrarySectorLaneSupplyRoutedIsTrue =
        refl
    ; repoGlobalForeignLaneIdentityTheoremSupplied =
        false
    ; repoGlobalForeignLaneIdentityTheoremSuppliedIsFalse =
        refl
    ; firstResidual =
        Hexagon.residualGlobalForeignLaneIdentityRequiresExplicitWitness
    ; firstResidualIsExplicitForeignIdentityWitness =
        refl
    ; downstreamAQFTDRBlockers =
        Hexagon.missingDASHILocalAlgebra
        ∷ Hexagon.blockedByMissingGate1GaugeRepresentationSemantics
        ∷ []
    ; arbitrarySectorClassificationPromoted =
        false
    ; arbitrarySectorClassificationPromotedIsFalse =
        refl
    ; promotesDRClassification =
        false
    ; promotesDRClassificationIsFalse =
        refl
    ; packagingPlanBoundary =
        "u6 proof-plan wrapper: selected-predicate foreign-lane identity is packageable from supplied nondegenerate localised interfaces"
        ∷ "That packaging routes to arbitrary-sector DHRSuperselectionSectorLaneSupply, but it does not derive a repo-native global identity theorem"
        ∷ "The first u6 blocker remains residualGlobalForeignLaneIdentityRequiresExplicitWitness"
        ∷ "missingDASHILocalAlgebra and blockedByMissingGate1GaugeRepresentationSemantics are downstream AQFT/DR blockers, not proofs constructed here"
        ∷ "No arbitrary-sector classification, DR classification, gauge reconstruction, or symmetric hexagon closure is promoted"
        ∷ []
    }

canonicalDHRArbitrarySectorSelectedForeignIdentityPackagingPlanFirstResidual :
  firstResidual
    canonicalDHRArbitrarySectorSelectedForeignIdentityPackagingPlan
  ≡
  Hexagon.residualGlobalForeignLaneIdentityRequiresExplicitWitness
canonicalDHRArbitrarySectorSelectedForeignIdentityPackagingPlanFirstResidual =
  refl
