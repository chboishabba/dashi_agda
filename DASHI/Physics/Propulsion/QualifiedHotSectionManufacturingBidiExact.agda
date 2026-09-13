{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.QualifiedHotSectionManufacturingBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Propulsion.JetEngineFlowArchitectureExact as Jet
import DASHI.Physics.Nuclear.FissionICQualificationReliabilityDepthExact as FSPQual
import DASHI.Economics.TSMCHBMManufacturingDemandPolicy2026Exact as TSMC

------------------------------------------------------------------------
-- QUALIFIED HOT-SECTION / ADVANCED-MANUFACTURING BIDI CONSUMER
--
-- The canonical consumer is not "all metallurgy" and it is not "all fab
-- physics".  It is the smallest same-object qualification payment needed to
-- say that a manufactured article/process instance is acceptable for a bounded
-- operating envelope.  Detailed alloy/process/device models are alternative
-- producers of this payment, not definitionally mandatory prerequisites.
------------------------------------------------------------------------

data QualificationDomain : Set where
  turbineHotSection : QualificationDomain
  semiconductorProcess : QualificationDomain
  fissionInstrumentation : QualificationDomain

record ManufacturedObjectIdentity : Set where
  constructor manufactured-object-identity
  field
    domain : QualificationDomain
    objectIdentity : String
    revisionOrLot : String
    sourceObject : String

open ManufacturedObjectIdentity public

record ProcessHistory : Set where
  constructor process-history
  field
    materialOrStackIdentity : String
    manufacturingRoute : String
    thermalProcessHistory : String
    geometryOrPatternRevision : String
    sameObjectBound : Bool
    sameObjectBoundIsTrue : sameObjectBound ≡ true

open ProcessHistory public

record InspectionReceipt : Set where
  constructor inspection-receipt
  field
    inspectionMethod : String
    acceptanceCriterion : String
    observedResult : String
    sameObjectInspected : Bool
    sameObjectInspectedIsTrue : sameObjectInspected ≡ true

open InspectionReceipt public

record OperatingEnvelope : Set where
  constructor operating-envelope
  field
    temperatureEnvelope : String
    mechanicalOrElectricalEnvelope : String
    environmentEnvelope : String
    lifetimeEnvelope : String
    boundedUse : String

open OperatingEnvelope public

record QualificationPayment : Set where
  constructor qualification-payment
  field
    object : ManufacturedObjectIdentity
    history : ProcessHistory
    inspection : InspectionReceipt
    envelope : OperatingEnvelope
    sameObjectAcrossHistoryInspectionEnvelope : Bool
    sameObjectAcrossHistoryInspectionEnvelopeIsTrue :
      sameObjectAcrossHistoryInspectionEnvelope ≡ true
    acceptanceDemonstrated : Bool
    acceptanceDemonstratedIsTrue : acceptanceDemonstrated ≡ true
    evidenceReference : String

open QualificationPayment public

record CanonicalQualificationConsumer : Set where
  constructor canonical-qualification-consumer
  field
    payment : QualificationPayment
    identityPaid : Bool
    identityPaidIsTrue : identityPaid ≡ true
    processHistoryPaid : Bool
    processHistoryPaidIsTrue : processHistoryPaid ≡ true
    inspectionPaid : Bool
    inspectionPaidIsTrue : inspectionPaid ≡ true
    envelopePaid : Bool
    envelopePaidIsTrue : envelopePaid ≡ true

open CanonicalQualificationConsumer public

------------------------------------------------------------------------
-- Producer families remain optional routes.
------------------------------------------------------------------------

data QualificationProducerFamily : Set where
  alloyAndCoatingModel : QualificationProducerFamily
  castingOrAdditiveProcessModel : QualificationProducerFamily
  heatTreatmentModel : QualificationProducerFamily
  fatigueCreepOxidationModel : QualificationProducerFamily
  nondestructiveInspectionProducer : QualificationProducerFamily
  engineTestProducer : QualificationProducerFamily
  semiconductorProcessControlProducer : QualificationProducerFamily
  semiconductorMetrologyProducer : QualificationProducerFamily
  acceleratedReliabilityProducer : QualificationProducerFamily

record QualificationProducerRoute : Set where
  constructor qualification-producer-route
  field
    family : QualificationProducerFamily
    sourceObject : String
    sameObjectResolved : Bool
    producesQualificationPayment : Bool

open QualificationProducerRoute public

------------------------------------------------------------------------
-- Existing-owner anchors.
--
-- FSP qualification already formalises the structural rule that survival of a
-- single environmental axis does not imply mission qualification.  TSMC's
-- owner supplies demand/capacity provenance only; it does not certify a wafer,
-- process node, package, or device instance.
------------------------------------------------------------------------

fspQualificationEnvelope : FSPQual.QualificationEnvelope
fspQualificationEnvelope = FSPQual.canonicalQualificationEnvelope

tsmcCapacitySource : TSMC.SourceReceipt
tsmcCapacitySource = TSMC.tsmcCapacityPlanning

------------------------------------------------------------------------
-- Cross-domain structural coordinates.  The domains are not identified; only
-- the qualification grammar is shared.
------------------------------------------------------------------------

data SharedQualificationCoordinate : Set where
  controlledProcessWindow : SharedQualificationCoordinate
  traceableRevisionOrLot : SharedQualificationCoordinate
  geometryOrPatternControl : SharedQualificationCoordinate
  metrologyOrInspection : SharedQualificationCoordinate
  defectAcceptance : SharedQualificationCoordinate
  boundedOperatingEnvelope : SharedQualificationCoordinate
  lifetimeOrReliability : SharedQualificationCoordinate
  qualificationEvidence : SharedQualificationCoordinate

record CrossDomainQualificationBridge : Set where
  constructor cross-domain-qualification-bridge
  field
    leftDomain : QualificationDomain
    rightDomain : QualificationDomain
    sharedCoordinates : List SharedQualificationCoordinate
    systemIdentityClaimed : Bool
    systemIdentityClaimedIsFalse : systemIdentityClaimed ≡ false

open CrossDomainQualificationBridge public

hotSectionSemiconductorBridge : CrossDomainQualificationBridge
hotSectionSemiconductorBridge =
  cross-domain-qualification-bridge
    turbineHotSection semiconductorProcess
    (controlledProcessWindow ∷ traceableRevisionOrLot ∷ geometryOrPatternControl ∷
     metrologyOrInspection ∷ defectAcceptance ∷ boundedOperatingEnvelope ∷
     lifetimeOrReliability ∷ qualificationEvidence ∷ [])
    false refl

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data MaterialIdentityImpliesQualifiedPartPermission : Set where

data ProcessRecipeImpliesQualifiedPartPermission : Set where

data SingleInspectionImpliesLifecycleQualificationPermission : Set where

data CapacityPlanningImpliesProcessQualificationPermission : Set where

data SharedQualificationGrammarImpliesTechnologyIdentityPermission : Set where

data ThermalSurvivalImpliesFullQualificationPermission : Set where

materialIdentityDoesNotProveQualifiedPart :
  MaterialIdentityImpliesQualifiedPartPermission → ⊥
materialIdentityDoesNotProveQualifiedPart ()

processRecipeDoesNotProveQualifiedPart :
  ProcessRecipeImpliesQualifiedPartPermission → ⊥
processRecipeDoesNotProveQualifiedPart ()

singleInspectionDoesNotProveLifecycleQualification :
  SingleInspectionImpliesLifecycleQualificationPermission → ⊥
singleInspectionDoesNotProveLifecycleQualification ()

capacityPlanningDoesNotProveProcessQualification :
  CapacityPlanningImpliesProcessQualificationPermission → ⊥
capacityPlanningDoesNotProveProcessQualification ()

sharedQualificationGrammarDoesNotIdentifyTechnologies :
  SharedQualificationGrammarImpliesTechnologyIdentityPermission → ⊥
sharedQualificationGrammarDoesNotIdentifyTechnologies ()

thermalSurvivalDoesNotProveFullQualification :
  ThermalSurvivalImpliesFullQualificationPermission → ⊥
thermalSurvivalDoesNotProveFullQualification ()

------------------------------------------------------------------------
-- Engine weld.  A qualified hot-section article becomes relevant to the jet
-- architecture only through an installed-component identity receipt.
------------------------------------------------------------------------

record QualifiedPartInstalledComponentWeld : Set where
  constructor qualified-part-installed-component-weld
  field
    qualification : QualificationPayment
    component : Jet.EngineComponent
    installedPartIdentity : String
    samePhysicalPart : Bool
    samePhysicalPartIsTrue : samePhysicalPart ≡ true
    installationEvidence : String

open QualifiedPartInstalledComponentWeld public

data MatchingPartNumberCreatesInstallationIdentityPermission : Set where

matchingPartNumberDoesNotCreateInstallationIdentity :
  MatchingPartNumberCreatesInstallationIdentityPermission → ⊥
matchingPartNumberDoesNotCreateInstallationIdentity ()

------------------------------------------------------------------------
-- Reverse acquisition frontier.
------------------------------------------------------------------------

data QualificationReverseTarget : Set where
  acquireMaterialOrStackIdentity : QualificationReverseTarget
  acquireProcessRouteAndRevision : QualificationReverseTarget
  acquireThermalOrProcessHistory : QualificationReverseTarget
  acquireGeometryOrPatternRevision : QualificationReverseTarget
  acquireInspectionAndMetrology : QualificationReverseTarget
  acquireDefectAcceptanceCriteria : QualificationReverseTarget
  acquireOperatingEnvelope : QualificationReverseTarget
  acquireLifeReliabilityEvidence : QualificationReverseTarget
  acquireInstalledPartIdentity : QualificationReverseTarget
  acquireSemiconductorProcessQualification : QualificationReverseTarget

record QualificationReverseObligation : Set where
  constructor qualification-reverse-obligation
  field
    target : QualificationReverseTarget
    preferredEvidence : String
    promotes : String
    cannotPromote : String

open QualificationReverseObligation public

record CanonicalQualificationBoundary : Set where
  constructor canonical-qualification-boundary
  field
    fullMetallurgyMandatoryForEveryQualification : Bool
    fullMetallurgyMandatoryForEveryQualificationIsFalse :
      fullMetallurgyMandatoryForEveryQualification ≡ false
    fullFabPhysicsMandatoryForEveryQualification : Bool
    fullFabPhysicsMandatoryForEveryQualificationIsFalse :
      fullFabPhysicsMandatoryForEveryQualification ≡ false
    sameObjectQualificationCarrierMandatory : Bool
    sameObjectQualificationCarrierMandatoryIsTrue :
      sameObjectQualificationCarrierMandatory ≡ true
    capacityPlanningDistinctFromProcessQualification : Bool
    capacityPlanningDistinctFromProcessQualificationIsTrue :
      capacityPlanningDistinctFromProcessQualification ≡ true

canonicalQualificationBoundary : CanonicalQualificationBoundary
canonicalQualificationBoundary =
  canonical-qualification-boundary false refl false refl true refl true refl
