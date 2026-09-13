module DASHI.Physics.ExoticGravity.LiTorrOrdinaryConfounderResidualRouterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Units.SI as SI
import DASHI.Physics.ExoticGravity.LiTorrSourceAttributedObservationResidualBidiExact as Residual
import DASHI.Physics.ExoticGravity.LiTorrSourceAttributedOrdinaryGREvaluationExact as Attribution
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- ORDINARY-CONFOUNDER ROUTER FOR A SOURCE-ATTRIBUTED RESIDUAL
--
-- This is the next least-privilege gate after ordinary-GR comparison.  A
-- residual outside declared uncertainty is routed through ordinary apparatus
-- explanations before it is eligible for any exotic-gravity interpretation.
-- Each clearance is experimental evidence about the tested confounder; it is
-- not an endorsement of Amy Eskridge, Li/Torr, or a DASHI reconstruction.
------------------------------------------------------------------------

data OrdinaryConfounder : Set where
  electromagneticCoupling : OrdinaryConfounder
  mechanicalCoupling : OrdinaryConfounder
  vibrationCoupling : OrdinaryConfounder
  thermalCoupling : OrdinaryConfounder
  calibrationDrift : OrdinaryConfounder
  geometryMisregistration : OrdinaryConfounder
  sensorCrossSensitivity : OrdinaryConfounder
  environmentalBackground : OrdinaryConfounder

data ConfounderStatus : Set where
  untested : ConfounderStatus
  controlledWithinDeclaredBound : ConfounderStatus
  detectedAndExplainsResidual : ConfounderStatus
  testedButResidualSurvives : ConfounderStatus

record ConfounderTestReceipt : Set where
  constructor confounder-test-receipt
  field
    confounder : OrdinaryConfounder
    status : ConfounderStatus
    apparatusIdentity : String
    calibrationRevision : String
    geometryRevision : String
    protocolLocator : String
    resultLocator : String
    measurementSource : Attribution.RoleBoundSource
    measurementSourceRoleIsExperimental :
      Attribution.role measurementSource ≡ Attribution.experimentalMeasurement
    measurementSourceSameApparatus :
      Attribution.entitlement measurementSource ≡ Attribution.sameApparatusMeasurement
    independentControlChannel : Bool
    sourceRolesRetained : Bool

open ConfounderTestReceipt public

producerForConfounder : OrdinaryConfounder → Search.ProducerClass
producerForConfounder electromagneticCoupling = Search.empiricalEvidenceProducer
producerForConfounder mechanicalCoupling = Search.empiricalEvidenceProducer
producerForConfounder vibrationCoupling = Search.empiricalEvidenceProducer
producerForConfounder thermalCoupling = Search.empiricalEvidenceProducer
producerForConfounder calibrationDrift = Search.empiricalEvidenceProducer
producerForConfounder geometryMisregistration = Search.identityProducer
producerForConfounder sensorCrossSensitivity = Search.empiricalEvidenceProducer
producerForConfounder environmentalBackground = Search.empiricalEvidenceProducer

record OrdinaryConfounderBundle : Set where
  constructor ordinary-confounder-bundle
  field
    electromagnetic : ConfounderTestReceipt
    mechanical : ConfounderTestReceipt
    vibration : ConfounderTestReceipt
    thermal : ConfounderTestReceipt
    calibration : ConfounderTestReceipt
    geometry : ConfounderTestReceipt
    sensor : ConfounderTestReceipt
    environment : ConfounderTestReceipt
    sameResidualApparatusAcrossTests : Bool
    sameCalibrationLineageAcrossTests : Bool
    noConfounderReceiptBorrowedFromDifferentApparatus : Bool

open OrdinaryConfounderBundle public

data ResidualRoutingDecision : Set where
  remainAtOrdinaryConfounderAnalysis : ResidualRoutingDecision
  ordinaryConfounderExplainsResidual : ResidualRoutingDecision
  eligibleForMechanismDiscriminator : ResidualRoutingDecision

record SourceAttributedResidualRouting (d : SI.Dimension) : Set₂ where
  constructor source-attributed-residual-routing
  field
    residual : Residual.SourceAttributedResidualReceipt d
    confounders : OrdinaryConfounderBundle
    decision : ResidualRoutingDecision
    decisionRevision : String
    residualSourceRolesRetained : Bool
    confounderTestsAreExperimentalEvidence : Bool
    decisionDoesNotCreateHistoricalAttribution : Bool

open SourceAttributedResidualRouting public

record OrdinaryConfounderRouterBoundary : Set where
  constructor ordinary-confounder-router-boundary
  field
    residualOutsideUncertaintySkipsConfounderAnalysis : Bool
    oneClearedConfounderClearsAllConfounders : Bool
    differentApparatusControlMayPaySameApparatusClearance : Bool
    confounderClearanceProvesLiTorrMechanism : Bool
    confounderClearanceMayBeAttributedToAmy : Bool
    survivingResidualMayEnterMechanismDiscriminator : Bool
    survivingResidualAutomaticallyProvesExoticGravity : Bool

canonicalOrdinaryConfounderRouterBoundary : OrdinaryConfounderRouterBoundary
canonicalOrdinaryConfounderRouterBoundary =
  ordinary-confounder-router-boundary
    false false false false false true false
