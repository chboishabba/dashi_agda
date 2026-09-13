module DASHI.Reasoning.FibreRoutingJoinedObserverEmpiricalFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.DrosophilaJoinedObserverSourceSnowballExact as Source
import DASHI.Reasoning.FibreRoutingJoinedObserverAdequacyExact as Joined
import DASHI.Reasoning.FibreRoutingCompressionLadderExact as Ladder

------------------------------------------------------------------------
-- EMPIRICAL FRONTIER AFTER JOINED OVERLAP + STIMULUS CONTROL RUN
--
-- Numerical authority stays with the dashiBRAIN JSON artefact.  This owner
-- records promotion gates and exact string-valued observations only; it does
-- not reinterpret non-rejected nulls as evidence for pair-specific wiring.
------------------------------------------------------------------------

record FourStageJoinedObserverObservation : Set where
  constructor four-stage-joined-observer-observation
  field
    runtime : Source.JoinedObserverRuntimeReceipt
    rawSoftResidual : String
    overlapControlledResidual : String
    stimulusControlledResidual : String
    joinedDecisionResidual : String
    stimulusMeanVarianceRemoved : String
    stimulusMedianVarianceRemoved : String
    stimulusVarianceRemovedRange : String
    strengthNullP : String
    strengthNullMean : String
    strengthNullMin : String
    labelNullP : String
    labelNullMean : String
    labelNullMin : String
    maxRowStrengthError : String
    maxColumnStrengthError : String

open FourStageJoinedObserverObservation public

currentFourStageObservation : FourStageJoinedObserverObservation
currentFourStageObservation =
  four-stage-joined-observer-observation
    Source.currentJoinedObserverRuntime
    "0.1485"
    "0.1360"
    "0.1496"
    "0.1364"
    "0.0688"
    "0.0495"
    "0.0058..0.3376"
    "0.3366"
    "0.1369"
    "0.1302"
    "0.8317"
    "0.1328"
    "0.1145"
    "9.78e-11"
    "8.88e-16"

data PromotionGate : Set where
  joinedControlExecutionGate : PromotionGate
  regressionTestGate : PromotionGate
  strengthNullDetachmentGate : PromotionGate
  labelNullDetachmentGate : PromotionGate
  pairSpecificWiringGate : PromotionGate
  independentReplicationGate : PromotionGate
  finerCarrierGate : PromotionGate

record GateState : Set where
  constructor gate-state
  field
    gate : PromotionGate
    paid : Bool
    evidenceReference : String

open GateState public

joinedControlExecution : GateState
joinedControlExecution =
  gate-state joinedControlExecutionGate true
    "malecns_joined_observer_ndim.json generated on dashiBRAIN c2dd30118c45521c2eeebd407f8d421d9c5b88b3"

regressionTests : GateState
regressionTests =
  gate-state regressionTestGate true
    "166/166 pytest suite passing after joined-observer run"

strengthNullDetachment : GateState
strengthNullDetachment =
  gate-state strengthNullDetachmentGate false
    "strength-preserving wiring null p=0.3366; null not rejected"

labelNullDetachment : GateState
labelNullDetachment =
  gate-state labelNullDetachmentGate false
    "co-permuted region-label null p=0.8317; null not rejected"

pairSpecificWiring : GateState
pairSpecificWiring =
  gate-state pairSpecificWiringGate false
    "pair-specific wiring mechanism is not promoted while both decision-target null families remain non-rejected"

independentReplication : GateState
independentReplication =
  gate-state independentReplicationGate false
    "single Gauthey session 04032024_6f_a2_r5 only"

finerCarrier : GateState
finerCarrier =
  gate-state finerCarrierGate false
    "current decision target remains at 26 retained painted-domain regions; sub-neuropil/cluster carrier not yet executed"

------------------------------------------------------------------------
-- Parallel snowball acquisition frontier.
-- Acquisition order is opportunistic; promotion remains dependency ordered.
------------------------------------------------------------------------

data AcquisitionTarget : Set where
  additionalGautheyTrial : AcquisitionTarget
  crossAnimalReplication : AcquisitionTarget
  subNeuropilFunctionalCarrier : AcquisitionTarget
  subNeuropilStructuralCarrier : AcquisitionTarget
  compressionCurveAcrossFlyCarriers : AcquisitionTarget
  grokkingCheckpointCompressionCurve : AcquisitionTarget

record AcquisitionFrontier : Set where
  constructor acquisition-frontier
  field
    target : AcquisitionTarget
    mayAcquireNow : Bool
    automaticallyPaysPairSpecificWiring : Bool
    rationale : String

open AcquisitionFrontier public

additionalTrialFrontier : AcquisitionFrontier
additionalTrialFrontier =
  acquisition-frontier additionalGautheyTrial true false
    "process remaining Gauthey recordings with the same source/registration/control grammar"

crossAnimalFrontier : AcquisitionFrontier
crossAnimalFrontier =
  acquisition-frontier crossAnimalReplication true false
    "independent animals are stronger than additional null resampling for population-level transfer"

subNeuropilFunctionalFrontier : AcquisitionFrontier
subNeuropilFunctionalFrontier =
  acquisition-frontier subNeuropilFunctionalCarrier true false
    "retain finer functional fibres only with provenance-preserving membership/registration receipts"

subNeuropilStructuralFrontier : AcquisitionFrontier
subNeuropilStructuralFrontier =
  acquisition-frontier subNeuropilStructuralCarrier true false
    "test whether coarse region strength dominance weakens at finer structural resolution"

flyCompressionCurveFrontier : AcquisitionFrontier
flyCompressionCurveFrontier =
  acquisition-frontier compressionCurveAcrossFlyCarriers true false
    "measure the smallest held-out-adequate biological fibre carrier after the richer soft carrier is admitted"

grokkingCompressionCurveFrontier : AcquisitionFrontier
grokkingCompressionCurveFrontier =
  acquisition-frontier grokkingCheckpointCompressionCurve true false
    "compare minimum adequate carrier complexity before/during/after grokking using the same consumer-indexed ladder"

------------------------------------------------------------------------
-- Cross-pollination anchors.
------------------------------------------------------------------------

sourceSnowball : Source.SourceSnowballBoundary
sourceSnowball = Source.canonicalSourceSnowballBoundary

joinedObserverBoundary : Joined.JoinedObserverCrossPollinationBoundary
joinedObserverBoundary = Joined.canonicalJoinedObserverCrossPollinationBoundary

compressionLadderBoundary : Ladder.FibreCompressionLadderBoundary
compressionLadderBoundary = Ladder.canonicalFibreCompressionLadderBoundary

record EmpiricalFrontierBoundary : Set where
  constructor empirical-frontier-boundary
  field
    lowerJoinedResidualEstablishesPairSpecificWiring : Bool
    nonRejectedStrengthNullMayBeRewrittenAsPositiveDetachment : Bool
    nonRejectedLabelNullMayBeRewrittenAsPositiveIdentityEvidence : Bool
    stimulusControlExecutionIsPaid : Bool
    currentRunIsIndependentReplication : Bool
    acquisitionMayProceedInParallel : Bool
    promotionMaySkipSourceIdentity : Bool
    negativeNullResultRemainsAppendOnlyEvidence : Bool

canonicalEmpiricalFrontierBoundary : EmpiricalFrontierBoundary
canonicalEmpiricalFrontierBoundary =
  empirical-frontier-boundary
    false false false true false true false true
