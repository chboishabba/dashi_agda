module DASHI.ComputerScience.RSA260BidiIntrospectiveOffsetRepairExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)

import DASHI.Core.ConsumerIndexedTrajectoryFibreAdequacyExact as Fibre
import DASHI.Core.ConsumerFibreRefinementSchedulerExact as Scheduler
import DASHI.Core.DiscriminatorSynthesisExact as Synthesis
import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as LeastPrivilege
import DASHI.Interop.DialecticalMaterialProofSearchExperimentLoopExact as Loop
import DASHI.Interop.IntrospectiveProofLoopExact as Introspective
import DASHI.ComputerScience.RSA260BidiKrylovFiniteHorizonSaturationExact as FiniteHorizon
import DASHI.ComputerScience.RSA260BidiKrylovReachableRankExact as DynamicRank
import DASHI.ComputerScience.RSA260BlockWiedemannProductionScaleReconstructionExact as Scale

------------------------------------------------------------------------
-- RSA-260 BIDI INTROSPECTIVE OFFSET REPAIR
--
-- The current dynamic observer carries (r80 , h80).  The finite-horizon
-- experiments leave a live offset residual:
--
--   d - h80 in {-1,0,+1}
--
-- on the tested portfolio.  In particular, two observed synthetic cases can
-- share r80 = 512 and h80 = 65 while requiring different generator-degree
-- answers (65 versus 66).  That is a concrete consumer-indexed observer defect,
-- not merely a narrative observation.
--
-- This thin adapter binds the defect to the repository-native introspective
-- loop.  The next scheduled coordinate is block invariant-factor /
-- minimal-generator structure.  The experiment route is bound to exactly the
-- same live ConsumerRefinementResidual.  No consumer closure is claimed here.
------------------------------------------------------------------------

finiteHorizonBoundary : FiniteHorizon.FiniteHorizonInterpretationBoundary
finiteHorizonBoundary = FiniteHorizon.canonicalFiniteHorizonInterpretationBoundary

dynamicRankBoundary : DynamicRank.DynamicRankInterpretationBoundary
dynamicRankBoundary = DynamicRank.canonicalDynamicRankInterpretationBoundary

productionScaleBoundary : Scale.ProductionScaleReconstructionBoundary
productionScaleBoundary = Scale.canonicalProductionScaleReconstructionBoundary

------------------------------------------------------------------------
-- Concrete witness: the current (r80,h80) observer does not determine d.
------------------------------------------------------------------------

data OffsetWorld : Set where
  degree65At512x65 : OffsetWorld
  degree66At512x65 : OffsetWorld

data DynamicObserver : Set where
  observedR80_512H80_65 : DynamicObserver

data OffsetConsumer : Set where
  explainFiniteHorizonOffset : OffsetConsumer

data GeneratorDegreeAnswer : Set where
  generatorDegree65 : GeneratorDegreeAnswer
  generatorDegree66 : GeneratorDegreeAnswer

offsetObserve : OffsetWorld → DynamicObserver
offsetObserve _ = observedR80_512H80_65

offsetAnswer : OffsetConsumer → OffsetWorld → GeneratorDegreeAnswer
offsetAnswer explainFiniteHorizonOffset degree65At512x65 = generatorDegree65
offsetAnswer explainFiniteHorizonOffset degree66At512x65 = generatorDegree66

offsetSystem : Fibre.ConsumerIndexedFibreSystem
offsetSystem = Fibre.consumerIndexedFibreSystem
  OffsetWorld
  DynamicObserver
  OffsetConsumer
  GeneratorDegreeAnswer
  offsetObserve
  offsetAnswer
  "RSA-260 synthetic bidi offset consumer: the current (r80,h80) dynamic observer cannot distinguish generator degree 65 from 66 at the shared observed summary (512,65)."

offsetCollision :
  Fibre.SameObservationDifferentConsumerAnswer
    offsetSystem explainFiniteHorizonOffset
offsetCollision = Fibre.sameObservationDifferentConsumerAnswer
  degree65At512x65
  degree66At512x65
  refl
  (λ ())

offsetDefect :
  Fibre.ConsumerAdequacyDefect offsetSystem explainFiniteHorizonOffset
offsetDefect = Fibre.sameObservationDifferentAnswerGivesDefect offsetCollision

------------------------------------------------------------------------
-- Existing scheduler specialization: name the missing coordinate, then route
-- its producer.  This is not a new planner.
------------------------------------------------------------------------

data OffsetMissingCoordinate : Set where
  blockInvariantFactorMinimalGeneratorStructure : OffsetMissingCoordinate

data OffsetProducer : Set where
  invariantFactorDiscriminatorExperiment : OffsetProducer

offsetMissingCoordinateFor : OffsetConsumer → OffsetMissingCoordinate
offsetMissingCoordinateFor _ = blockInvariantFactorMinimalGeneratorStructure

offsetProducerFor : OffsetMissingCoordinate → OffsetProducer
offsetProducerFor blockInvariantFactorMinimalGeneratorStructure =
  invariantFactorDiscriminatorExperiment

offsetSchedule : Scheduler.RefinementSchedule offsetSystem
offsetSchedule = Scheduler.refinementSchedule
  OffsetMissingCoordinate
  OffsetProducer
  offsetMissingCoordinateFor
  offsetProducerFor

liveOffsetResidual :
  Scheduler.ConsumerRefinementResidual
    offsetSchedule explainFiniteHorizonOffset
liveOffsetResidual = Scheduler.consumerRefinementResidual
  offsetDefect
  blockInvariantFactorMinimalGeneratorStructure
  refl
  invariantFactorDiscriminatorExperiment
  refl

------------------------------------------------------------------------
-- Scheduled discriminator experiment.
--
-- The signature language is deliberately only rich enough to separate the
-- concrete live witness pair.  Executing a real invariant-factor/minimal-
-- generator computation remains future work; this object is the experiment
-- demand, not an execution receipt.
------------------------------------------------------------------------

data InvariantFactorSignature : Set where
  signatureForDegree65Case : InvariantFactorSignature
  signatureForDegree66Case : InvariantFactorSignature

invariantFactorSignature : OffsetWorld → InvariantFactorSignature
invariantFactorSignature degree65At512x65 = signatureForDegree65Case
invariantFactorSignature degree66At512x65 = signatureForDegree66Case

invariantFactorExperiment : Synthesis.ExperimentBundle OffsetWorld
invariantFactorExperiment = Synthesis.experimentBundle
  InvariantFactorSignature
  invariantFactorSignature
  1
  "RSA260 block invariant-factor/minimal-generator discriminator for the live finite-horizon offset residual"
  "synthetic paired-case calibration; production A*/F.sols* acquisition remains separate"

invariantFactorExperimentSeparatesLiveWitness :
  Synthesis.BundleSeparates
    invariantFactorExperiment
    degree65At512x65
    degree66At512x65
invariantFactorExperimentSeparatesLiveWitness =
  Synthesis.bundleSeparates (λ ())

offsetExperimentDemand :
  Loop.ConsumerDefectExperimentDemand
    offsetSchedule explainFiniteHorizonOffset
offsetExperimentDemand = Loop.consumer-defect-experiment-demand
  liveOffsetResidual
  invariantFactorExperiment
  invariantFactorExperimentSeparatesLiveWitness
  (λ _ → ⊤)
  tt
  LeastPrivilege.canonicalRouteAdmission
  "synthetic block invariant-factor/minimal-generator offset discriminator"
  "least-privilege route admitted for the same live RSA-260 offset residual"

offsetExperimentBinding :
  Introspective.ConsumerDefectExperimentBinding liveOffsetResidual
offsetExperimentBinding =
  Introspective.consumer-defect-experiment-binding offsetExperimentDemand refl

offsetExperimentPaysLiveResidual :
  Loop.residual (Introspective.demand offsetExperimentBinding)
  ≡ liveOffsetResidual
offsetExperimentPaysLiveResidual =
  Introspective.demandResidualMatchesLiveResidual offsetExperimentBinding

------------------------------------------------------------------------
-- Introspective ZKP audit frame.  O/R/C/S/L/P/G/F are references only.
------------------------------------------------------------------------

offsetRepairFrame : Introspective.ZKPFrame
offsetRepairFrame = Introspective.zkp-frame
  "O: chboishabba/dashi_agda + chboishabba/dashiRTX"
  "R: draft PR #875; live residual explainFiniteHorizonOffsetExceptions"
  "C: finite-horizon blob 80509498988c47f13a3602c431e60bcca65006af; dynamic-rank blob b4fd8b1fef6f31a28b227b42cde1bd47ac74fb5f"
  "S: tested d-h80 envelope is {-1,0,+1}; current (r80,h80) observer is progress but not closure"
  "L: consumer observer carries reachable Krylov rank r80 and finite-horizon saturation h80"
  "P: compute block invariant-factor/minimal-generator signature for the concrete offset collision"
  "G: predict generator degree d without collapsing preparation/projection dependence"
  "F: explain the surviving finite-horizon offset exceptions for the same live consumer residual"

------------------------------------------------------------------------
-- Status: introspective progress, explicitly not consumer closure.
------------------------------------------------------------------------

record OffsetRepairIntrospectiveBoundary : Set where
  constructor offset-repair-introspective-boundary
  field
    currentR80H80ObserverHasConcreteConsumerDefect : Bool
    missingCoordinateIsInvariantFactorMinimalGeneratorStructure : Bool
    scheduledExperimentBindsSameLiveResidual : Bool
    zkpFrameIsAuditMetadataOnly : Bool
    existingFiniteHorizonResultCountsAsProgress : Bool
    invariantFactorExperimentAlreadyExecuted : Bool
    consumerRefinementReceiptPaid : Bool
    offsetResidualClosed : Bool
    productionAStarOrFSolsAcquisitionRemainsSeparate : Bool
open OffsetRepairIntrospectiveBoundary public

canonicalOffsetRepairIntrospectiveBoundary : OffsetRepairIntrospectiveBoundary
canonicalOffsetRepairIntrospectiveBoundary =
  offset-repair-introspective-boundary
    true
    true
    true
    true
    true
    false
    false
    false
    true

------------------------------------------------------------------------
-- Next experiment and production acquisition stay separate.
------------------------------------------------------------------------

data OffsetRepairResidual : Set where
  runInvariantFactorMinimalGeneratorExperiment : OffsetRepairResidual
  compileExperimentIntoRefinedObserver : OffsetRepairResidual
  proveConsumerDescendsThroughRefinedObserver : OffsetRepairResidual
  acquireSameObjectAStarOrFSolsForProductionDiagnostic : OffsetRepairResidual

firstOffsetRepairResidual : OffsetRepairResidual
firstOffsetRepairResidual = runInvariantFactorMinimalGeneratorExperiment

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data ExperimentDemandMeansExperimentExecuted : Set where
data ExperimentBindingMeansConsumerClosure : Set where
data ZKPFrameMeansEvidence : Set where
data SyntheticOffsetExplanationMeansProductionIdentity : Set where

experimentDemandDoesNotMeanExecuted : ExperimentDemandMeansExperimentExecuted → ⊥
experimentDemandDoesNotMeanExecuted ()

experimentBindingDoesNotCloseConsumer : ExperimentBindingMeansConsumerClosure → ⊥
experimentBindingDoesNotCloseConsumer ()

zkpFrameDoesNotCreateEvidence : ZKPFrameMeansEvidence → ⊥
zkpFrameDoesNotCreateEvidence ()

syntheticOffsetExplanationDoesNotCreateProductionIdentity :
  SyntheticOffsetExplanationMeansProductionIdentity → ⊥
syntheticOffsetExplanationDoesNotCreateProductionIdentity ()
