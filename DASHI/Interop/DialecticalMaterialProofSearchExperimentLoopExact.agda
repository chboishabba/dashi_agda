module DASHI.Interop.DialecticalMaterialProofSearchExperimentLoopExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.ConsumerIndexedTrajectoryFibreAdequacyExact as Fibre
import DASHI.Core.ConsumerFibreRefinementSchedulerExact as Scheduler
import DASHI.Core.DiscriminatorSynthesisExact as Synthesis
import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice
import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as LeastPrivilege
import DASHI.Interop.DialecticalMaterialSourceDiligenceReopeningExact as MaterialSource

------------------------------------------------------------------------
-- DIALECTICAL MATERIAL PROOF SEARCH / EXPERIMENT LOOP
--
-- A consumer-relative observation defect can motivate further inquiry, but it
-- does not determine whether the next highest-alpha move is source research,
-- observation, perturbation, fidelity escalation, or immediate closure after a
-- separately supplied refinement.  This owner is only the junction between the
-- already-existing source-diligence and experiment/refinement calculi.
------------------------------------------------------------------------

private
  variable
    system : Fibre.ConsumerIndexedFibreSystem

------------------------------------------------------------------------
-- Experimental repair must address the actual non-factorability witness, not
-- merely produce a new coordinate or an interesting measurement.
------------------------------------------------------------------------

record ConsumerDefectExperimentDemand
    (schedule : Scheduler.RefinementSchedule system)
    (consumer : Fibre.Consumer system) : Set₂ where
  constructor consumer-defect-experiment-demand
  field
    residual : Scheduler.ConsumerRefinementResidual schedule consumer
    experiment : Synthesis.ExperimentBundle (Fibre.State system)
    separatesDefectWitness :
      Synthesis.BundleSeparates
        experiment
        (NF.left (Scheduler.defect residual))
        (NF.right (Scheduler.defect residual))

    AdmittedExperiment :
      Choice.InformationMove → Set
    experimentAdmission :
      AdmittedExperiment (Synthesis.bundleInformationMove experiment)

    routeAdmission : LeastPrivilege.RouteAdmission
    experimentReference : String
    admissionReference : String

open ConsumerDefectExperimentDemand public

------------------------------------------------------------------------
-- The next step is explicitly typed.  Source diligence, experiment, and closure
-- are alternatives; none is manufactured merely from the existence of a defect.
------------------------------------------------------------------------

data ConsumerRefinementStep
    (schedule : Scheduler.RefinementSchedule system)
    (consumer : Fibre.Consumer system) : Set₂ where

  acquireSource :
    MaterialSource.DialecticalSourceReopening →
    ConsumerRefinementStep schedule consumer

  runDiscriminatingExperiment :
    ConsumerDefectExperimentDemand schedule consumer →
    ConsumerRefinementStep schedule consumer

  closeConsumerAfterRefinement :
    Fibre.ConsumerRefinementReceipt system consumer →
    ConsumerRefinementStep schedule consumer

------------------------------------------------------------------------
-- A completed experiment result is not itself closure.  Applications must
-- compile the result into a refined observer and prove that the target descends.
------------------------------------------------------------------------

record ExperimentToConsumerClosure
    (schedule : Scheduler.RefinementSchedule system)
    (consumer : Fibre.Consumer system) : Set₂ where
  constructor experiment-to-consumer-closure
  field
    demand : ConsumerDefectExperimentDemand schedule consumer
    refinedReceipt : Fibre.ConsumerRefinementReceipt system consumer
    resultReference : String
    refinementReference : String

open ExperimentToConsumerClosure public

experimentClosureStep :
  ∀ {schedule : Scheduler.RefinementSchedule system}
    {consumer : Fibre.Consumer system} →
  ExperimentToConsumerClosure schedule consumer →
  ConsumerRefinementStep schedule consumer
experimentClosureStep closure =
  closeConsumerAfterRefinement (refinedReceipt closure)

------------------------------------------------------------------------
-- The experimental bundle can be reused by the existing sequential planner.
-- This adapter is intentionally definitional and adds no new search semantics.
------------------------------------------------------------------------

experimentInformationMove :
  ∀ {schedule : Scheduler.RefinementSchedule system}
    {consumer : Fibre.Consumer system} →
  ConsumerDefectExperimentDemand schedule consumer →
  Choice.InformationMove
experimentInformationMove demand =
  Synthesis.bundleInformationMove (experiment demand)

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ConsumerDefectSelectsExperimentPermission : Set where

data PairwiseExperimentSeparationMeansConsumerClosurePermission : Set where

data ExperimentAdmissionCreatesInterventionAuthorityPermission : Set where

data SourceGapMustBePaidByPhysicalExperimentPermission : Set where

data MaterialContradictionMeansRefutationPermission : Set where

consumerDefectDoesNotSelectExperimentByItself :
  ConsumerDefectSelectsExperimentPermission → ⊥
consumerDefectDoesNotSelectExperimentByItself ()

pairwiseSeparationDoesNotAutoCloseConsumer :
  PairwiseExperimentSeparationMeansConsumerClosurePermission → ⊥
pairwiseSeparationDoesNotAutoCloseConsumer ()

experimentAdmissionDoesNotCreateInterventionAuthority :
  ExperimentAdmissionCreatesInterventionAuthorityPermission → ⊥
experimentAdmissionDoesNotCreateInterventionAuthority ()

sourceGapNeedNotBePaidByPhysicalExperiment :
  SourceGapMustBePaidByPhysicalExperimentPermission → ⊥
sourceGapNeedNotBePaidByPhysicalExperiment ()

materialContradictionDoesNotAutoRefute :
  MaterialContradictionMeansRefutationPermission → ⊥
materialContradictionDoesNotAutoRefute ()

------------------------------------------------------------------------
-- Boundary receipt.
------------------------------------------------------------------------

record DialecticalMaterialProofSearchExperimentBoundary : Set where
  constructor dialectical-material-proof-search-experiment-boundary
  field
    consumerDefectMayScheduleFurtherInquiry : Bool
    sourceResearchAndExperimentAreDistinctRoutes : Bool
    experimentMustSeparateConcreteDefectWitness : Bool
    pairwiseSeparationAloneClosesConsumer : Bool
    experimentalResultStillNeedsRefinementReceipt : Bool
    routeNeedsLeastPrivilegeAdmission : Bool
    contradictionAloneRefutesCurrentModel : Bool

canonicalDialecticalMaterialProofSearchExperimentBoundary :
  DialecticalMaterialProofSearchExperimentBoundary
canonicalDialecticalMaterialProofSearchExperimentBoundary =
  dialectical-material-proof-search-experiment-boundary
    true true true false true true false
