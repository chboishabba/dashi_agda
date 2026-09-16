module DASHI.Wikimedia.IbrahimPesticideExperimentDesignParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimPesticideStandardsAustraliaUSEUComparisonParetoExact as Standards
import DASHI.Wikimedia.IbrahimCannabisTobaccoCoSmokeExposureParetoExact as CoSmoke
import DASHI.Wikimedia.IbrahimCannabisThermalTransferEvidenceGradeExact as Thermal
import DASHI.Wikimedia.IbrahimCannabisBtHarvestResidueAcquisitionResidualExact as BtHarvest
import DASHI.Wikimedia.IbrahimCannabisGlyphosateAMPAPyrolysisParetoExact as Glyphosate

------------------------------------------------------------------------
-- PESTICIDE / CONTAMINANT EXPERIMENT-DESIGN PARETO BRIDGE
--
-- Existing DASHI experiment discipline reused here:
--
--   State / Control / Observation / Experiment / Residual
--
-- A new measurement is justified only when the current observer erases a
-- distinction required by the declared scientific consumer.  Admissibility
-- is checked before Pareto ranking.  A Pareto front does not manufacture a
-- preferred experiment or intervention authority.
------------------------------------------------------------------------

data ScientificConsumer : Set where
  inhaledDoseConsumer
  mixedCombustionInteractionConsumer
  btHarvestBurdenConsumer
  glyphosateOccurrenceConsumer
  regulatoryModelFreshnessConsumer
  nonFoodToFoodLifecycleConsumer : ScientificConsumer

data ExperimentFamily : Set where
  sameMaterialThreeArmCombustion
  matchedCannabisVapeTransfer
  btPostApplicationHarvestSeries
  glyphosateAMPADedicatedSurvey
  exposurePriorBacktest
  nonFoodFoodLifecycleResidueFollowup : ExperimentFamily

data ObservationClass : Set where
  sourceResidueVector
  mainstreamSmokeParentVector
  emittedAerosolParentVector
  thermalProductVector
  viableBtCount
  btStrainIdentity
  cryVipProteinBurden
  glyphosateAMPAVector
  consumptionDistribution
  legalMarketState : ObservationClass

record ExperimentCarrier : Set where
  constructor experiment-carrier
  field
    family : ExperimentFamily
    declaredConsumer : ScientificConsumer
    sourceObjectIdentity : String
    controls : String
    observations : String
    residual : String
    heldOutOrSameObjectValidation : String
    admissible : Bool
    executesSameObjectComparison : Bool
    consumerAdequacyPaid : Bool
open ExperimentCarrier public

------------------------------------------------------------------------
-- Priority 0: same-material three-arm combustion.
--
-- This is the cheapest direct discriminator for the currently open question
-- whether mixed cannabis+tobacco smoke can be reconstructed from the two
-- separate source streams.  It keeps material identity, starting residue
-- vectors and smoking-machine conditions fixed across arms.
------------------------------------------------------------------------

threeArmCoSmokeExperiment : ExperimentCarrier
threeArmCoSmokeExperiment = experiment-carrier
  sameMaterialThreeArmCombustion
  mixedCombustionInteractionConsumer
  "one homogenized cannabis source object plus one homogenized tobacco source object; aliquots split across all arms"
  "arm C: cannabis only; arm T: tobacco only; arm CT: fixed cannabis:tobacco mass ratio; same paper/device/filter, puff protocol, conditioning, replicate schedule and starting residue assay"
  "pre-burn source residue vectors; mainstream smoke parent residues; thermal-product vector; total particulate matter; water/moisture; replicate uncertainty"
  "Rmix = Q(CT) - [Q(C) + Q(T)] after mass normalization; non-zero residual witnesses non-additive mixed-combustion behaviour"
  "blind replicate aliquots from the same homogenized source materials; predeclared held-out replicate block"
  true true true

------------------------------------------------------------------------
-- Priority 1: Bt harvest burden.
------------------------------------------------------------------------

btHarvestSeriesExperiment : ExperimentCarrier
btHarvestSeriesExperiment = experiment-carrier
  btPostApplicationHarvestSeries
  btHarvestBurdenConsumer
  "same cannabis cultivar/batch grown under one controlled production protocol; exact registered Bt product, strain, rate and application timing recorded"
  "untreated control plus labelled-application arms; fixed harvest/drying protocol; repeated sampling from application through harvest"
  "total viable Bacillus count; strain-specific qPCR; Cry/Vip protein assay where strain complement is paid; moisture and ordinary microbial counts retained separately"
  "post-application Bt burden trajectory minus untreated background; generic TAMC must not substitute for strain identity"
  "same-plant / same-batch longitudinal identity where feasible, otherwise randomized plant-level blocks with blinded lab identifiers"
  true true true

------------------------------------------------------------------------
-- Priority 2: dedicated glyphosate/AMPA survey.
------------------------------------------------------------------------

glyphosateSurveyExperiment : ExperimentCarrier
glyphosateSurveyExperiment = experiment-carrier
  glyphosateAMPADedicatedSurvey
  glyphosateOccurrenceConsumer
  "retail dried-cannabis samples with market/jurisdiction/product identifiers retained"
  "dedicated validated cannabis-matrix polar-analyte method; blanks, spikes, isotopic internal standards where method supports them; legal/illicit source classes separated"
  "glyphosate, AMPA, matrix recovery, LOD, LOQ, uncertainty and sample mass"
  "observed occurrence and concentration distributions; ordinary multiresidue-panel non-detection is not imported as absence"
  "predeclared train/calibration versus held-out QC material; duplicate extraction subset"
  true true true

------------------------------------------------------------------------
-- Priority 3: regulatory prior backtest.
------------------------------------------------------------------------

exposurePriorBacktestExperiment : ExperimentCarrier
exposurePriorBacktestExperiment = experiment-carrier
  exposurePriorBacktest
  regulatoryModelFreshnessConsumer
  "same pesticide-food pair evaluated under historical and contemporary consumption distributions"
  "freeze toxicological endpoint and residue assumption; vary only consumption distribution / body-weight population inputs"
  "acute and chronic exposure outputs, population percentile, reference dose fraction, decision-state crossing"
  "decision delta attributable to exposure-prior refresh rather than changed hazard"
  "reproduce historical decision with archived inputs, then evaluate contemporary held-out survey distribution"
  true true true

------------------------------------------------------------------------
-- Priority 4: non-food -> food lifecycle.
------------------------------------------------------------------------

lifecycleResidueExperiment : ExperimentCarrier
lifecycleResidueExperiment = experiment-carrier
  nonFoodFoodLifecycleResidueFollowup
  nonFoodToFoodLifecycleConsumer
  "same treated perennial plant followed from permitted non-bearing state into later bearing state"
  "treated versus untreated plants; exact product/rate/application carrier; fixed horticultural conditions; repeated tissue/soil/fruit sampling"
  "active ingredient and metabolites in substrate/root/leaf/fruit through time; legal market state and bearing state recorded"
  "downstream edible-state residue minus control; explicitly tests whether non-food treatment leaves a consumer-relevant later residue"
  "longitudinal same-plant identity plus blinded analytical replicates"
  true true true

------------------------------------------------------------------------
-- Observer collisions: if these pairs collapse under the current projection,
-- downstream scoring cannot repair the missing distinction.
------------------------------------------------------------------------

record ObserverCollision : Set where
  constructor observer-collision
  field
    consumer : ScientificConsumer
    coarseObserver : String
    worldA : String
    worldB : String
    sameCoarseObservation : Bool
    differentConsumerAnswer : Bool
    missingCoordinate : String
open ObserverCollision public

coSmokeCollision : ObserverCollision
coSmokeCollision = observer-collision
  mixedCombustionInteractionConsumer
  "source residue vectors only"
  "mixed burn is additive"
  "mixed burn changes transfer / thermal products"
  true true
  "mixed-arm emitted smoke/aerosol observation"

btCollision : ObserverCollision
btCollision = observer-collision
  btHarvestBurdenConsumer
  "generic microbial count only"
  "background Bacillus burden"
  "applied Btk strain persists"
  true true
  "strain-specific identity and/or Cry/Vip burden"

glyphosateCollision : ObserverCollision
glyphosateCollision = observer-collision
  glyphosateOccurrenceConsumer
  "conventional GC/LC multiresidue panel"
  "glyphosate absent"
  "glyphosate present but outside observer chemistry"
  true true
  "dedicated glyphosate/AMPA measurement"

priorCollision : ObserverCollision
priorCollision = observer-collision
  regulatoryModelFreshnessConsumer
  "hazard + MRL without dated consumption distribution"
  "historical consumption"
  "contemporary higher niche-food consumption"
  true true
  "dated population consumption distribution"

------------------------------------------------------------------------
-- Hard firewalls.
------------------------------------------------------------------------

data MoreAnalytesRepairObserverCollision : Set where
data ParetoFrontCreatesPreferredExperiment : Set where
data PredictiveAdequacyCreatesInterventionAuthority : Set where
data CalibrationFitCreatesHeldOutValidation : Set where
data DifferentMaterialCreatesSameObjectTransferProof : Set where

moreAnalytesDoNotRepairObserverCollision : MoreAnalytesRepairObserverCollision → ⊥
moreAnalytesDoNotRepairObserverCollision ()

paretoDoesNotCreatePreferredExperiment : ParetoFrontCreatesPreferredExperiment → ⊥
paretoDoesNotCreatePreferredExperiment ()

predictiveAdequacyDoesNotCreateAuthority : PredictiveAdequacyCreatesInterventionAuthority → ⊥
predictiveAdequacyDoesNotCreateAuthority ()

calibrationDoesNotCreateHeldOutValidation : CalibrationFitCreatesHeldOutValidation → ⊥
calibrationDoesNotCreateHeldOutValidation ()

differentMaterialDoesNotCreateSameObjectProof : DifferentMaterialCreatesSameObjectTransferProof → ⊥
differentMaterialDoesNotCreateSameObjectTransferProof ()

------------------------------------------------------------------------
-- Pareto axes.  These are local experimental-design costs / information axes,
-- not dollars, ethical authority, or scientific truth.
------------------------------------------------------------------------

record ExperimentParetoProfile : Set where
  constructor experiment-pareto-profile
  field
    experiment : ExperimentCarrier
    priority : Nat
    unresolvedConsumerCoordinatesPaid : Nat
    sourceIdentityBurden : Nat
    assayModalityBurden : Nat
    executionComplexity : Nat
    longitudinalBurden : Nat
    routeSpecificInformationGain : Nat
open ExperimentParetoProfile public

coSmokeProfile : ExperimentParetoProfile
coSmokeProfile = experiment-pareto-profile
  threeArmCoSmokeExperiment 0 3 2 3 3 1 5

btProfile : ExperimentParetoProfile
btProfile = experiment-pareto-profile
  btHarvestSeriesExperiment 1 3 3 4 4 5 3

glyphosateProfile : ExperimentParetoProfile
glyphosateProfile = experiment-pareto-profile
  glyphosateSurveyExperiment 2 2 2 3 3 1 2

priorProfile : ExperimentParetoProfile
priorProfile = experiment-pareto-profile
  exposurePriorBacktestExperiment 3 2 1 1 2 2 1

lifecycleProfile : ExperimentParetoProfile
lifecycleProfile = experiment-pareto-profile
  lifecycleResidueExperiment 4 2 5 3 5 5 1

------------------------------------------------------------------------
-- Cheap-to-expensive escalation rule reused from existing experiment design:
-- if a cheaper observer can answer the consumer, do not automatically escalate
-- to a maximal experiment.  If it cannot, retain the collision as the typed
-- witness justifying refinement.
------------------------------------------------------------------------

record AdaptiveExperimentEscalation : Set where
  constructor adaptive-experiment-escalation
  field
    firstTry : String
    collisionTest : String
    refinement : String
    stopCondition : String
open AdaptiveExperimentEscalation public

canonicalEscalation : AdaptiveExperimentEscalation
canonicalEscalation = adaptive-experiment-escalation
  "reuse existing residue / surveillance packets first"
  "look for two admissible worlds with the same current observation but different consumer answer"
  "add only the missing coordinate or run the smallest experiment that measures it"
  "stop when the declared consumer factors through the refined observer with held-out / same-object validation"

record PesticideExperimentDesignBoundary : Set where
  constructor pesticide-experiment-design-boundary
  field
    observerAdequacyBeforeRanking : Bool
    admissibilityBeforePareto : Bool
    paretoFrontCreatesAuthority : Bool
    heldOutValidationSeparateFromCalibration : Bool
    sameObjectIdentityRequired : Bool
    cheapestAdequateEscalationPreferred : Bool
    moreAnalytesAlwaysHigherPriority : Bool
open PesticideExperimentDesignBoundary public

canonicalPesticideExperimentDesignBoundary : PesticideExperimentDesignBoundary
canonicalPesticideExperimentDesignBoundary =
  pesticide-experiment-design-boundary true true false true true true false
