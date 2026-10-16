module DASHI.Biology.KitzerowBH4NeuralContextDiscriminatorExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.KitzerowBH4FluxCausalModelsExact as Flux
import DASHI.Biology.KitzerowBH4NeuralContextSourceAtlasExact as Sources

------------------------------------------------------------------------
-- NEURAL / DEVELOPMENTAL CONTEXT DISCRIMINATOR
--
-- These studies directly test a failure mode of a simple current-pool model:
-- if present total BH4 is the only relevant allocator coordinate, restoring
-- BH4 should restore the corresponding monoamine outputs.  In hph-1 and Gch1
-- deficiency models that implication fails.  The evidence instead forces
-- developmental history, enzyme abundance, anatomical region and branch state
-- to remain explicit coordinates.
------------------------------------------------------------------------

record NeuralContextObservation : Set where
  constructor neuralContextObservation
  field
    source : Source.AttributedSource
    system : String
    perturbation : String
    bh4State : String
    branchReadouts : String
    interventionOrRescue : String
    observedOutcome : String
    causalAlternativeConstraint : String
    remainingResidual : String

open NeuralContextObservation public

hph1Observation : NeuralContextObservation
hph1Observation =
  neuralContextObservation
    Sources.hylandEtAl1996Hph1
    "hph-1 mouse with reduced GTP cyclohydrolase-I activity"
    "chronic inherited/developmental BH4 deficiency"
    "brain BH4 deficient; chronic subcutaneous BH4 raised brain BH4 above control values"
    "brain dopamine, norepinephrine, serotonin and metabolites; in-vivo TH/TPH activity; striatal TH and liver PAH activity/protein"
    "chronic subcutaneous BH4 supplementation"
    "monoamine metabolism did not recover despite brain BH4 restoration above control; TH/TPH activities were reduced and lower hydroxylase activity reflected reduced enzyme abundance"
    "present total BH4 concentration alone is insufficient to identify downstream monoamine function after chronic/developmental deficiency; enzyme-state/history remains a causal coordinate"
    "mouse model; does not pay human neural flux, NOS/AGMO allocation or autism causation"

ptsKOObservation : NeuralContextObservation
ptsKOObservation =
  neuralContextObservation
    Sources.sumiIchinoseEtAl2001PtsKO
    "6-pyruvoyltetrahydropterin synthase knockout mouse neonates"
    "near-complete inability to synthesize BH4 through the canonical de-novo pathway"
    "brain biopterin extremely low in homozygous mutants"
    "catecholamines, serotonin, TH abundance and reported differential impact across catecholaminergic/serotonergic/NO systems"
    "genetic BH4 synthesis ablation rather than acute pharmacological depletion"
    "catecholamines and serotonin were both strongly affected, but BH4 starvation did not act as one uniform branch-scaling factor; TH abundance itself was BH4-dependent"
    "branch identity and enzyme abundance are state variables, not mere readouts of one scalar shared-pool coordinate"
    "perinatal knockout is a severe context and does not quantify adult human branch competition"

jiang2024Observation : NeuralContextObservation
jiang2024Observation =
  neuralContextObservation
    Sources.jiangEtAl2024Gch1Therapy
    "Gch1 KI/KI mouse model of GTP cyclohydrolase-I deficiency"
    "genetic GCH1 deficiency with dopa/BH4 therapy across development"
    "high-dose BH4 restored total brain BH4; liver BH4 synthesis/regeneration transcripts increased while brain transcripts did not show the same response"
    "brain dopamine, total-brain TH, striatal TH, growth/motor phenotype and liver-versus-brain transcriptional response"
    "BH4 supplementation alone and combined dopa + BH4 therapy"
    "brain dopamine deficiency persisted despite restored total brain BH4; total-brain TH increased relatively but striatal TH remained almost undetectable; rescue efficacy depended on developmental stage and combined therapy"
    "anatomical region, developmental timing and enzyme-state history separate total-pool restoration from functional recovery; context-specific/subgroup architecture stays live"
    "mouse disease model; does not establish the same response in humans or prove the whole Kitzerow model"

canonicalNeuralContextObservations : List NeuralContextObservation
canonicalNeuralContextObservations =
  hph1Observation ∷ ptsKOObservation ∷ jiang2024Observation ∷ []

record NeuralContextDiscriminator : Set where
  constructor neuralContextDiscriminator
  field
    targetModelReference : String
    simpleModelPrediction : String
    observedCounterexampleReference : String
    refinedModelReference : String
    remainingExperiment : String

open NeuralContextDiscriminator public

canonicalNeuralContextDiscriminator : NeuralContextDiscriminator
canonicalNeuralContextDiscriminator =
  neuralContextDiscriminator
    "KitzerowBH4FluxCausalModelsExact H1 upstream allocator versus H4 context-specific/developmental mechanism"
    "simple current-pool sufficiency model: restoring total BH4 should restore downstream monoamine branch function if present BH4 concentration is the sole limiting causal coordinate"
    "hph-1 chronic BH4 supplementation and Gch1 KI/KI high-dose BH4 restore brain BH4 without corresponding monoamine/dopamine rescue; PTPS knockout additionally shows branch-differential dependence and BH4-dependent TH abundance"
    "retain BH4 pool as a causal coordinate but augment with enzyme abundance, developmental history, anatomical region, cell type, branch identity, redox state and timing; this is closer to H4/context-specific or an adaptive-state H1 than a scalar fixed-pool model"
    "target-relevant human/neural same-object perturbation with BH4/BH2, NAD(P)H, enzyme abundance/localization and branch flux resolved by region/cell type/time"

record NeuralContextBoundary : Set where
  constructor neuralContextBoundary
  field
    brainBH4RestoredWithoutMonoamineRescue : Bool
    brainBH4RestoredWithoutMonoamineRescueIsTrue : brainBH4RestoredWithoutMonoamineRescue ≡ true
    brainBH4RestoredWithoutDopamineRescue : Bool
    brainBH4RestoredWithoutDopamineRescueIsTrue : brainBH4RestoredWithoutDopamineRescue ≡ true
    enzymeAbundanceStateMatters : Bool
    enzymeAbundanceStateMattersIsTrue : enzymeAbundanceStateMatters ≡ true
    brainRegionContextMatters : Bool
    brainRegionContextMattersIsTrue : brainRegionContextMatters ≡ true
    developmentalTimingMatters : Bool
    developmentalTimingMattersIsTrue : developmentalTimingMatters ≡ true
    currentBH4PoolStillCausallyRelevant : Bool
    currentBH4PoolStillCausallyRelevantIsTrue : currentBH4PoolStillCausallyRelevant ≡ true
    simpleCurrentPoolSufficiencySupported : Bool
    simpleCurrentPoolSufficiencySupportedIsFalse : simpleCurrentPoolSufficiencySupported ≡ false
    contextSpecificArchitectureSupportedAsLiveAlternative : Bool
    contextSpecificArchitectureSupportedAsLiveAlternativeIsTrue :
      contextSpecificArchitectureSupportedAsLiveAlternative ≡ true
    neuralEvidenceProvesWholeKitzerowModel : Bool
    neuralEvidenceProvesWholeKitzerowModelIsFalse : neuralEvidenceProvesWholeKitzerowModel ≡ false
    neuralEvidencePaysNOS_AGMOFlux : Bool
    neuralEvidencePaysNOS_AGMOFluxIsFalse : neuralEvidencePaysNOS_AGMOFlux ≡ false

open NeuralContextBoundary public

canonicalNeuralContextBoundary : NeuralContextBoundary
canonicalNeuralContextBoundary =
  neuralContextBoundary
    true refl true refl true refl true refl true refl true refl
    false refl true refl false refl false refl
