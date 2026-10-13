module DASHI.Cognition.MavenMinabPineGapTargetingChainExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Maven / Minab / Pine Gap operational-chain boundary.
------------------------------------------------------------------------

record TargetingChainBoundary : Set where
  constructor targeting-chain-boundary
  field
    projectMavenLaunched2017Paid : Bool
    googleEarlyMavenParticipationPaid : Bool
    workerOppositionAndNonRenewalPaid : Bool
    palantirMavenSmartSystemPaid : Bool
    palantir2024Maven480mPaid : Bool
    palantir2025Maven795mExpansionPaid : Bool
    palantir2026CoreProgramStatusPaid : Bool
    mavenUsedInIran2026Paid : Bool
    minabSchoolStrikeAndStaleTargetDataPaid : Bool
    reportedAutomationBiasPaid : Bool
    mavenAloneCausedStrike : Bool
    pineGapFeedsUSMiddleEastTargetingChainPaid : Bool
    pineGapDatumToSpecificMinabStrikePaid : Bool
    humanInLoopEliminatesAutomationBias : Bool
open TargetingChainBoundary public

canonicalTargetingChainBoundary : TargetingChainBoundary
canonicalTargetingChainBoundary = targeting-chain-boundary
  true true true true true true true true true true false true false false

record TargetingReceipt : Set where
  constructor targeting-receipt
  field
    source : String
    boundedFinding : String
    relationPaid : Bool
open TargetingReceipt public

mavenOriginReceipt : TargetingReceipt
mavenOriginReceipt = targeting-receipt
  "US Department of Defense, Project Maven releases 2017"
  "DoD launched the Algorithmic Warfare Cross-Function Team / Project Maven in April 2017 to convert large intelligence-data streams into actionable intelligence and initially focused on computer vision for full-motion video."
  true

palantirExpansionReceipt : TargetingReceipt
palantirExpansionReceipt = targeting-receipt
  "US Department of Defense contracts 2024-05-29 and 2025-05-21; Reuters 2026-03-20"
  "Palantir received a $480m Maven Smart System contract in 2024, a $795m modification in 2025, and Maven was designated a core US military program in 2026."
  true

minabReceipt : TargetingReceipt
minabReceipt = targeting-receipt
  "Bloomberg 2026 kill-chain investigation; Guardian 2026 analysis"
  "Reporting on the Minab school strike describes stale underlying target intelligence entering the targeting chain and personnel relying on Maven Smart System under extreme operational tempo; this pays an automation-bias/system-data-failure concern, not sole software causation."
  true

pineGapIranReceipt : TargetingReceipt
pineGapIranReceipt = targeting-receipt
  "ABC Australia 2026 Pine Gap reporting"
  "Defence experts assessed Pine Gap intelligence as probably/all-but-certainly feeding US Middle-East operations and the targeting command chain during the Iran war; public evidence still does not trace a particular Pine Gap datum to the Minab strike."
  true

data HumanInLoopImpliesMeaningfulControl : Set where
data PipelineParticipationImpliesSpecificStrikeDatum : Set where
data AutomationBiasImpliesSoleMachineCause : Set where

humanLabelDoesNotCreateMeaningfulControl : HumanInLoopImpliesMeaningfulControl → ⊥
humanLabelDoesNotCreateMeaningfulControl ()

pipelineDoesNotCreateSpecificDatumAttribution :
  PipelineParticipationImpliesSpecificStrikeDatum → ⊥
pipelineDoesNotCreateSpecificDatumAttribution ()

automationBiasDoesNotCreateSoleMachineCause : AutomationBiasImpliesSoleMachineCause → ⊥
automationBiasDoesNotCreateSoleMachineCause ()
