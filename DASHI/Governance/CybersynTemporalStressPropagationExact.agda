module DASHI.Governance.CybersynTemporalStressPropagationExact where

-- DASHI-original finite temporal scenario semantics.
-- Source and empirical attribution follow Docs/SourceAttributionPolicy.md.
-- This is a reproducible symbolic stress experiment, NOT a 2026 calibration.
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Governance.CybersynCrossSectorScenarioExact as Scenario
import DASHI.Governance.CybersynGlobalViabilityMaxCutExact as Viability
import DASHI.Governance.CybersynPhysicalFinanceCutExact as Physical

-- A trace orders exogenous events. Source/claim promotion remains distinct
-- from this synthetic physical transmission schedule.
runShocks : List Scenario.Shock → Scenario.Exposures → Scenario.Exposures
runShocks [] state = state
runShocks (shock ∷ rest) state =
  runShocks rest (Scenario.applyShock shock state)

record IndexedEpisode : Set where
  constructor indexedEpisode
  field
    initialTime : Nat
    shocks : List Scenario.Shock
    startingExposures : Scenario.Exposures
    finalExposures : Scenario.Exposures
    replayExact :
      finalExposures ≡ runShocks shocks startingExposures

open IndexedEpisode public

replay : Nat → List Scenario.Shock →
  Scenario.Exposures → IndexedEpisode
replay t shocks start =
  indexedEpisode t shocks start (runShocks shocks start) refl

-- The credit/funding shock is not itself the cascade.  The conjunction
-- must be reached in a common time-indexed state to activate this toy rule.
singleYenEpisode : IndexedEpisode
singleYenEpisode =
  replay zero (Scenario.yenFundingReversal ∷ []) Scenario.noStress

coupledCreditEpisode : IndexedEpisode
coupledCreditEpisode =
  replay zero
    (Scenario.yenFundingReversal ∷
     Scenario.aiCollateralRepricing ∷ [])
    Scenario.noStress

yenOnlyNotCascade :
  Scenario.coupledCascade (finalExposures singleYenEpisode) ≡ false
yenOnlyNotCascade = refl

yenPlusCollateralCascade :
  Scenario.coupledCascade (finalExposures coupledCreditEpisode) ≡ true
yenPlusCollateralCascade = refl

-- The selected shocks commute as final exposure sets, but intermediate
-- states differ.  This retains the historical sequence rather than reducing
-- the trace to an unordered list of event names.
yenThenCollateral :
  Scenario.Exposures
yenThenCollateral =
  runShocks
    (Scenario.yenFundingReversal ∷
     Scenario.aiCollateralRepricing ∷ [])
    Scenario.noStress

collateralThenYen :
  Scenario.Exposures
collateralThenYen =
  runShocks
    (Scenario.aiCollateralRepricing ∷
     Scenario.yenFundingReversal ∷ [])
    Scenario.noStress

sameFinalExposure :
  yenThenCollateral ≡ collateralThenYen
sameFinalExposure = refl

data FirstSignal : Set where
  yenFundingSignal : FirstSignal
  aiCreditSignal : FirstSignal

firstSignal : List Scenario.Shock → FirstSignal
firstSignal [] = yenFundingSignal
firstSignal (Scenario.yenFundingReversal ∷ rest) = yenFundingSignal
firstSignal (Scenario.aiCollateralRepricing ∷ rest) = aiCreditSignal
firstSignal (_ ∷ rest) = yenFundingSignal

differentFirstSignal :
  firstSignal
    (Scenario.yenFundingReversal ∷
     Scenario.aiCollateralRepricing ∷ [])
  ≡
  firstSignal
    (Scenario.aiCollateralRepricing ∷
     Scenario.yenFundingReversal ∷ []) → ⊥
differentFirstSignal ()

-- The same end state does not identify which actor received information
-- first. That distinction affects response time, preemption and losses.
record TemporalCausalReceipt : Set where
  constructor temporalCausalReceipt
  field
    eventOrderPreserved : Bool
    actorObservationsPreserved : Bool
    sourceTimestampsPreserved : Bool
    counterfactualComparable : Bool
    empiricalCoefficientsAdmitted : Bool

open TemporalCausalReceipt public

candidateTraceOnly : TemporalCausalReceipt
candidateTraceOnly =
  temporalCausalReceipt true false false false false

-- Source-written synthetic replay is not an empirical causal forecast.
data SyntheticReplayImpliesEmpiricalForecast : Set where

syntheticReplayDoesNotValidateForecast :
  SyntheticReplayImpliesEmpiricalForecast → ⊥
syntheticReplayDoesNotValidateForecast ()

-- Counterfactual comparison is constructive only for a stated transition
-- model and shock sequence, not a claim of population-level policy effects.
record PairedPolicyExperiment (State Policy : Set) : Set₁ where
  constructor pairedPolicyExperiment
  field
    initialState : State
    baseline : Policy
    intervention : Policy
    simulate : Policy → State → State
    baselineOutcome : State
    interventionOutcome : State
    baselineExact : baselineOutcome ≡ simulate baseline initialState
    interventionExact :
      interventionOutcome ≡ simulate intervention initialState

open PairedPolicyExperiment public

data ToyPolicy : Set where
  retainHarm : ToyPolicy
  materialRepair : ToyPolicy

runPolicy : ToyPolicy → Viability.AccessState → Viability.AccessState
runPolicy retainHarm state = state
runPolicy materialRepair _ = Viability.constructionAccessOpen

toyPairedIntervention :
  PairedPolicyExperiment Viability.AccessState ToyPolicy
toyPairedIntervention =
  pairedPolicyExperiment
    Viability.constructionAccessBlocked
    retainHarm materialRepair runPolicy
    Viability.constructionAccessBlocked
    Viability.constructionAccessOpen
    refl refl

toyBaselineStaysBlocked :
  baselineOutcome toyPairedIntervention ≡
  Viability.constructionAccessBlocked
toyBaselineStaysBlocked = refl

toyInterventionChangesAccess :
  interventionOutcome toyPairedIntervention ≡
  Viability.constructionAccessOpen
toyInterventionChangesAccess = refl

-- Physical capacity and financial settlements still need independent
-- quantification, even when the stress trace is formally reproducible.
physicalAccountingOwner : Physical.CashAllocation
physicalAccountingOwner = Physical.allocateCash 3 2
