module DASHI.GameTheory.GameTheoryCompletionFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Core.ProofDebtRouterExact as Debt
import DASHI.GameTheory.StrategicInteractionCoreExact as Core
import DASHI.GameTheory.FiniteMixedStrategyExpectedUtilityExact as Mixed
import DASHI.GameTheory.AgenticStrategicInteractionBridgeExact as AgenticBridge
import DASHI.GameTheory.EvolutionaryStrategicSelectionBridgeExact as EvolutionBridge
import DASHI.GameTheory.RepeatedStrategicLearningMemoryBridgeExact as Repeated

------------------------------------------------------------------------
-- GAME THEORY COMPLETION FRONTIER
--
-- Definitions/carriers are not existence theorems.  In particular, having a
-- finite mixed-Nash type does not prove that every intended finite game
-- instantiates it.  Standard finite mixed-Nash existence is established
-- mathematics but remains untranscribed/source-unaligned in this lane, so the
-- correct next action is transcription audit rather than inventing a proof.
------------------------------------------------------------------------

data StandardGameTheoremFamily : Set where
  finiteMixedNashExistence : StandardGameTheoremFamily

standardGameTheoremRoute :
  StandardGameTheoremFamily → Debt.ProofDebtRoutingReceipt
standardGameTheoremRoute _ =
  Debt.proof-debt-routing-receipt
    Debt.deductiveTheorem
    Debt.sourceEstablished
    Debt.notTranscribed
    Debt.uncertified
    Debt.sourceOnly
    Debt.transcriptionDebt
    refl

finiteMixedNashExistenceNeedsTranscription :
  Debt.routedDebt (standardGameTheoremRoute finiteMixedNashExistence)
  ≡ Debt.transcriptionDebt
finiteMixedNashExistenceNeedsTranscription = refl

finiteMixedNashExistenceSchedulerAction :
  Debt.scheduleAction
    (Debt.routedDebt (standardGameTheoremRoute finiteMixedNashExistence))
    (Debt.statementStatus (standardGameTheoremRoute finiteMixedNashExistence))
    Debt.constrained32GB
    Debt.heavyReplay
  ≡ Debt.auditTranscription
finiteMixedNashExistenceSchedulerAction = refl

------------------------------------------------------------------------
-- Distinct open semantic coordinates.
------------------------------------------------------------------------

data GameTheoryResidual : Set where
  finiteMixedNashExistenceTheorem
  incompleteInformationBayesianSemantics
  extensiveFormSequentialRationality
  subgamePerfectEquilibrium
  evolutionaryStableStrategyInvasionSemantics
  replicatorOrPopulationFrequencyDynamics
  coalitionalCooperativeStability
  bargainingAndAllocationSemantics
  mechanismDesignIncentiveCompatibility
  empiricalStrategicModelIdentification : GameTheoryResidual

------------------------------------------------------------------------
-- Existing closed boundaries retained explicitly.
------------------------------------------------------------------------

strategicBoundary : Core.StrategicInteractionBoundary
strategicBoundary = Core.canonicalStrategicInteractionBoundary

mixedBoundary : Mixed.FiniteMixedStrategyBoundary
mixedBoundary = Mixed.canonicalFiniteMixedStrategyBoundary

agenticBoundary : AgenticBridge.AgenticStrategicBoundary
agenticBoundary = AgenticBridge.canonicalAgenticStrategicBoundary

evolutionaryBoundary : EvolutionBridge.EvolutionaryStrategicBoundary
evolutionaryBoundary = EvolutionBridge.canonicalEvolutionaryStrategicBoundary

repeatedLearningBoundary : Repeated.RepeatedStrategicLearningBoundary
repeatedLearningBoundary = Repeated.canonicalRepeatedStrategicLearningBoundary

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data MixedNashCarrierMeansExistenceTheoremPermission : Set where

data NashMeansBayesianEquilibriumPermission : Set where

data NashMeansSubgamePerfectPermission : Set where

data NashMeansESSPermission : Set where

data NashMeansCoalitionalStabilityPermission : Set where

data RepeatedLearningMeansFolkTheoremPermission : Set where

data UtilityMeansMechanismTruthfulnessPermission : Set where

mixedNashCarrierDoesNotProveExistence :
  MixedNashCarrierMeansExistenceTheoremPermission → ⊥
mixedNashCarrierDoesNotProveExistence ()

nashDoesNotBecomeBayesianEquilibrium : NashMeansBayesianEquilibriumPermission → ⊥
nashDoesNotBecomeBayesianEquilibrium ()

nashDoesNotBecomeSubgamePerfect : NashMeansSubgamePerfectPermission → ⊥
nashDoesNotBecomeSubgamePerfect ()

nashDoesNotBecomeESS : NashMeansESSPermission → ⊥
nashDoesNotBecomeESS ()

nashDoesNotBecomeCoalitionalStability :
  NashMeansCoalitionalStabilityPermission → ⊥
nashDoesNotBecomeCoalitionalStability ()

repeatedLearningDoesNotManufactureFolkTheorem :
  RepeatedLearningMeansFolkTheoremPermission → ⊥
repeatedLearningDoesNotManufactureFolkTheorem ()

utilityDoesNotManufactureTruthfulMechanism :
  UtilityMeansMechanismTruthfulnessPermission → ⊥
utilityDoesNotManufactureTruthfulMechanism ()

record GameTheoryCompletionFrontier : Set where
  constructor game-theory-completion-frontier
  field
    pureStrategicCoreClosed : Bool
    pureNashDefinitionClosed : Bool
    dominanceAndParetoClosed : Bool
    finiteMixedExpectedUtilityClosed : Bool
    finiteMixedNashDefinitionClosed : Bool
    agenticStrategicBridgeClosed : Bool
    evolutionarySelectionBridgeClosed : Bool
    repeatedLearningMemoryBridgeClosed : Bool
    finiteMixedNashExistenceNeedsSourceTranscription : Bool
    incompleteInformationClosed : Bool
    extensiveFormClosed : Bool
    evolutionaryStabilityClosed : Bool
    coalitionalCooperativeClosed : Bool
    mechanismDesignClosed : Bool

canonicalGameTheoryCompletionFrontier : GameTheoryCompletionFrontier
canonicalGameTheoryCompletionFrontier =
  game-theory-completion-frontier
    true true true true true true true true
    true
    false false false false false
