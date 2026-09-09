module DASHI.GameTheory.GameTheoryCompletionFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Core.ProofDebtRouterExact as Debt
import DASHI.GameTheory.StrategicInteractionCoreExact as Core
import DASHI.GameTheory.FiniteMixedStrategyExpectedUtilityExact as Mixed
import DASHI.GameTheory.FiniteIncompleteInformationBayesianExact as Bayesian
import DASHI.GameTheory.SequentialExtensiveFormExact as Sequential
import DASHI.GameTheory.SequentialGameFractranWolframCrossPollinationExact as Computation
import DASHI.GameTheory.AgenticStrategicInteractionBridgeExact as AgenticBridge
import DASHI.GameTheory.EvolutionaryStrategicSelectionBridgeExact as EvolutionBridge
import DASHI.GameTheory.EvolutionaryInvasionStabilityExact as Invasion
import DASHI.GameTheory.SymmetricEvolutionaryStableStrategyExact as ESS
import DASHI.GameTheory.FiniteTwoStrategyReplicatorExact as Replicator
import DASHI.GameTheory.RepeatedStrategicLearningMemoryBridgeExact as Repeated
import DASHI.GameTheory.GameTheorySourceAtlasExact as Sources

------------------------------------------------------------------------
-- GAME THEORY COMPLETION FRONTIER
--
-- Definitions/carriers are not existence theorems.  We now own bounded pure,
-- finite mixed, finite common-prior Bayesian, sequential/extensive, invasion,
-- classic symmetric ESS-shape, finite replicator, agentic/evolutionary, memory,
-- FRACTRAN and Wolfram-residual bridges.  Existence, posterior hierarchies,
-- cooperative/mechanism theory and empirical identification remain separately
-- receipted.
------------------------------------------------------------------------

data StandardGameTheoremFamily : Set where
  finiteMixedNashExistence
  finiteBayesianNashExistence : StandardGameTheoremFamily

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

finiteBayesianNashExistenceNeedsTranscription :
  Debt.routedDebt (standardGameTheoremRoute finiteBayesianNashExistence)
  ≡ Debt.transcriptionDebt
finiteBayesianNashExistenceNeedsTranscription = refl

standardGameTheoremSchedulerAction :
  (family : StandardGameTheoremFamily) →
  Debt.scheduleAction
    (Debt.routedDebt (standardGameTheoremRoute family))
    (Debt.statementStatus (standardGameTheoremRoute family))
    Debt.constrained32GB
    Debt.heavyReplay
  ≡ Debt.auditTranscription
standardGameTheoremSchedulerAction family = refl

------------------------------------------------------------------------
-- Distinct residual coordinates.
------------------------------------------------------------------------

data GameTheoryResidual : Set where
  finiteMixedNashExistenceTheorem
  finiteBayesianNashExistenceTheorem
  posteriorConditioningAndBayesUpdate
  generalTypeHierarchyAndCommonKnowledge
  subgamePerfectExistenceTheorem
  perfectRecallBehaviouralEquivalence
  generalReplicatorODEAndStability
  empiricalEvolutionaryFixation
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

bayesianBoundary : Bayesian.FiniteBayesianGameBoundary
bayesianBoundary = Bayesian.canonicalFiniteBayesianGameBoundary

sequentialBoundary : Sequential.SequentialExtensiveFormBoundary
sequentialBoundary = Sequential.canonicalSequentialExtensiveFormBoundary

computationBoundary : Computation.SequentialGameComputationBoundary
computationBoundary = Computation.canonicalSequentialGameComputationBoundary

agenticBoundary : AgenticBridge.AgenticStrategicBoundary
agenticBoundary = AgenticBridge.canonicalAgenticStrategicBoundary

evolutionaryBoundary : EvolutionBridge.EvolutionaryStrategicBoundary
evolutionaryBoundary = EvolutionBridge.canonicalEvolutionaryStrategicBoundary

invasionBoundary : Invasion.EvolutionaryInvasionBoundary
invasionBoundary = Invasion.canonicalEvolutionaryInvasionBoundary

essBoundary : ESS.SymmetricESSBoundary
essBoundary = ESS.canonicalSymmetricESSBoundary

replicatorBoundary : Replicator.FiniteReplicatorBoundary
replicatorBoundary = Replicator.canonicalFiniteReplicatorBoundary

repeatedLearningBoundary : Repeated.RepeatedStrategicLearningBoundary
repeatedLearningBoundary = Repeated.canonicalRepeatedStrategicLearningBoundary

sourceAtlasCount : Sources.canonicalGameTheorySourceCount ≡ 8
sourceAtlasCount = Sources.canonicalGameTheorySourceCountIsEight

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data MixedNashCarrierMeansExistenceTheoremPermission : Set where

data BayesianCarrierMeansPosteriorTheoremPermission : Set where

data NashMeansSubgamePerfectPermission : Set where

data SubgamePerfectCarrierMeansExistencePermission : Set where

data NashMeansESSPermission : Set where

data ESSMeansFixationPermission : Set where

data ReplicatorStepMeansConvergencePermission : Set where

data NashMeansCoalitionalStabilityPermission : Set where

data RepeatedLearningMeansFolkTheoremPermission : Set where

data UtilityMeansMechanismTruthfulnessPermission : Set where

data FractranTraceMeansStrategicEquilibriumPermission : Set where

data WolframCausalInvarianceMeansStrategicEquilibriumPermission : Set where

mixedNashCarrierDoesNotProveExistence :
  MixedNashCarrierMeansExistenceTheoremPermission → ⊥
mixedNashCarrierDoesNotProveExistence ()

bayesianCarrierDoesNotInventPosteriorTheorem :
  BayesianCarrierMeansPosteriorTheoremPermission → ⊥
bayesianCarrierDoesNotInventPosteriorTheorem ()

nashDoesNotBecomeSubgamePerfect : NashMeansSubgamePerfectPermission → ⊥
nashDoesNotBecomeSubgamePerfect ()

subgamePerfectCarrierDoesNotProveExistence :
  SubgamePerfectCarrierMeansExistencePermission → ⊥
subgamePerfectCarrierDoesNotProveExistence ()

nashDoesNotBecomeESS : NashMeansESSPermission → ⊥
nashDoesNotBecomeESS ()

essDoesNotBecomeHistoricalFixation : ESSMeansFixationPermission → ⊥
essDoesNotBecomeHistoricalFixation ()

replicatorStepDoesNotProveConvergence : ReplicatorStepMeansConvergencePermission → ⊥
replicatorStepDoesNotProveConvergence ()

nashDoesNotBecomeCoalitionalStability :
  NashMeansCoalitionalStabilityPermission → ⊥
nashDoesNotBecomeCoalitionalStability ()

repeatedLearningDoesNotManufactureFolkTheorem :
  RepeatedLearningMeansFolkTheoremPermission → ⊥
repeatedLearningDoesNotManufactureFolkTheorem ()

utilityDoesNotManufactureTruthfulMechanism :
  UtilityMeansMechanismTruthfulnessPermission → ⊥
utilityDoesNotManufactureTruthfulMechanism ()

fractranExecutionDoesNotCreateEquilibrium :
  FractranTraceMeansStrategicEquilibriumPermission → ⊥
fractranExecutionDoesNotCreateEquilibrium ()

wolframCausalInvarianceDoesNotCreateEquilibrium :
  WolframCausalInvarianceMeansStrategicEquilibriumPermission → ⊥
wolframCausalInvarianceDoesNotCreateEquilibrium ()

record GameTheoryCompletionFrontier : Set where
  constructor game-theory-completion-frontier
  field
    sourceAtlasClosed : Bool
    pureStrategicCoreClosed : Bool
    pureNashDefinitionClosed : Bool
    dominanceAndParetoClosed : Bool
    finiteMixedExpectedUtilityClosed : Bool
    finiteMixedNashDefinitionClosed : Bool
    finiteBayesianCommonPriorClosed : Bool
    finiteBayesianNashDefinitionClosed : Bool
    sequentialExtensiveFormClosed : Bool
    subgamePerfectDefinitionClosed : Bool
    fractranSequentialRepresentationBridgeClosed : Bool
    wolframPathResidualStrategicBridgeClosed : Bool
    agenticStrategicBridgeClosed : Bool
    evolutionarySelectionBridgeClosed : Bool
    invasionStabilityClosed : Bool
    classicSymmetricESSCriterionClosed : Bool
    finiteReplicatorReweightingClosed : Bool
    repeatedLearningMemoryBridgeClosed : Bool

    finiteMixedNashExistenceNeedsSourceTranscription : Bool
    finiteBayesianNashExistenceNeedsSourceTranscription : Bool

    posteriorConditioningClosed : Bool
    generalTypeHierarchyClosed : Bool
    subgamePerfectExistenceClosed : Bool
    perfectRecallBehaviouralEquivalenceClosed : Bool
    generalReplicatorODEClosed : Bool
    historicalFixationProved : Bool
    coalitionalCooperativeClosed : Bool
    bargainingAllocationClosed : Bool
    mechanismDesignClosed : Bool
    empiricalStrategicIdentificationClosed : Bool

canonicalGameTheoryCompletionFrontier : GameTheoryCompletionFrontier
canonicalGameTheoryCompletionFrontier =
  game-theory-completion-frontier
    true
    true true true true true
    true true
    true true
    true true
    true true
    true true true
    true
    true true
    false false false false false false false false false false
