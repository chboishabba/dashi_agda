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
import DASHI.GameTheory.CooperativeCoalitionBargainingCoreExact as Cooperative
import DASHI.GameTheory.MechanismDesignIncentiveCompatibilityExact as Mechanism
import DASHI.GameTheory.StrategicExperimentalIdentificationFibreExact as Identification
import DASHI.GameTheory.GameTheorySourceAtlasExact as Sources

------------------------------------------------------------------------
-- GAME THEORY COMPLETION FRONTIER
--
-- Definitions/carriers are not existence theorems.  We now own bounded pure,
-- finite mixed, finite common-prior Bayesian, sequential/extensive, invasion,
-- classic symmetric ESS-shape, finite replicator, cooperative/core/bargaining,
-- mechanism-design, experimental-identification, agentic/evolutionary, memory,
-- FRACTRAN and Wolfram-residual bridges.  Existence, characterization,
-- posterior hierarchies and empirical application receipts remain separate.
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
  cooperativeCoreExistenceOrNonemptiness
  bargainingSolutionCharacterization
  mechanismDesignNamedTruthfulnessTheorems
  empiricalStrategicApplicationReceipt : GameTheoryResidual

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

cooperativeBoundary : Cooperative.CooperativeBargainingBoundary
cooperativeBoundary = Cooperative.canonicalCooperativeBargainingBoundary

mechanismBoundary : Mechanism.MechanismDesignBoundary
mechanismBoundary = Mechanism.canonicalMechanismDesignBoundary

identificationBoundary : Identification.StrategicExperimentalIdentificationBoundary
identificationBoundary = Identification.canonicalStrategicExperimentalIdentificationBoundary

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

data CooperativeCarrierMeansCoreNonemptyPermission : Set where

data BargainingCarrierMeansCharacterizationTheoremPermission : Set where

data DSICCarrierMeansNamedMechanismTheoremPermission : Set where

data IdentifiedQueryMeansAllStrategicCoordinatesPermission : Set where

data RepeatedLearningMeansFolkTheoremPermission : Set where

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

cooperativeCarrierDoesNotProveCoreNonempty :
  CooperativeCarrierMeansCoreNonemptyPermission → ⊥
cooperativeCarrierDoesNotProveCoreNonempty ()

bargainingCarrierDoesNotProveCharacterization :
  BargainingCarrierMeansCharacterizationTheoremPermission → ⊥
bargainingCarrierDoesNotProveCharacterization ()

DSICCarrierDoesNotProveNamedMechanismTheorem :
  DSICCarrierMeansNamedMechanismTheoremPermission → ⊥
DSICCarrierDoesNotProveNamedMechanismTheorem ()

oneIdentifiedQueryDoesNotIdentifyEverything :
  IdentifiedQueryMeansAllStrategicCoordinatesPermission → ⊥
oneIdentifiedQueryDoesNotIdentifyEverything ()

repeatedLearningDoesNotManufactureFolkTheorem :
  RepeatedLearningMeansFolkTheoremPermission → ⊥
repeatedLearningDoesNotManufactureFolkTheorem ()

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
    coalitionalCooperativeCarrierClosed : Bool
    bargainingCarrierClosed : Bool
    mechanismDesignDSICCarrierClosed : Bool
    strategicExperimentalIdentificationClosed : Bool

    finiteMixedNashExistenceNeedsSourceTranscription : Bool
    finiteBayesianNashExistenceNeedsSourceTranscription : Bool

    posteriorConditioningClosed : Bool
    generalTypeHierarchyClosed : Bool
    subgamePerfectExistenceClosed : Bool
    perfectRecallBehaviouralEquivalenceClosed : Bool
    generalReplicatorODEClosed : Bool
    historicalFixationProved : Bool
    cooperativeCoreNonemptyProved : Bool
    bargainingCharacterizationProved : Bool
    namedMechanismTruthfulnessTheoremProved : Bool
    empiricalStrategicApplicationReceipted : Bool

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
    true true true true
    true true
    false false false false false false false false false false
