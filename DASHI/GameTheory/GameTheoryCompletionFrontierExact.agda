module DASHI.GameTheory.GameTheoryCompletionFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Core.ProofDebtRouterExact as Debt
import DASHI.GameTheory.StrategicInteractionCoreExact as Core
import DASHI.GameTheory.FiniteMixedStrategyExpectedUtilityExact as Mixed
import DASHI.GameTheory.FiniteMixedNashProductCorrectionExact as Correction
import DASHI.GameTheory.FiniteMixedNashReceiptBindingExact as Binding
import DASHI.GameTheory.Nash1950CorrectedExistenceAlignmentExact as Nash1950
import DASHI.GameTheory.FiniteIncompleteInformationBayesianExact as Bayesian
import DASHI.GameTheory.FiniteBayesianAgentNormalFormReductionExact as BayesianReduction
import DASHI.GameTheory.FiniteMixedBayesianExistenceViaNashExact as BayesianViaNash
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
-- The corrected mixed-Nash consumer is now source-aligned to Nash 1950 for an
-- exact finite normal-form receipt, so its remaining theorem debt is
-- certification, not transcription.  Finite MIXED Bayesian existence is reduced
-- to that same theorem through the contingent-plan agent normal form; it does
-- not require a second fixed-point theorem.  Pure Bayesian equilibrium,
-- posterior semantics, existence/characterization results in other lanes and
-- empirical applications remain separate.
------------------------------------------------------------------------

data SharedExistenceTheoremLeaf : Set where
  correctedFiniteMixedNash
  finiteMixedBayesianViaNash : SharedExistenceTheoremLeaf

sharedExistenceRoute :
  SharedExistenceTheoremLeaf → Debt.ProofDebtRoutingReceipt
sharedExistenceRoute _ = Nash1950.nash1950PostAlignmentRoute

correctedMixedNashIsCertificationDebt :
  Debt.routedDebt (sharedExistenceRoute correctedFiniteMixedNash)
  ≡ Debt.certificationDebt
correctedMixedNashIsCertificationDebt = refl

finiteMixedBayesianSharesNashCertificationDebt :
  Debt.routedDebt (sharedExistenceRoute finiteMixedBayesianViaNash)
  ≡ Debt.certificationDebt
finiteMixedBayesianSharesNashCertificationDebt = refl

sharedExistenceSchedulerAction :
  (leaf : SharedExistenceTheoremLeaf) →
  Debt.scheduleAction
    (Debt.routedDebt (sharedExistenceRoute leaf))
    (Debt.statementStatus (sharedExistenceRoute leaf))
    Debt.constrained32GB
    Debt.heavyReplay
  ≡ Debt.sendAristotleLean
sharedExistenceSchedulerAction leaf = refl

------------------------------------------------------------------------
-- Distinct residual coordinates.
------------------------------------------------------------------------

data GameTheoryResidual : Set where
  correctedFiniteMixedNashCertification
  pureFiniteBayesianEquilibriumExistenceIfRequired
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

mixedCorrectionBoundary : Correction.FiniteMixedNashCorrectionBoundary
mixedCorrectionBoundary = Correction.canonicalFiniteMixedNashCorrectionBoundary

mixedReceiptBindingBoundary : Binding.FiniteMixedNashReceiptBindingBoundary
mixedReceiptBindingBoundary = Binding.canonicalFiniteMixedNashReceiptBindingBoundary

bayesianBoundary : Bayesian.FiniteBayesianGameBoundary
bayesianBoundary = Bayesian.canonicalFiniteBayesianGameBoundary

bayesianNormalFormBoundary : BayesianReduction.FiniteBayesianNormalFormBoundary
bayesianNormalFormBoundary = BayesianReduction.canonicalFiniteBayesianNormalFormBoundary

bayesianViaNashBoundary : BayesianViaNash.FiniteMixedBayesianViaNashBoundary
bayesianViaNashBoundary = BayesianViaNash.canonicalFiniteMixedBayesianViaNashBoundary

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

data SourceAlignmentMeansCertifiedNashPermission : Set where

data MixedBayesianReductionMeansPureBayesianPermission : Set where

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

sourceAlignmentDoesNotCertifyMixedNash :
  SourceAlignmentMeansCertifiedNashPermission → ⊥
sourceAlignmentDoesNotCertifyMixedNash ()

mixedBayesianReductionDoesNotBecomePureBayesian :
  MixedBayesianReductionMeansPureBayesianPermission → ⊥
mixedBayesianReductionDoesNotBecomePureBayesian ()

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
    correctedIndependentProductMixedNashClosed : Bool
    exactFiniteReceiptBindingClosed : Bool
    nash1950StatementSourceAligned : Bool
    nash1950KernelCertified : Bool

    finiteBayesianCommonPriorClosed : Bool
    pureFiniteBayesianNashDefinitionClosed : Bool
    finiteBayesianAgentNormalFormReductionClosed : Bool
    finiteMixedBayesianExistenceReducedToNash : Bool
    pureBayesianExistenceProved : Bool

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
    true true true true true
    true true true false
    true true true true false
    true true true true
    true true true true true true
    true true true true
    false false false false false false false false false false
