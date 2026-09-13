module DASHI.Cognition.PNF.GrokkingSparseActiveColouringRoutingExact where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Cognition.PNF.GrokkingInvariantSubspaceSelectionExact as GrokSelect
import DASHI.Cognition.PNF.GrokkingMeasureStrataExact as GrokMeasure
import DASHI.Combinatorics.GraphColouringRecolourPantsSnowballExact as Colouring
import DASHI.ComputerScience.RSA260FractalPadicHyperfabricBatchGluingExact as CanonicalReducer

record SparseSupportWitness : Set where
  constructor sparseSupportWitness
  field availableCapacity : Nat; activeSupport : Nat
open SparseSupportWitness public
structuredSparseWitness : SparseSupportWitness
structuredSparseWitness = sparseSupportWitness 2 1
structuredSparseUsesStrictSubset : activeSupport structuredSparseWitness < availableCapacity structuredSparseWitness
structuredSparseUsesStrictSubset = s≤s (s≤s z≤n)

record ConditionalUnitUse : Set where
  constructor conditionalUnitUse
  field inactiveForCurrentInput : Bool; usefulOnAnotherInput : Bool
open ConditionalUnitUse public
conditionallyUsefulUnit : ConditionalUnitUse
conditionallyUsefulUnit = conditionalUnitUse true true
conditionalUseWitness : inactiveForCurrentInput conditionallyUsefulUnit ≡ true × usefulOnAnotherInput conditionallyUsefulUnit ≡ true
conditionalUseWitness = refl , refl
inactiveNowDoesNotProveGlobalRedundancy : Bool
inactiveNowDoesNotProveGlobalRedundancy = true

data Route : Set where memorizerRoute characterRoute : Route
routeCandidate : Route → GrokSelect.RepresentationCandidate
routeCandidate memorizerRoute = GrokSelect.memorizer
routeCandidate characterRoute = GrokSelect.characterRule
trainingFitSame : Route → Route → Bool
trainingFitSame _ _ = true
structuralDefect : Route → Nat
structuralDefect route = GrokSelect.invarianceDefect (routeCandidate route)
fitEqualButStructuralRouteImproves : trainingFitSame memorizerRoute characterRoute ≡ true × structuralDefect characterRoute < structuralDefect memorizerRoute
fitEqualButStructuralRouteImproves = refl , GrokSelect.characterStrictlyImprovesInvariantGeometry
trainingTaskMechanismMassRemainDistinct : Bool
trainingTaskMechanismMassRemainDistinct = true

------------------------------------------------------------------------
-- Source-scoped sparse-activation and grokking coordinates.
------------------------------------------------------------------------

moneSource : Source.AttributedSource
moneSource = Source.mkDOISource "Runxi Cheng; Yuchen Guan; Yucheng Ding; Qingguo Hu; Yongxian Wei; Chun Yuan; Yelong Shen; Weizhu Chen; Yeyun Gong" "Mixture of Neuron Experts" "arXiv:2510.05781" "2025" "10.48550/arXiv.2510.05781" "https://arxiv.org/abs/2510.05781" Source.academicArticleSource "source for neuron-granular MoE activation sparsity and the reported 50-percent activated-parameter MoNE comparison; not a universal neuron-usage theorem" Source.publicAttribution

salahYevickSource : Source.AttributedSource
salahYevickSource = Source.mkDOISource "Ahmed Salah; David Yevick" "Tracing the Path to Grokking: Dropout, Embeddings, and Network Activation" "Neural Processing Letters 58, article 36" "2026" "10.1007/s11063-026-11843-4" "https://doi.org/10.1007/s11063-026-11843-4" Source.academicArticleSource "source for grokking diagnostics including neuron activity; reports decreasing inactive-neuron percentage during generalisation in the studied models" Source.publicAttribution

humayunCircuitSource : Source.AttributedSource
humayunCircuitSource = Source.mkNoDOISource "Ahmed Imtiaz Humayun; Randall Balestriero; Richard G. Baraniuk" "Grokking and the Geometry of Circuit Formation" "ICML 2024 Workshop on Mechanistic Interpretability" "2024" "https://research.google/pubs/grokking-and-the-geometry-of-circuit-formation/" Source.academicArticleSource "source for circuit-geometry and circuit-density changes during grokking; not identified with neuron activation sparsity" Source.publicAttribution

record MoNEActivationObservation : Set where
  constructor moneActivation
  field activationSource : Source.AttributedSource; reportedMoNEActivatedPercent : Nat; nearZeroNeuronActivationsReported : Bool; universalLLMNeuronUsageClaim : Bool; sourceImportsProof : Bool
open MoNEActivationObservation public

moneActivationObservation : MoNEActivationObservation
moneActivationObservation = moneActivation moneSource 50 true false false

data SparseRoutingMetric : Set where inactiveNeuronFraction activeSupportSize uniqueCircuitDensity conflictEdgeCount compatibleBatchSize : SparseRoutingMetric

data Trend : Set where increases decreases stable unmeasured : Trend

record EmpiricalMetricObservation : Set where
  constructor empiricalMetricObservation
  field observationSource : Source.AttributedSource; metric : SparseRoutingMetric; trend : Trend; universalAcrossArchitectures : Bool; importsMechanisticProof : Bool
open EmpiricalMetricObservation public

salahNeuronActivityObservation : EmpiricalMetricObservation
salahNeuronActivityObservation = empiricalMetricObservation salahYevickSource inactiveNeuronFraction decreases false false

humayunCircuitDensityObservation : EmpiricalMetricObservation
humayunCircuitDensityObservation = empiricalMetricObservation humayunCircuitSource uniqueCircuitDensity decreases false false

inactiveNeuronFractionIsUniqueCircuitDensity : Bool
inactiveNeuronFractionIsUniqueCircuitDensity = false

grokkingActiveSupportShrinkPaid : Bool
grokkingActiveSupportShrinkPaid = false

empiricalConflictGraphChromaticObjectivePaid : Bool
empiricalConflictGraphChromaticObjectivePaid = false

record GrokkingRoutingTransitionReceipt : Set where
  constructor grokkingRoutingTransitionReceipt
  field activeSupportMeasured : Bool; circuitFamilyMeasured : Bool; conflictEdgesMeasured : Bool; sameCheckpointFamily : Bool; sameActivationThreshold : Bool; heldOutGeneralisationMeasured : Bool
open GrokkingRoutingTransitionReceipt public

unpaidGrokkingRoutingTransition : GrokkingRoutingTransitionReceipt
unpaidGrokkingRoutingTransition = grokkingRoutingTransitionReceipt false false false false false false

------------------------------------------------------------------------
-- Canonical conflict / requirement / independence carrier.
--
-- Reuse the existing RSA/NDim relation rather than introducing another graph
-- ontology.  Grokking-specific semantics remain downstream measurements.
------------------------------------------------------------------------

GrokkingReducerRelation : Set
GrokkingReducerRelation = CanonicalReducer.ReducerRelation

conflict : GrokkingReducerRelation
conflict = CanonicalReducer.conflict

gluingRequirement : GrokkingReducerRelation
gluingRequirement = CanonicalReducer.gluingRequirement

independent : GrokkingReducerRelation
independent = CanonicalReducer.independent

canonicalConflict : CanonicalReducer.ReducerRelation
canonicalConflict = CanonicalReducer.conflict

canonicalRequirement : CanonicalReducer.ReducerRelation
canonicalRequirement = CanonicalReducer.gluingRequirement

canonicalIndependent : CanonicalReducer.ReducerRelation
canonicalIndependent = CanonicalReducer.independent

fromCanonicalReducerRelation : CanonicalReducer.ReducerRelation → GrokkingReducerRelation
fromCanonicalReducerRelation relation = relation

conflictFreeImpliesRequirementClosed : Bool
conflictFreeImpliesRequirementClosed = false

record ConflictCarrierIntegrationResidual : Set where
  constructor conflictCarrierIntegrationResidual
  field localDuplicateConflictOntologyAdded : Bool; canonicalReducerRelationAdapterPaid : Bool; rebaseNeededBeforeCanonicalImport : Bool
open ConflictCarrierIntegrationResidual public

currentConflictCarrierIntegrationResidual : ConflictCarrierIntegrationResidual
currentConflictCarrierIntegrationResidual = conflictCarrierIntegrationResidual false true false

------------------------------------------------------------------------
-- Colouring cross-pollination remains structural, not objective identity.
------------------------------------------------------------------------

colouringSourceClaim : Colouring.AttributedClaim
colouringSourceClaim = Colouring.fourColourLinearReductionClaim

colouringConflictFreeBatchWitness : Bool
colouringConflictFreeBatchWitness = true

grokkingLiterallyMinimisesChromaticNumber : Bool
grokkingLiterallyMinimisesChromaticNumber = false

colouringAnalogyBoundary : colouringConflictFreeBatchWitness ≡ true × grokkingLiterallyMinimisesChromaticNumber ≡ false
colouringAnalogyBoundary = refl , refl

record CandidateActionRoutingWitness : Set where
  constructor candidateActionRoutingWitness
  field largeCandidateFamily : Bool; sparseCompatibleAction : Bool; globalCorrectnessStillNeedsLiftOrConsumer : Bool
open CandidateActionRoutingWitness public

colouringRoutingWitness : CandidateActionRoutingWitness
colouringRoutingWitness = candidateActionRoutingWitness true true true

colouringCandidateActionWitness : largeCandidateFamily colouringRoutingWitness ≡ true × sparseCompatibleAction colouringRoutingWitness ≡ true
colouringCandidateActionWitness = refl , refl

record SparseActiveGrokkingBoundary : Set where
  constructor sparseActiveGrokkingBoundary
  field availableCapacityIsActiveCapacity : Bool; inactiveForOneInputImpliesGloballyRedundant : Bool; interpolationImpliesGeneralisation : Bool; grokkingIsOrdinaryLossReduction : Bool; sparseActivationImpliesPrunableEverywhere : Bool; graphColouringCompatibilityIsMoERoutingIdentity : Bool; graphChromaticNumberIsGrokkingObjective : Bool; neuronActivationSparsityIsCircuitDensity : Bool; sourceScopedMoNEHalfActivationIsUniversalLLMLaw : Bool; largeCandidateFamilyCanPermitSparseCompatibleAction : Bool; overcompleteCarrierMaySupportConditionalReuse : Bool
open SparseActiveGrokkingBoundary public

canonicalSparseActiveGrokkingBoundary : SparseActiveGrokkingBoundary
canonicalSparseActiveGrokkingBoundary = sparseActiveGrokkingBoundary false false false false false false false false false true true
