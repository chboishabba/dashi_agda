module DASHI.Cognition.PNF.GrokkingSparseActiveColouringRoutingExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (_+_)
open import Data.Nat using (_∸_)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
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
-- Intervention discipline for empirical relation edges.
------------------------------------------------------------------------

activationCorrelationAlonePaysConflict : Bool
activationCorrelationAlonePaysConflict = false
jointInterventionRequiredForConflict : Bool
jointInterventionRequiredForConflict = true
record CircuitPairInterventionReceipt : Set where
  constructor circuitPairInterventionReceipt
  field activationCorrelationMeasured : Bool; leftInterventionMeasured : Bool; rightInterventionMeasured : Bool; jointInterventionMeasured : Bool; sameCheckpoint : Bool; sameHeldOutEvaluation : Bool; proposedRelation : GrokkingReducerRelation; relationPromotionPaid : Bool
open CircuitPairInterventionReceipt public
unpaidCircuitPairIntervention : CircuitPairInterventionReceipt
unpaidCircuitPairIntervention = circuitPairInterventionReceipt false false false false false false independent false
syntheticPaidConflictIntervention : CircuitPairInterventionReceipt
syntheticPaidConflictIntervention = circuitPairInterventionReceipt true true true true true true conflict true
syntheticConflictIsEmpiricalGrokkingResult : Bool
syntheticConflictIsEmpiricalGrokkingResult = false

------------------------------------------------------------------------
-- Threshold-governed pair classifier.
------------------------------------------------------------------------

record PairInterventionScore : Set where
  constructor pairInterventionScore
  field leftEffect : Nat; rightEffect : Nat; jointEffect : Nat; interactionThreshold : Nat; adequatelyPowered : Bool; leftRequiresRight : Bool; rightRequiresLeft : Bool
open PairInterventionScore public
interactionExcess : PairInterventionScore → Nat
interactionExcess score = jointEffect score ∸ (leftEffect score + rightEffect score)
interactionDeficit : PairInterventionScore → Nat
interactionDeficit score = (leftEffect score + rightEffect score) ∸ jointEffect score
natLE : Nat → Nat → Bool
natLE zero _ = true
natLE (suc _) zero = false
natLE (suc left) (suc right) = natLE left right
aboveInteractionThreshold : PairInterventionScore → Bool
aboveInteractionThreshold score = natLE (suc (interactionThreshold score)) (interactionExcess score)

data PairRelationClassification : Set where
  underpowered : PairRelationClassification
  classified : GrokkingReducerRelation → PairRelationClassification
classifyPair : PairInterventionScore → PairRelationClassification
classifyPair score with adequatelyPowered score
... | false = underpowered
... | true with leftRequiresRight score | rightRequiresLeft score
...   | true  | _     = classified gluingRequirement
...   | false | true  = classified gluingRequirement
...   | false | false with aboveInteractionThreshold score
...     | true  = classified conflict
...     | false = classified independent

------------------------------------------------------------------------
-- Requirement direction is an evidence coordinate, not the opposite sign of
-- conflict.  The current Mod97 runtime intervenes on parallel post-ReLU units
-- in one hidden layer, so its singleton/joint pair ablations cannot supply a
-- directed hidden-unit requirement edge.  An externally paid directional
-- receipt is a separate admissible source for the generic classifier.
------------------------------------------------------------------------

data RequirementEvidenceSource : Set where
  sameLayerPostReLUPairAblation : RequirementEvidenceSource
  externallyPaidDirectionalRequirement : RequirementEvidenceSource

requirementEvidencePaysDirection : RequirementEvidenceSource → Bool
requirementEvidencePaysDirection sameLayerPostReLUPairAblation = false
requirementEvidencePaysDirection externallyPaidDirectionalRequirement = true

classifyPairWithoutRequirementDirection : PairInterventionScore → PairRelationClassification
classifyPairWithoutRequirementDirection score with adequatelyPowered score
... | false = underpowered
... | true with aboveInteractionThreshold score
...   | true = classified conflict
...   | false = classified independent

classifyPairWithRequirementEvidence :
  RequirementEvidenceSource → PairInterventionScore → PairRelationClassification
classifyPairWithRequirementEvidence source score with requirementEvidencePaysDirection source
... | true = classifyPair score
... | false = classifyPairWithoutRequirementDirection score

------------------------------------------------------------------------
-- Exact query-indexed nonfactorability of requirement direction through the
-- symmetric singleton/joint pair-ablation surface.  The finite collision is a
-- repository-local theorem; the imported query calculus retains its own source
-- attribution boundary and imports neither empirical truth nor authority.
------------------------------------------------------------------------

data RequirementDirectionWorld : Set where
  worldLeftRequiresRight : RequirementDirectionWorld
  worldRightRequiresLeft : RequirementDirectionWorld

record PairAblationObservedEffects : Set where
  constructor pairAblationObservedEffects
  field observedLeftEffect : Nat; observedRightEffect : Nat; observedJointEffect : Nat
open PairAblationObservedEffects public

pairAblationProject : RequirementDirectionWorld → PairAblationObservedEffects
pairAblationProject world = pairAblationObservedEffects 2 2 4

data RequirementDirectionQuery : Set where
  askRequirementDirection : RequirementDirectionQuery

data RequirementDirectionAnswer : Set where
  answerLeftRequiresRight : RequirementDirectionAnswer
  answerRightRequiresLeft : RequirementDirectionAnswer

requirementDirectionAnswer :
  RequirementDirectionQuery → RequirementDirectionWorld → RequirementDirectionAnswer
requirementDirectionAnswer askRequirementDirection worldLeftRequiresRight = answerLeftRequiresRight
requirementDirectionAnswer askRequirementDirection worldRightRequiresLeft = answerRightRequiresLeft

requirementDirectionSemantics :
  Query.QuerySemantics RequirementDirectionWorld RequirementDirectionQuery RequirementDirectionAnswer
requirementDirectionSemantics = Query.querySemantics requirementDirectionAnswer

pairAblationRequirementDirectionDefect :
  Query.QueryAdequacyDefect
    pairAblationProject
    requirementDirectionSemantics
    askRequirementDirection
pairAblationRequirementDirectionDefect =
  Query.queryAdequacyDefect
    worldLeftRequiresRight
    worldRightRequiresLeft
    refl
    (λ ())

pairAblationRequirementDirectionNotAdequate :
  Query.AdequateFor
    pairAblationProject
    requirementDirectionSemantics
    askRequirementDirection → ⊥
pairAblationRequirementDirectionNotAdequate =
  Query.queryAdequacyDefectBlocksFactorisation
    pairAblationRequirementDirectionDefect

pairAblationRequirementDirectionCollisionPaid : Bool
pairAblationRequirementDirectionCollisionPaid = true

requirementDirectionFactorsThroughPairAblation : Bool
requirementDirectionFactorsThroughPairAblation = false

activationCorrelationIsClassificationInput : Bool
activationCorrelationIsClassificationInput = false
syntheticConflictScore : PairInterventionScore
syntheticConflictScore = pairInterventionScore 2 2 7 1 true false false
syntheticRequirementScore : PairInterventionScore
syntheticRequirementScore = pairInterventionScore 2 2 4 1 true true false
syntheticIndependentScore : PairInterventionScore
syntheticIndependentScore = pairInterventionScore 2 3 5 1 true false false
syntheticUnderpoweredScore : PairInterventionScore
syntheticUnderpoweredScore = pairInterventionScore 2 2 7 1 false false false
classifierIsEmpiricalGrokkingResult : Bool
classifierIsEmpiricalGrokkingResult = false

------------------------------------------------------------------------
-- Finite closed-compatible-family beta witness.
------------------------------------------------------------------------

record ClosedCompatibleFamilyCertificate : Set where
  constructor closedCompatibleFamilyCertificate
  field familySize : Nat; conflictFree : Bool; requirementClosed : Bool
open ClosedCompatibleFamilyCertificate public
record FiniteClosedCompatibleSystem : Set where
  constructor finiteClosedCompatibleSystem
  field rawCandidateCount : Nat; conflictEdgeCountFinite : Nat; requirementEdgeCountFinite : Nat; certifiedFamily : ClosedCompatibleFamilyCertificate; certifiedMaximum : Nat; maximalityPaidByFiniteExhaustion : Bool
open FiniteClosedCompatibleSystem public
betaClosedCompatible : FiniteClosedCompatibleSystem → Nat
betaClosedCompatible system = certifiedMaximum system

baseClosedCompatibleSystem : FiniteClosedCompatibleSystem
baseClosedCompatibleSystem = finiteClosedCompatibleSystem 3 1 0 (closedCompatibleFamilyCertificate 2 true true) 2 true
extraBlockedCapacitySystem : FiniteClosedCompatibleSystem
extraBlockedCapacitySystem = finiteClosedCompatibleSystem 4 2 0 (closedCompatibleFamilyCertificate 2 true true) 2 true
conflictRemovedSystem : FiniteClosedCompatibleSystem
conflictRemovedSystem = finiteClosedCompatibleSystem 3 0 0 (closedCompatibleFamilyCertificate 3 true true) 3 true
requirementOpenSystem : FiniteClosedCompatibleSystem
requirementOpenSystem = finiteClosedCompatibleSystem 2 0 1 (closedCompatibleFamilyCertificate 1 true true) 1 true
requirementClosedSystem : FiniteClosedCompatibleSystem
requirementClosedSystem = finiteClosedCompatibleSystem 2 0 1 (closedCompatibleFamilyCertificate 2 true true) 2 true

betaMaximalityIsReceiptGated : Bool
betaMaximalityIsReceiptGated = true
betaWitnessIsUniversalGrokkingObjective : Bool
betaWitnessIsUniversalGrokkingObjective = false

------------------------------------------------------------------------
-- Matched checkpoint transition receipt.
--
-- Beta, held-out generalisation, active support, and training loss remain
-- separate coordinates.  Promotion requires matched checkpoint provenance and
-- paid finite beta maximality receipts on both sides; no delta alone promotes.
------------------------------------------------------------------------

record GrokkingCheckpointObservation : Set where
  constructor grokkingCheckpointObservation
  field
    closedCompatibleSystem : FiniteClosedCompatibleSystem
    activeSupportAtCheckpoint : Nat
    heldOutGeneralisationScore : Nat
    trainingLossMagnitude : Nat
    checkpointMeasured : Bool
open GrokkingCheckpointObservation public

record GrokkingClosedCompatibleTransitionReceipt : Set where
  constructor grokkingClosedCompatibleTransitionReceipt
  field
    beforeCheckpoint : GrokkingCheckpointObservation
    afterCheckpoint : GrokkingCheckpointObservation
    sameModelFamily : Bool
    sameHeldOutSplit : Bool
    sameCircuitExtractionRule : Bool
open GrokkingClosedCompatibleTransitionReceipt public

betaGain : GrokkingClosedCompatibleTransitionReceipt → Nat
betaGain receipt =
  betaClosedCompatible (closedCompatibleSystem (afterCheckpoint receipt)) ∸
  betaClosedCompatible (closedCompatibleSystem (beforeCheckpoint receipt))

heldOutGeneralisationGain : GrokkingClosedCompatibleTransitionReceipt → Nat
heldOutGeneralisationGain receipt =
  heldOutGeneralisationScore (afterCheckpoint receipt) ∸
  heldOutGeneralisationScore (beforeCheckpoint receipt)

activeSupportGain : GrokkingClosedCompatibleTransitionReceipt → Nat
activeSupportGain receipt =
  activeSupportAtCheckpoint (afterCheckpoint receipt) ∸
  activeSupportAtCheckpoint (beforeCheckpoint receipt)

trainingLossDecrease : GrokkingClosedCompatibleTransitionReceipt → Nat
trainingLossDecrease receipt =
  trainingLossMagnitude (beforeCheckpoint receipt) ∸
  trainingLossMagnitude (afterCheckpoint receipt)

transitionPromotionPaid : GrokkingClosedCompatibleTransitionReceipt → Bool
transitionPromotionPaid receipt with sameModelFamily receipt
... | false = false
... | true with sameHeldOutSplit receipt
...   | false = false
...   | true with sameCircuitExtractionRule receipt
...     | false = false
...     | true with checkpointMeasured (beforeCheckpoint receipt)
...       | false = false
...       | true with checkpointMeasured (afterCheckpoint receipt)
...         | false = false
...         | true with maximalityPaidByFiniteExhaustion (closedCompatibleSystem (beforeCheckpoint receipt))
...           | false = false
...           | true with maximalityPaidByFiniteExhaustion (closedCompatibleSystem (afterCheckpoint receipt))
...             | false = false
...             | true = true

syntheticBeforeCheckpoint : GrokkingCheckpointObservation
syntheticBeforeCheckpoint =
  grokkingCheckpointObservation baseClosedCompatibleSystem 2 5 1 true

syntheticAfterCheckpoint : GrokkingCheckpointObservation
syntheticAfterCheckpoint =
  grokkingCheckpointObservation conflictRemovedSystem 3 8 1 true

syntheticClosedCompatibleTransition : GrokkingClosedCompatibleTransitionReceipt
syntheticClosedCompatibleTransition =
  grokkingClosedCompatibleTransitionReceipt
    syntheticBeforeCheckpoint
    syntheticAfterCheckpoint
    true true true

unmatchedClosedCompatibleTransition : GrokkingClosedCompatibleTransitionReceipt
unmatchedClosedCompatibleTransition =
  grokkingClosedCompatibleTransitionReceipt
    syntheticBeforeCheckpoint
    syntheticAfterCheckpoint
    false true true

unpaidBetaSystem : FiniteClosedCompatibleSystem
unpaidBetaSystem =
  finiteClosedCompatibleSystem 3 1 0
    (closedCompatibleFamilyCertificate 2 true true)
    2 false

unpaidBetaBeforeCheckpoint : GrokkingCheckpointObservation
unpaidBetaBeforeCheckpoint =
  grokkingCheckpointObservation unpaidBetaSystem 2 5 1 true

unpaidBetaClosedCompatibleTransition : GrokkingClosedCompatibleTransitionReceipt
unpaidBetaClosedCompatibleTransition =
  grokkingClosedCompatibleTransitionReceipt
    unpaidBetaBeforeCheckpoint
    syntheticAfterCheckpoint
    true true true

syntheticTransitionIsEmpiricalGrokkingResult : Bool
syntheticTransitionIsEmpiricalGrokkingResult = false

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
