module DASHI.Analysis.RiemannAristotleRHBidiSearchSchedulerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotleExperimentalProofSearchExact as Search
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as HOff

------------------------------------------------------------------------
-- RH-ONLY BIDI-AWARE SEARCH SCHEDULER
--
-- Consumer first, recursively.  A candidate experiment is schedulable only if
-- it feeds an open producer node on the backward RH cut.
--
-- The checked cutoff theorem is generic in taper g, so instantiating it at the
-- final high-ordinate pole taper is not a separate analytic research theorem.
-- The infinite far shell is already controlled.  Therefore H_off^pole now has
-- one genuine analytic producer node:
--
--   finite signed target-centred nearOffFinset evaluation.
--
-- Together with the consumer-insufficient Gamma result, the active queue is:
--
--   (1) evaluate the finite signed near zero sum;
--   (2) repair H_Gamma to consumer-sufficient O(|t|^-2)-scale accuracy.
------------------------------------------------------------------------

data ProducerNeed : Set where
  unpaidProducer
  consumerInsufficientProducer
  producerClosed
  routeRefuted
  : ProducerNeed

currentNeed : Search.RHResearchSocket → ProducerNeed
currentNeed Search.offOrdinateSocket = unpaidProducer
currentNeed Search.gammaSocket = consumerInsufficientProducer
currentNeed Search.clusterMarginSocket = producerClosed

------------------------------------------------------------------------
-- Recursive producer nodes beneath the coarse RH sockets.
------------------------------------------------------------------------

data RHProducerNode : Set where
  offFiniteNearEvaluationNode
  gammaPrecisionNode
  : RHProducerNode

nodeFeedsSocket : RHProducerNode → Search.RHResearchSocket
nodeFeedsSocket offFiniteNearEvaluationNode = Search.offOrdinateSocket
nodeFeedsSocket gammaPrecisionNode = Search.gammaSocket

------------------------------------------------------------------------
-- Candidate experiment classes for the exact current cut.
------------------------------------------------------------------------

data RHBidiExperiment : Set where
  evaluateFiniteNearSignedSum
  improveGammaEvaluation
  repeatClusterMarginProof
  reproveGenericCutoffInstantiation
  reproveInfiniteFarShell
  sharpenBalanceBudgetRoute
  auditNamedExternalDonor
  : RHBidiExperiment

data RHExperimentOutputKind : Set where
  directFiniteProducer
  consumerSufficientRepair
  redundantClosedProducer
  redundantGenericInstantiation
  redundantOwnedFarTail
  balanceDerived
  donorAuditOnly
  : RHExperimentOutputKind

outputKind : RHBidiExperiment → RHExperimentOutputKind
outputKind evaluateFiniteNearSignedSum = directFiniteProducer
outputKind improveGammaEvaluation = consumerSufficientRepair
outputKind repeatClusterMarginProof = redundantClosedProducer
outputKind reproveGenericCutoffInstantiation = redundantGenericInstantiation
outputKind reproveInfiniteFarShell = redundantOwnedFarTail
outputKind sharpenBalanceBudgetRoute = balanceDerived
outputKind auditNamedExternalDonor = donorAuditOnly

------------------------------------------------------------------------
-- Consumer-first admissibility.
------------------------------------------------------------------------

data InhabitsLiveRHProducer : RHBidiExperiment → Set where
  finiteNearEvaluationIsLive :
    InhabitsLiveRHProducer evaluateFiniteNearSignedSum
  gammaPrecisionRepairIsLive :
    InhabitsLiveRHProducer improveGammaEvaluation

record RHBidiSchedulable (experiment : RHBidiExperiment) : Set where
  constructor rh-bidi-schedulable
  field
    inhabitsLiveProducer : InhabitsLiveRHProducer experiment
    rhConsumerReference : String
    producerInterfaceReference : String

open RHBidiSchedulable public

------------------------------------------------------------------------
-- Exact pruning theorems.
------------------------------------------------------------------------

clusterMarginRepeatNotSchedulable :
  RHBidiSchedulable repeatClusterMarginProof → ⊥
clusterMarginRepeatNotSchedulable s with inhabitsLiveProducer s
... | ()

genericCutoffInstantiationRepeatNotSchedulable :
  RHBidiSchedulable reproveGenericCutoffInstantiation → ⊥
genericCutoffInstantiationRepeatNotSchedulable s with inhabitsLiveProducer s
... | ()

farShellRepeatNotSchedulable :
  RHBidiSchedulable reproveInfiniteFarShell → ⊥
farShellRepeatNotSchedulable s with inhabitsLiveProducer s
... | ()

balanceRouteNotSchedulable :
  RHBidiSchedulable sharpenBalanceBudgetRoute → ⊥
balanceRouteNotSchedulable s with inhabitsLiveProducer s
... | ()

nameOnlyDonorNotSchedulable :
  RHBidiSchedulable auditNamedExternalDonor → ⊥
nameOnlyDonorNotSchedulable s with inhabitsLiveProducer s
... | ()

finiteNearEvaluationSchedulable :
  RHBidiSchedulable evaluateFiniteNearSignedSum
finiteNearEvaluationSchedulable =
  rh-bidi-schedulable
    finiteNearEvaluationIsLive
    "RH pole-quotient backward consumer: B_off + B_Gamma < M_cluster"
    "H_off^pole: finite reflection-paired target-centred nearOffFinset evaluation on the final high-ordinate pole taper"

gammaPrecisionRepairSchedulable :
  RHBidiSchedulable improveGammaEvaluation
gammaPrecisionRepairSchedulable =
  rh-bidi-schedulable
    gammaPrecisionRepairIsLive
    "RH pole-quotient backward consumer: B_off + B_Gamma < M_cluster"
    "H_Gamma consumer-sufficient O(|t|^-2)-scale evaluation"

------------------------------------------------------------------------
-- The active high-ordinate queue is exactly the two live analytic producers.
------------------------------------------------------------------------

data ActiveHighOrdinateExperiment : RHBidiExperiment → Set where
  activeFiniteNear : ActiveHighOrdinateExperiment evaluateFiniteNearSignedSum
  activeGammaRepair : ActiveHighOrdinateExperiment improveGammaEvaluation

schedulableIsActive :
  (experiment : RHBidiExperiment) →
  RHBidiSchedulable experiment →
  ActiveHighOrdinateExperiment experiment
schedulableIsActive evaluateFiniteNearSignedSum s = activeFiniteNear
schedulableIsActive improveGammaEvaluation s = activeGammaRepair
schedulableIsActive repeatClusterMarginProof s =
  ⊥-elim (clusterMarginRepeatNotSchedulable s)
schedulableIsActive reproveGenericCutoffInstantiation s =
  ⊥-elim (genericCutoffInstantiationRepeatNotSchedulable s)
schedulableIsActive reproveInfiniteFarShell s =
  ⊥-elim (farShellRepeatNotSchedulable s)
schedulableIsActive sharpenBalanceBudgetRoute s =
  ⊥-elim (balanceRouteNotSchedulable s)
schedulableIsActive auditNamedExternalDonor s =
  ⊥-elim (nameOnlyDonorNotSchedulable s)

------------------------------------------------------------------------
-- Highest-alpha selection only after the RH gate.
------------------------------------------------------------------------

record RHBidiCostSurface : Set₁ where
  constructor rh-bidi-cost-surface
  field
    cost : RHBidiExperiment → Nat
    Declared : RHBidiExperiment → Set
    costReference : String
    declarationReference : RHBidiExperiment → String

open RHBidiCostSurface public

record HighestAlphaRHExperiment (surface : RHBidiCostSurface) : Set₁ where
  constructor highest-alpha-rh-experiment
  field
    selected : RHBidiExperiment
    selectedDeclared : Declared surface selected
    selectedSchedulable : RHBidiSchedulable selected
    minimalAmongDeclaredLive :
      (alternative : RHBidiExperiment) →
      Declared surface alternative →
      RHBidiSchedulable alternative →
      cost surface selected ≤ cost surface alternative
    selectionReference : String

open HighestAlphaRHExperiment public

highestAlphaAlwaysTargetsActiveRHLeaf :
  (surface : RHBidiCostSurface) →
  (selection : HighestAlphaRHExperiment surface) →
  ActiveHighOrdinateExperiment (selected selection)
highestAlphaAlwaysTargetsActiveRHLeaf surface selection =
  schedulableIsActive (selected selection) (selectedSchedulable selection)

------------------------------------------------------------------------
-- Source-backed frontier receipts feeding this recursive queue.
------------------------------------------------------------------------

farShellAlreadyOwned :
  HOff.checkedLeanFarShellBoundOwned
    HOff.canonicalPoleQuotientOffOrdinateNearFarBoundary ≡ true
farShellAlreadyOwned = refl

genericCutoffTaperInstantiationNeedsNoNewAnalyticTheorem :
  HOff.separatePoleTaperTransportResearchTheoremRequired
    HOff.canonicalPoleQuotientOffOrdinateNearFarBoundary ≡ false
genericCutoffTaperInstantiationNeedsNoNewAnalyticTheorem = refl

finiteNearEvaluationStillOpen :
  HOff.finitePoleQuotientNearSignedEvaluationClosed
    HOff.canonicalPoleQuotientOffOrdinateNearFarBoundary ≡ false
finiteNearEvaluationStillOpen = refl

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

record RHBidiSearchSchedulerBoundary : Set where
  constructor rh-bidi-search-scheduler-boundary
  field
    schedulerPursuesOnlyRHProducerNodes : Bool
    schedulerPursuesOnlyRHProducerNodesIsTrue :
      schedulerPursuesOnlyRHProducerNodes ≡ true

    recursiveBackwardCutRefinementEnabled : Bool
    recursiveBackwardCutRefinementEnabledIsTrue :
      recursiveBackwardCutRefinementEnabled ≡ true

    genericCutoffInstantiationRemainsInActiveQueue : Bool
    genericCutoffInstantiationRemainsInActiveQueueIsFalse :
      genericCutoffInstantiationRemainsInActiveQueue ≡ false

    infiniteFarShellRemainsPrimarySearchLeaf : Bool
    infiniteFarShellRemainsPrimarySearchLeafIsFalse :
      infiniteFarShellRemainsPrimarySearchLeaf ≡ false

    closedClusterMarginRemainsInActiveQueue : Bool
    closedClusterMarginRemainsInActiveQueueIsFalse :
      closedClusterMarginRemainsInActiveQueue ≡ false

    balanceCircularityRouteRemainsInActiveQueue : Bool
    balanceCircularityRouteRemainsInActiveQueueIsFalse :
      balanceCircularityRouteRemainsInActiveQueue ≡ false

    nameOnlyHardyDonorRemainsInActiveQueue : Bool
    nameOnlyHardyDonorRemainsInActiveQueueIsFalse :
      nameOnlyHardyDonorRemainsInActiveQueue ≡ false

    finiteNearSignedEvaluationActive : Bool
    finiteNearSignedEvaluationActiveIsTrue :
      finiteNearSignedEvaluationActive ≡ true

    gammaPrecisionRepairActive : Bool
    gammaPrecisionRepairActiveIsTrue : gammaPrecisionRepairActive ≡ true

    highestAlphaMeansMinimalCostAmongDeclaredLiveRHMovesOnly : Bool
    highestAlphaMeansMinimalCostAmongDeclaredLiveRHMovesOnlyIsTrue :
      highestAlphaMeansMinimalCostAmongDeclaredLiveRHMovesOnly ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

canonicalRHBidiSearchSchedulerBoundary : RHBidiSearchSchedulerBoundary
canonicalRHBidiSearchSchedulerBoundary =
  rh-bidi-search-scheduler-boundary
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
    false refl
