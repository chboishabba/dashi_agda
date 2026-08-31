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
-- it feeds an open producer node on the backward RH cut.  The 8889 Lean return
-- closes M_cluster^pole and leaves H_Gamma consumer-insufficient.  The new
-- H_off near/far audit further decomposes H_off^pole into:
--
--   H_off carrier transport
--   + finite signed near evaluation
--   + already-owned arbitrary-accuracy far shell.
--
-- Hence the active high-ordinate queue is now exactly:
--
--   (1) identify the checked cutoff carrier with the final pole-quotient taper;
--   (2) evaluate the finite target-centred signed near sum on that carrier;
--   (3) repair H_Gamma to consumer-sufficient O(|t|^-2)-scale accuracy.
--
-- Re-proving the cluster margin, refining the balance identity, attacking the
-- infinite far shell as a fresh theorem, or searching a theorem merely because
-- it is labelled Hardy has no scheduling authority here.
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
  offCutoffCarrierTransportNode
  offFiniteNearEvaluationNode
  gammaPrecisionNode
  : RHProducerNode

nodeFeedsSocket : RHProducerNode → Search.RHResearchSocket
nodeFeedsSocket offCutoffCarrierTransportNode = Search.offOrdinateSocket
nodeFeedsSocket offFiniteNearEvaluationNode = Search.offOrdinateSocket
nodeFeedsSocket gammaPrecisionNode = Search.gammaSocket

data ProducerNodeStatus : Set where
  nodeOpen
  nodeClosed
  : ProducerNodeStatus

currentNodeStatus : RHProducerNode → ProducerNodeStatus
currentNodeStatus offCutoffCarrierTransportNode = nodeOpen
currentNodeStatus offFiniteNearEvaluationNode = nodeOpen
currentNodeStatus gammaPrecisionNode = nodeOpen

------------------------------------------------------------------------
-- Candidate experiment classes for the current exact cut.
------------------------------------------------------------------------

data RHBidiExperiment : Set where
  transportCutoffCarrierToPoleQuotient
  evaluateFiniteNearSignedSum
  improveGammaEvaluation
  repeatClusterMarginProof
  reproveInfiniteFarShell
  sharpenBalanceBudgetRoute
  auditNamedExternalDonor
  : RHBidiExperiment

data RHExperimentOutputKind : Set where
  carrierBridgeProducer
  directFiniteProducer
  consumerSufficientRepair
  redundantClosedProducer
  redundantOwnedFarTail
  balanceDerived
  donorAuditOnly
  : RHExperimentOutputKind

outputKind : RHBidiExperiment → RHExperimentOutputKind
outputKind transportCutoffCarrierToPoleQuotient = carrierBridgeProducer
outputKind evaluateFiniteNearSignedSum = directFiniteProducer
outputKind improveGammaEvaluation = consumerSufficientRepair
outputKind repeatClusterMarginProof = redundantClosedProducer
outputKind reproveInfiniteFarShell = redundantOwnedFarTail
outputKind sharpenBalanceBudgetRoute = balanceDerived
outputKind auditNamedExternalDonor = donorAuditOnly

experimentProducerNode :
  (experiment : RHBidiExperiment) →
  (outputKind experiment ≡ carrierBridgeProducer
    ⊎ outputKind experiment ≡ directFiniteProducer
    ⊎ outputKind experiment ≡ consumerSufficientRepair) →
  RHProducerNode
experimentProducerNode transportCutoffCarrierToPoleQuotient _ =
  offCutoffCarrierTransportNode
experimentProducerNode evaluateFiniteNearSignedSum _ =
  offFiniteNearEvaluationNode
experimentProducerNode improveGammaEvaluation _ = gammaPrecisionNode
experimentProducerNode repeatClusterMarginProof (inj₁ ())
experimentProducerNode repeatClusterMarginProof (inj₂ (inj₁ ()))
experimentProducerNode repeatClusterMarginProof (inj₂ (inj₂ ()))
experimentProducerNode reproveInfiniteFarShell (inj₁ ())
experimentProducerNode reproveInfiniteFarShell (inj₂ (inj₁ ()))
experimentProducerNode reproveInfiniteFarShell (inj₂ (inj₂ ()))
experimentProducerNode sharpenBalanceBudgetRoute (inj₁ ())
experimentProducerNode sharpenBalanceBudgetRoute (inj₂ (inj₁ ()))
experimentProducerNode sharpenBalanceBudgetRoute (inj₂ (inj₂ ()))
experimentProducerNode auditNamedExternalDonor (inj₁ ())
experimentProducerNode auditNamedExternalDonor (inj₂ (inj₁ ()))
experimentProducerNode auditNamedExternalDonor (inj₂ (inj₂ ()))

------------------------------------------------------------------------
-- Consumer-first admissibility.
------------------------------------------------------------------------

data InhabitsLiveRHProducer : RHBidiExperiment → Set where
  cutoffCarrierTransportIsLive :
    InhabitsLiveRHProducer transportCutoffCarrierToPoleQuotient
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

cutoffCarrierTransportSchedulable :
  RHBidiSchedulable transportCutoffCarrierToPoleQuotient
cutoffCarrierTransportSchedulable =
  rh-bidi-schedulable
    cutoffCarrierTransportIsLive
    "RH pole-quotient backward consumer: B_off + B_Gamma < M_cluster"
    "H_off^pole subcut: identify checked cutoff taper/response with final universal pole-quotient taper/response"

finiteNearEvaluationSchedulable :
  RHBidiSchedulable evaluateFiniteNearSignedSum
finiteNearEvaluationSchedulable =
  rh-bidi-schedulable
    finiteNearEvaluationIsLive
    "RH pole-quotient backward consumer: B_off + B_Gamma < M_cluster"
    "H_off^pole subcut: finite reflection-paired target-centred nearOffFinset evaluation"

gammaPrecisionRepairSchedulable :
  RHBidiSchedulable improveGammaEvaluation
gammaPrecisionRepairSchedulable =
  rh-bidi-schedulable
    gammaPrecisionRepairIsLive
    "RH pole-quotient backward consumer: B_off + B_Gamma < M_cluster"
    "H_Gamma consumer-sufficient O(|t|^-2)-scale evaluation"

------------------------------------------------------------------------
-- The active high-ordinate queue is exactly the three live producer nodes.
------------------------------------------------------------------------

data ActiveHighOrdinateExperiment : RHBidiExperiment → Set where
  activeCarrierTransport :
    ActiveHighOrdinateExperiment transportCutoffCarrierToPoleQuotient
  activeFiniteNear : ActiveHighOrdinateExperiment evaluateFiniteNearSignedSum
  activeGammaRepair : ActiveHighOrdinateExperiment improveGammaEvaluation

schedulableIsActive :
  (experiment : RHBidiExperiment) →
  RHBidiSchedulable experiment →
  ActiveHighOrdinateExperiment experiment
schedulableIsActive transportCutoffCarrierToPoleQuotient s = activeCarrierTransport
schedulableIsActive evaluateFiniteNearSignedSum s = activeFiniteNear
schedulableIsActive improveGammaEvaluation s = activeGammaRepair
schedulableIsActive repeatClusterMarginProof s =
  ⊥-elim (clusterMarginRepeatNotSchedulable s)
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

cutoffCarrierTransportStillOpen :
  HOff.oldCutoffCarrierTransportedToFinalPoleQuotientCarrier
    HOff.canonicalPoleQuotientOffOrdinateNearFarBoundary ≡ false
cutoffCarrierTransportStillOpen = refl

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

    cutoffCarrierTransportActive : Bool
    cutoffCarrierTransportActiveIsTrue : cutoffCarrierTransportActive ≡ true

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
    true refl
    true refl
    true refl
    true refl
    false refl
