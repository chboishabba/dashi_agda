module DASHI.Analysis.RiemannAristotleRHBidiSearchSchedulerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotleExperimentalProofSearchExact as Search

------------------------------------------------------------------------
-- RH-ONLY BIDI-AWARE SEARCH SCHEDULER
--
-- This scheduler is deliberately consumer-first.  A locally interesting
-- theorem experiment is not schedulable merely because it advances some
-- mathematics.  Its certified output must inhabit a producer socket still
-- required by the backward RH consumer cut.
--
-- The current pole-quotient cut has three named sockets, but the 8889 Lean
-- return changes their states:
--
--   offOrdinateSocket : open / no producer owned
--   gammaSocket       : partial / a bound exists but fails the consumer window
--   clusterMargin     : closed / quantitative producer owned
--
-- Hence the active high-ordinate queue is exactly:
--
--   (1) produce H_off^pole;
--   (2) repair H_Gamma to consumer-sufficient O(|t|^-2)-scale accuracy.
--
-- Re-proving the cluster margin, refining the balance identity, or searching a
-- theorem merely because it is labelled Hardy is not an admissible RH search
-- move unless a literal producer bridge changes one of those two live sockets.
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
-- Candidate experiment classes for the current RH cut.
------------------------------------------------------------------------

data RHBidiExperiment : Set where
  deriveOffOrdinateEvaluation
  improveGammaEvaluation
  repeatClusterMarginProof
  sharpenBalanceBudgetRoute
  auditNamedExternalDonor
  : RHBidiExperiment

experimentTarget : RHBidiExperiment → Search.RHResearchSocket
experimentTarget deriveOffOrdinateEvaluation = Search.offOrdinateSocket
experimentTarget improveGammaEvaluation = Search.gammaSocket
experimentTarget repeatClusterMarginProof = Search.clusterMarginSocket
experimentTarget sharpenBalanceBudgetRoute = Search.offOrdinateSocket
experimentTarget auditNamedExternalDonor = Search.offOrdinateSocket

------------------------------------------------------------------------
-- Output authority is separate from experiment identity.
--
-- A direct producer literally inhabits the missing theorem interface.
-- A precision repair strengthens an already-owned producer enough to satisfy
-- the downstream consumer.  DonorAuditOnly means no literal carrier bridge has
-- yet been supplied.  BalanceDerived is rejected by the checked circularity
-- no-go.
------------------------------------------------------------------------

data RHExperimentOutputKind : Set where
  directProducer
  consumerSufficientRepair
  redundantClosedProducer
  balanceDerived
  donorAuditOnly
  : RHExperimentOutputKind

outputKind : RHBidiExperiment → RHExperimentOutputKind
outputKind deriveOffOrdinateEvaluation = directProducer
outputKind improveGammaEvaluation = consumerSufficientRepair
outputKind repeatClusterMarginProof = redundantClosedProducer
outputKind sharpenBalanceBudgetRoute = balanceDerived
outputKind auditNamedExternalDonor = donorAuditOnly

------------------------------------------------------------------------
-- Consumer-first admissibility.
------------------------------------------------------------------------

data InhabitsLiveProducerSocket : RHBidiExperiment → Set where
  offProducerIsLive : InhabitsLiveProducerSocket deriveOffOrdinateEvaluation
  gammaRepairIsLive : InhabitsLiveProducerSocket improveGammaEvaluation

-- No constructor exists for the other experiment classes.
-- This is the scheduler's main guard: local mathematical progress outside a
-- live RH producer socket has zero scheduling authority here.

record RHBidiSchedulable (experiment : RHBidiExperiment) : Set where
  constructor rh-bidi-schedulable
  field
    inhabitsLiveProducer : InhabitsLiveProducerSocket experiment
    rhConsumerReference : String
    producerInterfaceReference : String

open RHBidiSchedulable public

------------------------------------------------------------------------
-- Exact pruning theorems for the 8889 frontier.
------------------------------------------------------------------------

clusterMarginRepeatNotSchedulable :
  RHBidiSchedulable repeatClusterMarginProof → ⊥
clusterMarginRepeatNotSchedulable s with inhabitsLiveProducer s
... | ()

balanceRouteNotSchedulable :
  RHBidiSchedulable sharpenBalanceBudgetRoute → ⊥
balanceRouteNotSchedulable s with inhabitsLiveProducer s
... | ()

nameOnlyDonorNotSchedulable :
  RHBidiSchedulable auditNamedExternalDonor → ⊥
nameOnlyDonorNotSchedulable s with inhabitsLiveProducer s
... | ()

offOrdinateDirectProducerSchedulable :
  RHBidiSchedulable deriveOffOrdinateEvaluation
offOrdinateDirectProducerSchedulable =
  rh-bidi-schedulable
    offProducerIsLive
    "RH pole-quotient backward consumer: B_off + B_Gamma < M_cluster"
    "H_off^pole signed target-centered off-ordinate evaluation"

gammaPrecisionRepairSchedulable :
  RHBidiSchedulable improveGammaEvaluation
gammaPrecisionRepairSchedulable =
  rh-bidi-schedulable
    gammaRepairIsLive
    "RH pole-quotient backward consumer: B_off + B_Gamma < M_cluster"
    "H_Gamma consumer-sufficient O(|t|^-2)-scale evaluation"

------------------------------------------------------------------------
-- The active high-ordinate queue is exactly the two live producer obligations.
------------------------------------------------------------------------

data ActiveHighOrdinateExperiment : RHBidiExperiment → Set where
  activeOff : ActiveHighOrdinateExperiment deriveOffOrdinateEvaluation
  activeGammaRepair : ActiveHighOrdinateExperiment improveGammaEvaluation

schedulableIsActive :
  (experiment : RHBidiExperiment) →
  RHBidiSchedulable experiment →
  ActiveHighOrdinateExperiment experiment
schedulableIsActive deriveOffOrdinateEvaluation s = activeOff
schedulableIsActive improveGammaEvaluation s = activeGammaRepair
schedulableIsActive repeatClusterMarginProof s =
  ⊥-elim (clusterMarginRepeatNotSchedulable s)
schedulableIsActive sharpenBalanceBudgetRoute s =
  ⊥-elim (balanceRouteNotSchedulable s)
schedulableIsActive auditNamedExternalDonor s =
  ⊥-elim (nameOnlyDonorNotSchedulable s)

------------------------------------------------------------------------
-- Highest-alpha selection only after the RH gate.
--
-- We do not infer theorem difficulty or success probability.  An application
-- may declare a resource cost over the already-gated active experiments.  A
-- selected next experiment is highest-alpha here only in the bounded sense:
-- it is live for the backward RH consumer and no more costly than every other
-- declared live experiment.
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
-- Boundaries.
------------------------------------------------------------------------

record RHBidiSearchSchedulerBoundary : Set where
  constructor rh-bidi-search-scheduler-boundary
  field
    schedulerPursuesOnlyRHProducerSockets : Bool
    schedulerPursuesOnlyRHProducerSocketsIsTrue :
      schedulerPursuesOnlyRHProducerSockets ≡ true

    localMathematicalProgressWithoutRHConsumerBridgeSchedulable : Bool
    localMathematicalProgressWithoutRHConsumerBridgeSchedulableIsFalse :
      localMathematicalProgressWithoutRHConsumerBridgeSchedulable ≡ false

    closedClusterMarginRemainsInActiveQueue : Bool
    closedClusterMarginRemainsInActiveQueueIsFalse :
      closedClusterMarginRemainsInActiveQueue ≡ false

    balanceCircularityRouteRemainsInActiveQueue : Bool
    balanceCircularityRouteRemainsInActiveQueueIsFalse :
      balanceCircularityRouteRemainsInActiveQueue ≡ false

    nameOnlyHardyDonorRemainsInActiveQueue : Bool
    nameOnlyHardyDonorRemainsInActiveQueueIsFalse :
      nameOnlyHardyDonorRemainsInActiveQueue ≡ false

    offOrdinateEvaluationActive : Bool
    offOrdinateEvaluationActiveIsTrue : offOrdinateEvaluationActive ≡ true

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
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
    false refl
