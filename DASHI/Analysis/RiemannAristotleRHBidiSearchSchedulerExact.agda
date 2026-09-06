module DASHI.Analysis.RiemannAristotleRHBidiSearchSchedulerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotleExperimentalProofSearchExact as Search
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as HOff
import DASHI.Analysis.RiemannG2GapSplitClusteringLeanReturn8894Exact as Gap
import DASHI.Analysis.RiemannAristotleZetaLocalCountLeanReturnExact as Z38

------------------------------------------------------------------------
-- RH-ONLY BIDI-AWARE SEARCH SCHEDULER
--
-- Consumer first, recursively. A candidate experiment is schedulable only if
-- it feeds an open producer node on the backward RH cut.
--
-- 8896 BIDI update: the optimized gap-split route exposes an additional live
-- zero-side producer, actual-zeta low-gap clustering
--
--   (4/pi^2) * highGapMass < lowGapMass,
--   D = pi/(3 Lambda).
--
-- This is NOT the already-closed `clusterMarginSocket`: that socket is the
-- off-line pole cluster margin M_cluster^pole.  The new clustering theorem is a
-- property of the retained zeta-zero mass distribution and feeds H_off.
--
-- The active high-ordinate queue is therefore three independent producer
-- classes: actual-zeta clustering, same-object finite-near evaluation, and
-- consumer-sufficient Gamma precision.  §37/§38 remove the constant-window and
-- zeta-upper-count searches from that queue.
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
  zetaLowGapClusteringNode
  offFiniteNearEvaluationNode
  gammaPrecisionNode
  : RHProducerNode

nodeFeedsSocket : RHProducerNode → Search.RHResearchSocket
nodeFeedsSocket zetaLowGapClusteringNode = Search.offOrdinateSocket
nodeFeedsSocket offFiniteNearEvaluationNode = Search.offOrdinateSocket
nodeFeedsSocket gammaPrecisionNode = Search.gammaSocket

------------------------------------------------------------------------
-- Candidate experiment classes for the exact current cut.
------------------------------------------------------------------------

data RHBidiExperiment : Set where
  proveActualZetaLowGapClustering
  evaluateFiniteNearSignedSum
  improveGammaEvaluation
  repeatClosedPoleClusterMarginProof
  repeatZetaUpperLocalCountProof
  repeatQuarterDensityConstantComparison
  reproveGenericCutoffInstantiation
  reproveInfiniteFarShell
  sharpenBalanceBudgetRoute
  auditNamedExternalDonor
  : RHBidiExperiment

data RHExperimentOutputKind : Set where
  directClusteringProducer
  directFiniteProducer
  consumerSufficientRepair
  redundantClosedProducer
  redundantCheckedProducer
  redundantGenericInstantiation
  redundantOwnedFarTail
  balanceDerived
  donorAuditOnly
  : RHExperimentOutputKind

outputKind : RHBidiExperiment → RHExperimentOutputKind
outputKind proveActualZetaLowGapClustering = directClusteringProducer
outputKind evaluateFiniteNearSignedSum = directFiniteProducer
outputKind improveGammaEvaluation = consumerSufficientRepair
outputKind repeatClosedPoleClusterMarginProof = redundantClosedProducer
outputKind repeatZetaUpperLocalCountProof = redundantCheckedProducer
outputKind repeatQuarterDensityConstantComparison = redundantCheckedProducer
outputKind reproveGenericCutoffInstantiation = redundantGenericInstantiation
outputKind reproveInfiniteFarShell = redundantOwnedFarTail
outputKind sharpenBalanceBudgetRoute = balanceDerived
outputKind auditNamedExternalDonor = donorAuditOnly

------------------------------------------------------------------------
-- Consumer-first admissibility.
------------------------------------------------------------------------

data InhabitsLiveRHProducer : RHBidiExperiment → Set where
  zetaLowGapClusteringIsLive :
    InhabitsLiveRHProducer proveActualZetaLowGapClustering
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

closedPoleClusterMarginRepeatNotSchedulable :
  RHBidiSchedulable repeatClosedPoleClusterMarginProof → ⊥
closedPoleClusterMarginRepeatNotSchedulable s with inhabitsLiveProducer s
... | ()

zetaUpperCountRepeatNotSchedulable :
  RHBidiSchedulable repeatZetaUpperLocalCountProof → ⊥
zetaUpperCountRepeatNotSchedulable s with inhabitsLiveProducer s
... | ()

quarterDensityComparisonRepeatNotSchedulable :
  RHBidiSchedulable repeatQuarterDensityConstantComparison → ⊥
quarterDensityComparisonRepeatNotSchedulable s with inhabitsLiveProducer s
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

zetaLowGapClusteringSchedulable :
  RHBidiSchedulable proveActualZetaLowGapClustering
zetaLowGapClusteringSchedulable =
  rh-bidi-schedulable
    zetaLowGapClusteringIsLive
    "RH off-ordinate backward consumer via optimized gap split"
    "actual zeta zeros: (4/pi^2) * highGapMass < lowGapMass at D = pi/(3 Lambda)"

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
-- The active high-ordinate queue after 8896.
------------------------------------------------------------------------

data ActiveHighOrdinateExperiment : RHBidiExperiment → Set where
  activeZetaClustering :
    ActiveHighOrdinateExperiment proveActualZetaLowGapClustering
  activeFiniteNear : ActiveHighOrdinateExperiment evaluateFiniteNearSignedSum
  activeGammaRepair : ActiveHighOrdinateExperiment improveGammaEvaluation

schedulableIsActive :
  (experiment : RHBidiExperiment) →
  RHBidiSchedulable experiment →
  ActiveHighOrdinateExperiment experiment
schedulableIsActive proveActualZetaLowGapClustering s = activeZetaClustering
schedulableIsActive evaluateFiniteNearSignedSum s = activeFiniteNear
schedulableIsActive improveGammaEvaluation s = activeGammaRepair
schedulableIsActive repeatClosedPoleClusterMarginProof s =
  ⊥-elim (closedPoleClusterMarginRepeatNotSchedulable s)
schedulableIsActive repeatZetaUpperLocalCountProof s =
  ⊥-elim (zetaUpperCountRepeatNotSchedulable s)
schedulableIsActive repeatQuarterDensityConstantComparison s =
  ⊥-elim (quarterDensityComparisonRepeatNotSchedulable s)
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

quarterDensityComparisonAlreadyPruned :
  Gap.GapSplitRelevant Gap.compareQuarterPeriodLowerConstantWithDensityUpperConstant
  → ⊥
quarterDensityComparisonAlreadyPruned = Gap.quarterDensityConstantComparisonPruned

zetaUpperCountAlreadyChecked :
  Z38.zetaShortWindowUpperCountOwnedInLean Z38.canonicalZetaLocalCountLeanReturn
  ≡ true
zetaUpperCountAlreadyChecked = refl

actualZetaClusteringNotYetClosed :
  Z38.actualZetaClusteringClosed Z38.canonicalZetaLocalCountLeanReturn ≡ false
actualZetaClusteringNotYetClosed = refl

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

    closedPoleClusterMarginRemainsInActiveQueue : Bool
    closedPoleClusterMarginRemainsInActiveQueueIsFalse :
      closedPoleClusterMarginRemainsInActiveQueue ≡ false

    zetaUpperCountRemainsInActiveQueue : Bool
    zetaUpperCountRemainsInActiveQueueIsFalse :
      zetaUpperCountRemainsInActiveQueue ≡ false

    quarterDensityConstantComparisonRemainsInActiveQueue : Bool
    quarterDensityConstantComparisonRemainsInActiveQueueIsFalse :
      quarterDensityConstantComparisonRemainsInActiveQueue ≡ false

    actualZetaLowGapClusteringActive : Bool
    actualZetaLowGapClusteringActiveIsTrue :
      actualZetaLowGapClusteringActive ≡ true

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
    false refl
    false refl
    true refl
    true refl
    true refl
    false refl
