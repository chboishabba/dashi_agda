module DASHI.Analysis.RiemannAristotleRHBidiSearchSchedulerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotleExperimentalProofSearchExact as Search
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as HOff
import DASHI.Analysis.RiemannG2GapSplitClusteringLeanReturn8894Exact as Gap
import DASHI.Analysis.RiemannAristotleZetaLocalCountLeanReturnExact as Z38
import DASHI.Analysis.RiemannG2AlpogeFurmanClusteringNonDescentExact as AFLocal
import DASHI.Analysis.RiemannG2LowGapClusteringMomentReductionExact as Moment
import DASHI.Analysis.RiemannG2SelectedTargetLocalMomentSameObjectExact as SelectedMoment
import DASHI.Analysis.RiemannG2SelectedDirectFiniteMomentBidiExact as Shared

------------------------------------------------------------------------
-- RH-ONLY BIDI-AWARE SEARCH SCHEDULER
--
-- Consumer first, recursively. A candidate experiment is schedulable only if
-- it feeds an open producer node on the backward RH cut.
--
-- 8896 BIDI update: the optimized gap-split route exposes the live actual-zeta
-- low-gap clustering theorem
--
--   (4/pi^2) * highGapMass < lowGapMass,
--   D = pi/(3 Lambda).
--
-- The clustering node is refined by a target-local second-moment compiler. The
-- actual analytic moment is not allowed to float on a parallel target/window.
-- More strongly, clustering and finite-near evaluation are now required to
-- share one selected/direct zero carrier through
-- `RiemannG2SelectedDirectFiniteMomentBidiExact.SelectedDirectFiniteWeld`.
--
-- Thus the same direct producer must carry targetRelativeGap, multiplicity,
-- nearIndex and the signed finite-near evaluation while being identified with
-- the existing ActualSelectedPoleNearProducer. The weld is a common upstream
-- gate for both the delta-moment route and the finite-near evaluation route.
--
-- Direct clustering remains an admissible alternative route. The Alpoge--Furman
-- global >2/3 simple/on-line theorem remains a relevant donor but is explicitly
-- rejected as a direct target-local clustering proof without localization.
--
-- This is NOT the already-closed `clusterMarginSocket`: that socket is the
-- off-line pole cluster margin M_cluster^pole. The new clustering theorem is a
-- property of the retained zeta-zero ordinate distribution and feeds H_off.
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
  selectedDirectZeroCarrierWeldNode
  zetaTargetLocalSecondMomentNode
  offFiniteNearEvaluationNode
  gammaPrecisionNode
  : RHProducerNode

nodeFeedsSocket : RHProducerNode → Search.RHResearchSocket
nodeFeedsSocket zetaLowGapClusteringNode = Search.offOrdinateSocket
nodeFeedsSocket selectedDirectZeroCarrierWeldNode = Search.offOrdinateSocket
nodeFeedsSocket zetaTargetLocalSecondMomentNode = Search.offOrdinateSocket
nodeFeedsSocket offFiniteNearEvaluationNode = Search.offOrdinateSocket
nodeFeedsSocket gammaPrecisionNode = Search.gammaSocket

data ProducerRefines : RHProducerNode → RHProducerNode → Set where
  targetLocalMomentRefinesClustering :
    ProducerRefines zetaTargetLocalSecondMomentNode zetaLowGapClusteringNode
  selectedDirectWeldFeedsMoment :
    ProducerRefines selectedDirectZeroCarrierWeldNode zetaTargetLocalSecondMomentNode
  selectedDirectWeldFeedsFiniteNear :
    ProducerRefines selectedDirectZeroCarrierWeldNode offFiniteNearEvaluationNode

------------------------------------------------------------------------
-- Candidate experiment classes for the exact current cut.
------------------------------------------------------------------------

data RHBidiExperiment : Set where
  proveActualZetaLowGapClustering
  weldSelectedDirectZeroCarrier
  proveTargetLocalSecondMoment
  evaluateFiniteNearSignedSum
  improveGammaEvaluation
  reuseGlobalSimpleZeroProportionAsLocalClustering
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
  sameObjectZeroCarrierWeld
  localMomentClusteringProducer
  directFiniteProducer
  consumerSufficientRepair
  rejectedNonlocalDonor
  redundantClosedProducer
  redundantCheckedProducer
  redundantGenericInstantiation
  redundantOwnedFarTail
  balanceDerived
  donorAuditOnly
  : RHExperimentOutputKind

outputKind : RHBidiExperiment → RHExperimentOutputKind
outputKind proveActualZetaLowGapClustering = directClusteringProducer
outputKind weldSelectedDirectZeroCarrier = sameObjectZeroCarrierWeld
outputKind proveTargetLocalSecondMoment = localMomentClusteringProducer
outputKind evaluateFiniteNearSignedSum = directFiniteProducer
outputKind improveGammaEvaluation = consumerSufficientRepair
outputKind reuseGlobalSimpleZeroProportionAsLocalClustering = rejectedNonlocalDonor
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
  selectedDirectZeroCarrierWeldIsLive :
    InhabitsLiveRHProducer weldSelectedDirectZeroCarrier
  zetaTargetLocalSecondMomentIsLive :
    InhabitsLiveRHProducer proveTargetLocalSecondMoment
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

globalSimpleZeroProportionNotSchedulableAsLocalClustering :
  RHBidiSchedulable reuseGlobalSimpleZeroProportionAsLocalClustering → ⊥
globalSimpleZeroProportionNotSchedulableAsLocalClustering s
  with inhabitsLiveProducer s
... | ()

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

selectedDirectZeroCarrierWeldSchedulable :
  RHBidiSchedulable weldSelectedDirectZeroCarrier
selectedDirectZeroCarrierWeldSchedulable =
  rh-bidi-schedulable
    selectedDirectZeroCarrierWeldIsLive
    "shared upstream gate for actual-zeta clustering and H_off finite-near evaluation"
    "RiemannG2SelectedDirectFiniteMomentBidiExact.SelectedDirectFiniteWeld: identify the existing DirectFinitePoleNearProducer with the existing ActualSelectedPoleNearProducer on target, cutoff, zero family, multiplicity, targetRelativeGap, pole taper, finite signed value and explicit-formula object"

zetaTargetLocalSecondMomentSchedulable :
  RHBidiSchedulable proveTargetLocalSecondMoment
zetaTargetLocalSecondMomentSchedulable =
  rh-bidi-schedulable
    zetaTargetLocalSecondMomentIsLive
    "actual-zeta low-gap clustering producer after same-object selected/direct weld"
    "SelectedDirectFiniteMomentProducer on the welded direct targetRelativeGap carrier; prove M2_norm with highGapMass <= M2_norm < 2*lowGapMass"

finiteNearEvaluationSchedulable :
  RHBidiSchedulable evaluateFiniteNearSignedSum
finiteNearEvaluationSchedulable =
  rh-bidi-schedulable
    finiteNearEvaluationIsLive
    "RH pole-quotient backward consumer: B_off + B_Gamma < M_cluster"
    "the SAME welded DirectFinitePoleNearProducer must carry the phase-preserving finite-near approximant/error receipt"

gammaPrecisionRepairSchedulable :
  RHBidiSchedulable improveGammaEvaluation
gammaPrecisionRepairSchedulable =
  rh-bidi-schedulable
    gammaPrecisionRepairIsLive
    "RH pole-quotient backward consumer: B_off + B_Gamma < M_cluster"
    "H_Gamma consumer-sufficient O(|t|^-2)-scale evaluation"

------------------------------------------------------------------------
-- The active high-ordinate queue after the shared-carrier refinement.
------------------------------------------------------------------------

data ActiveHighOrdinateExperiment : RHBidiExperiment → Set where
  activeZetaClustering :
    ActiveHighOrdinateExperiment proveActualZetaLowGapClustering
  activeSelectedDirectWeld :
    ActiveHighOrdinateExperiment weldSelectedDirectZeroCarrier
  activeZetaLocalMoment :
    ActiveHighOrdinateExperiment proveTargetLocalSecondMoment
  activeFiniteNear : ActiveHighOrdinateExperiment evaluateFiniteNearSignedSum
  activeGammaRepair : ActiveHighOrdinateExperiment improveGammaEvaluation

schedulableIsActive :
  (experiment : RHBidiExperiment) →
  RHBidiSchedulable experiment →
  ActiveHighOrdinateExperiment experiment
schedulableIsActive proveActualZetaLowGapClustering s = activeZetaClustering
schedulableIsActive weldSelectedDirectZeroCarrier s = activeSelectedDirectWeld
schedulableIsActive proveTargetLocalSecondMoment s = activeZetaLocalMoment
schedulableIsActive evaluateFiniteNearSignedSum s = activeFiniteNear
schedulableIsActive improveGammaEvaluation s = activeGammaRepair
schedulableIsActive reuseGlobalSimpleZeroProportionAsLocalClustering s =
  ⊥-elim (globalSimpleZeroProportionNotSchedulableAsLocalClustering s)
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

localMomentCompilerClosedInAgda :
  Moment.LocalMomentClusteringBoundary.natMomentToTwoToOneRatioCompilerClosedInAgda
    Moment.canonicalLocalMomentClusteringBoundary ≡ true
localMomentCompilerClosedInAgda = refl

selectedMomentSameObjectShapeOwned :
  SelectedMoment.SelectedTargetLocalMomentBoundary.selectedWindowMomentAttachmentIsExactConsumerShape
    SelectedMoment.canonicalSelectedTargetLocalMomentBoundary ≡ true
selectedMomentSameObjectShapeOwned = refl

selectedMomentSameObjectProducerStillOpen :
  SelectedMoment.SelectedTargetLocalMomentBoundary.selectedWindowMomentProducerInhabitedHere
    SelectedMoment.canonicalSelectedTargetLocalMomentBoundary ≡ false
selectedMomentSameObjectProducerStillOpen = refl

selectedDirectWeldRequired :
  Shared.SelectedDirectFiniteMomentBoundary.selectedAndDirectViewsMustBeWelded
    Shared.canonicalSelectedDirectFiniteMomentBoundary ≡ true
selectedDirectWeldRequired = refl

selectedDirectWeldStillOpen :
  Shared.SelectedDirectFiniteMomentBoundary.selectedDirectWeldInhabitedHere
    Shared.canonicalSelectedDirectFiniteMomentBoundary ≡ false
selectedDirectWeldStillOpen = refl

sharedDirectCarrierFeedsBothConsumers :
  Shared.SelectedDirectFiniteMomentBoundary.oneDirectGapCarrierCanFeedClusteringAndFiniteEvaluation
    Shared.canonicalSelectedDirectFiniteMomentBoundary ≡ true
sharedDirectCarrierFeedsBothConsumers = refl

secondSelectedWindowSearchPruned :
  Shared.paymentState Shared.recoverSecondSelectedWindow ≡ Shared.pruned
secondSelectedWindowSearchPruned = Shared.secondSelectedWindowPruned

secondDirectZeroFamilySearchPruned :
  Shared.paymentState Shared.recoverSecondDirectZeroFamily ≡ Shared.pruned
secondDirectZeroFamilySearchPruned = Shared.secondDirectZeroFamilyPruned

globalSimpleProportionCannotDirectlyCloseClustering :
  AFLocal.GlobalSimpleToLocalClusteringBoundary.alpogeFurmanDirectlyClosesGapSplitClustering
    AFLocal.canonicalGlobalSimpleToLocalClusteringBoundary ≡ false
globalSimpleProportionCannotDirectlyCloseClustering = refl

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

    selectedDirectZeroCarrierWeldActive : Bool
    selectedDirectZeroCarrierWeldActiveIsTrue :
      selectedDirectZeroCarrierWeldActive ≡ true

    targetLocalSecondMomentRefinementActive : Bool
    targetLocalSecondMomentRefinementActiveIsTrue :
      targetLocalSecondMomentRefinementActive ≡ true

    targetLocalSecondMomentUsesExistingSelectedWindow : Bool
    targetLocalSecondMomentUsesExistingSelectedWindowIsTrue :
      targetLocalSecondMomentUsesExistingSelectedWindow ≡ true

    clusteringAndFiniteNearForcedOntoSameDirectCarrier : Bool
    clusteringAndFiniteNearForcedOntoSameDirectCarrierIsTrue :
      clusteringAndFiniteNearForcedOntoSameDirectCarrier ≡ true

    globalSimpleZeroProportionDirectClusteringRouteActive : Bool
    globalSimpleZeroProportionDirectClusteringRouteActiveIsFalse :
      globalSimpleZeroProportionDirectClusteringRouteActive ≡ false

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
    true refl
    true refl
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
    false refl