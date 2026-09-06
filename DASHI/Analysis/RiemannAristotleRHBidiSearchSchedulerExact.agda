module DASHI.Analysis.RiemannAristotleRHBidiSearchSchedulerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotleExperimentalProofSearchExact as Search
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as HOff
import DASHI.Analysis.RiemannG2GapSplitClusteringLeanReturn8894Exact as Gap
import DASHI.Analysis.RiemannAristotleZetaLocalCountLeanReturnExact as Z38
import DASHI.Analysis.RiemannAristotlePoleQuotientDirectFiniteNearAttackExact as Direct
import DASHI.Analysis.RiemannG2TargetCenteredScalarCancellationAssemblyExact as Literal
import DASHI.Analysis.RiemannG2SelectedDirectFiniteMomentBidiExact as Shared

------------------------------------------------------------------------
-- RH-ONLY BIDI-AWARE SEARCH SCHEDULER
--
-- CORRECTED AFTER RE-READING THE CHECKED LEAN GAP-SPLIT THEOREMS.
--
-- The §35 inequality
--
--   (4/pi^2) * highGapMass < lowGapMass
--
-- is necessary for POSITIVITY of the gap-split lower bound. That positive floor
-- participates in a NO-GO (`not_scalar_bound_of_gap_split` / criterion variants)
-- against the desired small signed-scalar hypothesis. Therefore clustering is
-- useful obstruction information, but it is not a forward RH producer.
--
-- The canonical G2d/current-cut forward leaf is instead the literal signed
-- target-centred determinant sum. The direct owner now pins that theorem to
--
--   DirectSignedConsumerPayment P
--   = AcceptableForG2Consumer P (totalSignedResponse P),
--
-- and a recovered DirectFinitePoleNearProducer must carry that payment.
--
-- CURRENT LIVE QUEUE:
--
--   1. recover the literal consumer-sufficient DirectFinitePoleNearProducer;
--   2. repair Gamma precision.
--
-- After (1), selected-window attachment/budget transport becomes downstream.
-- The optional literal M2_delta / clustering audit remains diagnostic and may
-- explain when the gap-split NO-GO bites, but it is not scheduled as an RH leaf.
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
-- Forward RH producer nodes only.
------------------------------------------------------------------------

data RHProducerNode : Set where
  directFinitePoleNearProducerNode
  selectedDirectZeroCarrierWeldNode
  selectedFiniteNearConsumerAttachmentNode
  gammaPrecisionNode
  : RHProducerNode

nodeFeedsSocket : RHProducerNode → Search.RHResearchSocket
nodeFeedsSocket directFinitePoleNearProducerNode = Search.offOrdinateSocket
nodeFeedsSocket selectedDirectZeroCarrierWeldNode = Search.offOrdinateSocket
nodeFeedsSocket selectedFiniteNearConsumerAttachmentNode = Search.offOrdinateSocket
nodeFeedsSocket gammaPrecisionNode = Search.gammaSocket

data ProducerRefines : RHProducerNode → RHProducerNode → Set where
  directProducerFeedsSelectedWeld :
    ProducerRefines directFinitePoleNearProducerNode selectedDirectZeroCarrierWeldNode
  selectedDirectWeldFeedsFiniteConsumer :
    ProducerRefines selectedDirectZeroCarrierWeldNode selectedFiniteNearConsumerAttachmentNode

------------------------------------------------------------------------
-- Gap-split diagnostics are deliberately outside RHProducerNode.
------------------------------------------------------------------------

data GapSplitDiagnosticNode : Set where
  actualZetaLowGapClusteringDiagnostic
  literalTargetLocalSecondMomentDiagnostic
  : GapSplitDiagnosticNode

data DiagnosticRefines : GapSplitDiagnosticNode → GapSplitDiagnosticNode → Set where
  literalMomentRefinesClusteringDiagnostic :
    DiagnosticRefines literalTargetLocalSecondMomentDiagnostic
      actualZetaLowGapClusteringDiagnostic

------------------------------------------------------------------------
-- Candidate experiment classes. Old names remain so stale callers fail by
-- schedulability rather than by silently changing meaning.
------------------------------------------------------------------------

data RHBidiExperiment : Set where
  proveActualZetaLowGapClustering
  recoverDirectFinitePoleNearProducer
  weldSelectedDirectZeroCarrier
  proveTargetLocalSecondMoment
  attachDirectEvaluationToSelectedConsumer
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
  obstructionDiagnostic
  directFiniteProducer
  sameObjectZeroCarrierWeld
  selectedFiniteConsumerAttachment
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
outputKind proveActualZetaLowGapClustering = obstructionDiagnostic
outputKind recoverDirectFinitePoleNearProducer = directFiniteProducer
outputKind weldSelectedDirectZeroCarrier = sameObjectZeroCarrierWeld
outputKind proveTargetLocalSecondMoment = obstructionDiagnostic
outputKind attachDirectEvaluationToSelectedConsumer = selectedFiniteConsumerAttachment
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
-- Only genuinely live forward producers inhabit this relation NOW.
------------------------------------------------------------------------

data InhabitsLiveRHProducer : RHBidiExperiment → Set where
  directFinitePoleNearProducerIsLive :
    InhabitsLiveRHProducer recoverDirectFinitePoleNearProducer
  gammaPrecisionRepairIsLive :
    InhabitsLiveRHProducer improveGammaEvaluation

record RHBidiSchedulable (experiment : RHBidiExperiment) : Set where
  constructor rh-bidi-schedulable
  field
    inhabitsLiveProducer : InhabitsLiveRHProducer experiment
    rhConsumerReference : String
    producerInterfaceReference : String

open RHBidiSchedulable public

zetaClusteringNotSchedulableAsRHProducer :
  RHBidiSchedulable proveActualZetaLowGapClustering → ⊥
zetaClusteringNotSchedulableAsRHProducer s with inhabitsLiveProducer s
... | ()

targetLocalMomentNotSchedulableAsRHProducer :
  RHBidiSchedulable proveTargetLocalSecondMoment → ⊥
targetLocalMomentNotSchedulableAsRHProducer s with inhabitsLiveProducer s
... | ()

selectedWeldNotSchedulableBeforeDirectProducer :
  RHBidiSchedulable weldSelectedDirectZeroCarrier → ⊥
selectedWeldNotSchedulableBeforeDirectProducer s with inhabitsLiveProducer s
... | ()

selectedConsumerAttachmentNotSchedulableBeforeDirectProducer :
  RHBidiSchedulable attachDirectEvaluationToSelectedConsumer → ⊥
selectedConsumerAttachmentNotSchedulableBeforeDirectProducer s with inhabitsLiveProducer s
... | ()

globalSimpleZeroProportionNotSchedulableAsLocalClustering :
  RHBidiSchedulable reuseGlobalSimpleZeroProportionAsLocalClustering → ⊥
globalSimpleZeroProportionNotSchedulableAsLocalClustering s with inhabitsLiveProducer s
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

directFinitePoleNearProducerSchedulable :
  RHBidiSchedulable recoverDirectFinitePoleNearProducer
directFinitePoleNearProducerSchedulable =
  rh-bidi-schedulable
    directFinitePoleNearProducerIsLive
    "G2d literal signed target-centred scalar consumer"
    "DirectFinitePoleNearProducer carrying DirectSignedConsumerPayment = AcceptableForG2Consumer(totalSignedResponse) on the canonical LiteralTargetCenteredScalarProblem; canonical carrier fields compile from that problem"

gammaPrecisionRepairSchedulable :
  RHBidiSchedulable improveGammaEvaluation
gammaPrecisionRepairSchedulable =
  rh-bidi-schedulable
    gammaPrecisionRepairIsLive
    "RH pole-quotient backward consumer: B_off + B_Gamma < M_cluster"
    "H_Gamma consumer-sufficient O(|t|^-2)-scale evaluation"

------------------------------------------------------------------------
-- Active queue has exactly the two current forward leaves.
------------------------------------------------------------------------

data ActiveHighOrdinateExperiment : RHBidiExperiment → Set where
  activeDirectFiniteProducer :
    ActiveHighOrdinateExperiment recoverDirectFinitePoleNearProducer
  activeGammaRepair :
    ActiveHighOrdinateExperiment improveGammaEvaluation

schedulableIsActive :
  (experiment : RHBidiExperiment) →
  RHBidiSchedulable experiment →
  ActiveHighOrdinateExperiment experiment
schedulableIsActive proveActualZetaLowGapClustering s =
  ⊥-elim (zetaClusteringNotSchedulableAsRHProducer s)
schedulableIsActive recoverDirectFinitePoleNearProducer s = activeDirectFiniteProducer
schedulableIsActive weldSelectedDirectZeroCarrier s =
  ⊥-elim (selectedWeldNotSchedulableBeforeDirectProducer s)
schedulableIsActive proveTargetLocalSecondMoment s =
  ⊥-elim (targetLocalMomentNotSchedulableAsRHProducer s)
schedulableIsActive attachDirectEvaluationToSelectedConsumer s =
  ⊥-elim (selectedConsumerAttachmentNotSchedulableBeforeDirectProducer s)
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
-- Source-backed frontier receipts.
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
  Z38.zetaShortWindowUpperCountOwnedInLean Z38.canonicalZetaLocalCountLeanReturn ≡ true
zetaUpperCountAlreadyChecked = refl

actualZetaClusteringNotYetClosed :
  Z38.actualZetaClusteringClosed Z38.canonicalZetaLocalCountLeanReturn ≡ false
actualZetaClusteringNotYetClosed = refl

clusteringIsGapSplitDiagnosticNotRHProducer :
  Gap.clusteringDirectlyPaysRHScalarConsumer
    Gap.canonicalGapSplitClusteringLeanReturn8894 ≡ false
clusteringIsGapSplitDiagnosticNotRHProducer = Gap.clusteringDoesNotDirectlyPayRH

directProducerRequiresCanonicalConsumerPayment :
  Direct.DirectFiniteNearAttackBoundary.directProducerCarriesCanonicalConsumerPayment
    Direct.canonicalDirectFiniteNearAttackBoundary ≡ true
directProducerRequiresCanonicalConsumerPayment = refl

genericWithinAloneDoesNotCloseDirectConsumer :
  Direct.DirectFiniteNearAttackBoundary.genericWithinReceiptAloneIsSufficient
    Direct.canonicalDirectFiniteNearAttackBoundary ≡ false
genericWithinAloneDoesNotCloseDirectConsumer = refl

literalDirectAcceptanceCompilerOwned :
  Literal.TargetCenteredScalarCancellationBoundary.directSignedAcceptanceCompilesToExactConsumerReceipt
    Literal.canonicalTargetCenteredScalarCancellationBoundary ≡ true
literalDirectAcceptanceCompilerOwned = refl

selectedDirectWeldStillDownstream :
  Shared.paymentState Shared.weldExistingDirectProducerToSelectedWindow
    ≡ Shared.downstream
selectedDirectWeldStillDownstream = refl

literalMomentStillDownstreamDiagnostic :
  Shared.paymentState Shared.proveLiteralOrdinateMomentBoundAfterWeld
    ≡ Shared.downstream
literalMomentStillDownstreamDiagnostic = refl

------------------------------------------------------------------------
-- Boundary ledger.
------------------------------------------------------------------------

record RHBidiSearchSchedulerBoundary : Set where
  constructor rh-bidi-search-scheduler-boundary
  field
    schedulerPursuesOnlyRHProducerNodes : Bool
    schedulerPursuesOnlyRHProducerNodesIsTrue : schedulerPursuesOnlyRHProducerNodes ≡ true

    recursiveBackwardCutRefinementEnabled : Bool
    recursiveBackwardCutRefinementEnabledIsTrue : recursiveBackwardCutRefinementEnabled ≡ true

    genericCutoffInstantiationRemainsInActiveQueue : Bool
    genericCutoffInstantiationRemainsInActiveQueueIsFalse : genericCutoffInstantiationRemainsInActiveQueue ≡ false

    infiniteFarShellRemainsPrimarySearchLeaf : Bool
    infiniteFarShellRemainsPrimarySearchLeafIsFalse : infiniteFarShellRemainsPrimarySearchLeaf ≡ false

    closedPoleClusterMarginRemainsInActiveQueue : Bool
    closedPoleClusterMarginRemainsInActiveQueueIsFalse : closedPoleClusterMarginRemainsInActiveQueue ≡ false

    zetaUpperCountRemainsInActiveQueue : Bool
    zetaUpperCountRemainsInActiveQueueIsFalse : zetaUpperCountRemainsInActiveQueue ≡ false

    quarterDensityConstantComparisonRemainsInActiveQueue : Bool
    quarterDensityConstantComparisonRemainsInActiveQueueIsFalse : quarterDensityConstantComparisonRemainsInActiveQueue ≡ false

    actualZetaLowGapClusteringActive : Bool
    actualZetaLowGapClusteringActiveIsFalse : actualZetaLowGapClusteringActive ≡ false

    clusteringRetainedAsObstructionDiagnostic : Bool
    clusteringRetainedAsObstructionDiagnosticIsTrue : clusteringRetainedAsObstructionDiagnostic ≡ true

    directFinitePoleNearProducerActive : Bool
    directFinitePoleNearProducerActiveIsTrue : directFinitePoleNearProducerActive ≡ true

    directProducerCarriesCanonicalSignedConsumerPayment : Bool
    directProducerCarriesCanonicalSignedConsumerPaymentIsTrue :
      directProducerCarriesCanonicalSignedConsumerPayment ≡ true

    selectedDirectZeroCarrierWeldActive : Bool
    selectedDirectZeroCarrierWeldActiveIsFalse : selectedDirectZeroCarrierWeldActive ≡ false

    directProducerPrecedesSelectedDirectWeld : Bool
    directProducerPrecedesSelectedDirectWeldIsTrue : directProducerPrecedesSelectedDirectWeld ≡ true

    targetLocalSecondMomentRefinementActive : Bool
    targetLocalSecondMomentRefinementActiveIsFalse : targetLocalSecondMomentRefinementActive ≡ false

    targetLocalSecondMomentUsesExistingSelectedWindow : Bool
    targetLocalSecondMomentUsesExistingSelectedWindowIsTrue : targetLocalSecondMomentUsesExistingSelectedWindow ≡ true

    selectedFiniteConsumerAttachmentActive : Bool
    selectedFiniteConsumerAttachmentActiveIsFalse : selectedFiniteConsumerAttachmentActive ≡ false

    gammaPrecisionRepairActive : Bool
    gammaPrecisionRepairActiveIsTrue : gammaPrecisionRepairActive ≡ true

    highestAlphaMeansMinimalCostAmongDeclaredLiveRHMovesOnly : Bool
    highestAlphaMeansMinimalCostAmongDeclaredLiveRHMovesOnlyIsTrue : highestAlphaMeansMinimalCostAmongDeclaredLiveRHMovesOnly ≡ true

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
    false refl
    true refl
    true refl
    true refl
    false refl
    true refl
    false refl
    true refl
    false refl
    true refl
    true refl
    false refl
