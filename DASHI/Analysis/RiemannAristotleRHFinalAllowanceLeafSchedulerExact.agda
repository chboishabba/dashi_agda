module DASHI.Analysis.RiemannAristotleRHFinalAllowanceLeafSchedulerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotleRHAnalyticLeafSchedulerExact as Historical
import DASHI.Analysis.RiemannG2PoleQuotientFinalCutReconciliationExact as FinalCut
import DASHI.Analysis.RiemannG2PoleQuotientProducerAllowanceTargetExact as ProducerAllowance
import DASHI.Analysis.RiemannG2PoleQuotientOffAllowanceDirectCompilerExact as OffDirect
import DASHI.Analysis.RiemannG2FinalSplitComplementAllowanceAssemblyExact as Assembly

------------------------------------------------------------------------
-- AUTHORITATIVE FINAL-CARRIER RH ANALYTIC SCHEDULER
--
-- Historical H_X / modulation / determinant-direct nodes remain useful route
-- diagnostics and infrastructure. They are not the terminal high-ordinate RH
-- consumer. The final pole-quotient cut has exact producer-facing leaf types
-- carrying downstream-assigned allowances.
--
-- The Off leaf is not "make the far tail small" in isolation. The direct final
-- compiler requires ONE common quarter-period crossing cutoff J at which the
-- signed near budget and the owned far budget together fit A_off.
------------------------------------------------------------------------

data FinalRHAnalyticLeaf : Set where
  proveUniversalPoleQuotientOffAllowancePayment
  proveSameTaperGammaAllowancePayment
  attachOwnedClusterMarginSameObject
  transportAllowancePaymentsToFinalOrder
  rebuildStrictCombinedBudget
  rebuildFinalContradictionCompiler
  reopenDeterminantDiagnosticAsFinalCarrier
  reopenGapSplitClusteringAsForwardProducer
  : FinalRHAnalyticLeaf

data FinalLeafState : Set where
  open downstream pruned : FinalLeafState

finalLeafState : FinalRHAnalyticLeaf → FinalLeafState
finalLeafState proveUniversalPoleQuotientOffAllowancePayment = open
finalLeafState proveSameTaperGammaAllowancePayment = open
finalLeafState attachOwnedClusterMarginSameObject = downstream
finalLeafState transportAllowancePaymentsToFinalOrder = downstream
finalLeafState rebuildStrictCombinedBudget = pruned
finalLeafState rebuildFinalContradictionCompiler = pruned
finalLeafState reopenDeterminantDiagnosticAsFinalCarrier = pruned
finalLeafState reopenGapSplitClusteringAsForwardProducer = pruned

OffLeafPayment : Set₁
OffLeafPayment = ProducerAllowance.PoleQuotientOffAllowancePayment

GammaLeafPayment : Set₁
GammaLeafPayment = ProducerAllowance.PoleQuotientGammaAllowancePayment

------------------------------------------------------------------------
-- Only the two literal analytic payments are schedulable.
------------------------------------------------------------------------

data FinalRHLeafSchedulable : FinalRHAnalyticLeaf → Set where
  finalOffAllowanceLeafLive :
    FinalRHLeafSchedulable proveUniversalPoleQuotientOffAllowancePayment
  finalGammaAllowanceLeafLive :
    FinalRHLeafSchedulable proveSameTaperGammaAllowancePayment

clusterAttachmentNotAnalyticLeaf :
  FinalRHLeafSchedulable attachOwnedClusterMarginSameObject → ⊥
clusterAttachmentNotAnalyticLeaf ()

allowanceOrderTransportNotAnalyticLeaf :
  FinalRHLeafSchedulable transportAllowancePaymentsToFinalOrder → ⊥
allowanceOrderTransportNotAnalyticLeaf ()

combinedBudgetRebuildPruned :
  FinalRHLeafSchedulable rebuildStrictCombinedBudget → ⊥
combinedBudgetRebuildPruned ()

finalCompilerRebuildPruned :
  FinalRHLeafSchedulable rebuildFinalContradictionCompiler → ⊥
finalCompilerRebuildPruned ()

determinantPromotionPruned :
  FinalRHLeafSchedulable reopenDeterminantDiagnosticAsFinalCarrier → ⊥
determinantPromotionPruned ()

clusteringPromotionPruned :
  FinalRHLeafSchedulable reopenGapSplitClusteringAsForwardProducer → ⊥
clusteringPromotionPruned ()

------------------------------------------------------------------------
-- Highest-alpha selection on the final carrier only.
------------------------------------------------------------------------

record FinalRHLeafCostSurface : Set₁ where
  constructor final-rh-leaf-cost-surface
  field
    cost : FinalRHAnalyticLeaf → Nat
    Declared : FinalRHAnalyticLeaf → Set
    costReference : String

open FinalRHLeafCostSurface public

record SelectedFinalRHAnalyticLeaf (surface : FinalRHLeafCostSurface) : Set₁ where
  constructor selected-final-rh-analytic-leaf
  field
    selected : FinalRHAnalyticLeaf
    selectedDeclared : Declared surface selected
    selectedSchedulable : FinalRHLeafSchedulable selected
    minimalAmongDeclaredLive :
      (alternative : FinalRHAnalyticLeaf) →
      Declared surface alternative →
      FinalRHLeafSchedulable alternative →
      cost surface selected ≤ cost surface alternative
    selectionReference : String

open SelectedFinalRHAnalyticLeaf public

------------------------------------------------------------------------
-- Reconciliation pins.
------------------------------------------------------------------------

finalCutSaysOffIsLive :
  FinalCut.finalLeafState FinalCut.universalPoleQuotientSignedOff
    ≡ FinalCut.live
finalCutSaysOffIsLive = FinalCut.universalPoleQuotientOffIsLive

finalCutSaysGammaIsLive :
  FinalCut.finalLeafState FinalCut.sameTaperGammaPrecision
    ≡ FinalCut.live
finalCutSaysGammaIsLive = FinalCut.gammaPrecisionIsLive

finalCutSaysDeterminantIsDiagnostic :
  FinalCut.finalLeafState FinalCut.determinantSignedDiagnostic
    ≡ FinalCut.diagnostic
finalCutSaysDeterminantIsDiagnostic = FinalCut.determinantPaymentIsDiagnostic

offCompilerRequiresOneCommonCrossingCutoff :
  OffDirect.PoleQuotientOffAllowanceDirectCompilerBoundary.oneCommonCrossingCutoffRequired
    OffDirect.canonicalPoleQuotientOffAllowanceDirectCompilerBoundary ≡ true
offCompilerRequiresOneCommonCrossingCutoff = refl

offCompilerPrunesFarOnlyCutoffChoice :
  OffDirect.PoleQuotientOffAllowanceDirectCompilerBoundary.farDecayAloneSelectsFinalCutoff
    OffDirect.canonicalPoleQuotientOffAllowanceDirectCompilerBoundary ≡ false
offCompilerPrunesFarOnlyCutoffChoice = refl

offCompilerMakesFinalPaymentCompilerOutput :
  OffDirect.PoleQuotientOffAllowanceDirectCompilerBoundary.finalOffTargetAndAllowancePaymentCompile
    OffDirect.canonicalPoleQuotientOffAllowanceDirectCompilerBoundary ≡ true
offCompilerMakesFinalPaymentCompilerOutput = refl

allowanceAssemblyMakesStrictBudgetCompilerOutput :
  Assembly.FinalAllowanceAssemblyBoundary.strictCombinedBudgetIsFreshPostAnalysisLeaf
    Assembly.canonicalFinalAllowanceAssemblyBoundary ≡ false
allowanceAssemblyMakesStrictBudgetCompilerOutput = refl

historicalSchedulerRetainedForRouteDiagnostics : Bool
historicalSchedulerRetainedForRouteDiagnostics = true

historicalSchedulerRetainedForRouteDiagnosticsIsTrue :
  historicalSchedulerRetainedForRouteDiagnostics ≡ true
historicalSchedulerRetainedForRouteDiagnosticsIsTrue = refl

record FinalRHAllowanceSchedulerBoundary : Set where
  constructor final-rh-allowance-scheduler-boundary
  field
    terminalHighOrdinateSchedulerUsesPoleQuotientCarrier : Bool
    terminalHighOrdinateSchedulerUsesPoleQuotientCarrierIsTrue :
      terminalHighOrdinateSchedulerUsesPoleQuotientCarrier ≡ true

    determinantDirectProducerStillSchedulableAsTerminalLeaf : Bool
    determinantDirectProducerStillSchedulableAsTerminalLeafIsFalse :
      determinantDirectProducerStillSchedulableAsTerminalLeaf ≡ false

    complexCharacterInfrastructureStillSchedulableAheadOfLiteralFinalOffLeaf : Bool
    complexCharacterInfrastructureStillSchedulableAheadOfLiteralFinalOffLeafIsFalse :
      complexCharacterInfrastructureStillSchedulableAheadOfLiteralFinalOffLeaf ≡ false

    finalOffAllowancePaymentSchedulable : Bool
    finalOffAllowancePaymentSchedulableIsTrue :
      finalOffAllowancePaymentSchedulable ≡ true

    finalOffLeafUsesOneCommonCrossingCutoff : Bool
    finalOffLeafUsesOneCommonCrossingCutoffIsTrue :
      finalOffLeafUsesOneCommonCrossingCutoff ≡ true

    farTailDecayAloneIsFinalOffLeaf : Bool
    farTailDecayAloneIsFinalOffLeafIsFalse :
      farTailDecayAloneIsFinalOffLeaf ≡ false

    finalGammaAllowancePaymentSchedulable : Bool
    finalGammaAllowancePaymentSchedulableIsTrue :
      finalGammaAllowancePaymentSchedulable ≡ true

    clusterAttachmentIsFreshHarmonicAnalysis : Bool
    clusterAttachmentIsFreshHarmonicAnalysisIsFalse :
      clusterAttachmentIsFreshHarmonicAnalysis ≡ false

    strictCombinedBudgetIsFreshAnalyticLeaf : Bool
    strictCombinedBudgetIsFreshAnalyticLeafIsFalse :
      strictCombinedBudgetIsFreshAnalyticLeaf ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalFinalRHAllowanceSchedulerBoundary : FinalRHAllowanceSchedulerBoundary
canonicalFinalRHAllowanceSchedulerBoundary =
  final-rh-allowance-scheduler-boundary
    true refl
    false refl
    false refl
    true refl
    true refl
    false refl
    true refl
    false refl
    false refl
    false refl
    "Use the historical analytic scheduler only to navigate possible proof routes. Terminal high-ordinate RH scheduling occurs on the universal pole-quotient carrier and admits exactly two analytic payments: PoleQuotientOffAllowancePayment and PoleQuotientGammaAllowancePayment. The Off payment must be established at one common quarter-period crossing cutoff where the signed near budget plus the owned far budget fits the assigned A_off; far-tail decay alone cannot choose that cutoff. Cluster attachment and same-order transport are downstream engineering; strict budget composition and final contradiction are compiler output. Do not schedule determinant scalarization, H_X infrastructure, or gap-split clustering ahead of the literal final allowance leaves. RH is not derived."
