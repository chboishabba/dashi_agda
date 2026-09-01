module DASHI.Analysis.RiemannG2PoleQuotientProducerReconciliation8889Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientCurrentCutExact as Current
import DASHI.Analysis.RiemannAristotlePoleQuotientGammaBudgetTargetExact as Gamma
import DASHI.Analysis.RiemannAristotlePoleQuotientClusterMarginTargetExact as Cluster
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateBudgetTargetExact as Off
import DASHI.Analysis.RiemannG2QuarterPeriodPoleQuotientFinalCompilerExact as Final

------------------------------------------------------------------------
-- 8889 POLE-QUOTIENT PRODUCER RECONCILIATION
--
-- Cross-branch checked-Lean provenance reports:
--   * quantitative pole-quotient cluster margin owned;
--   * sharp O(|t|^-2)-scale margin demand owned;
--   * a uniform Gamma bound owned, but too coarse for that window;
--   * budget-circularity no-go owned;
--   * signed off-ordinate evaluation still unpaid.
--
-- No Lean proof term is transported here.  This owner only corrects the BIDI
-- search graph on the exact Agda target sockets already present on this branch.
------------------------------------------------------------------------

record CheckedLeanPoleQuotientReturn8889 : Set where
  constructor checked-lean-pole-quotient-return-8889
  field
    aggregateJobs : String
    quantitativeClusterMarginOwned : Bool
    quantitativeClusterMarginOwnedIsTrue : quantitativeClusterMarginOwned ≡ true
    sharpClusterAccuracyDemandOwned : Bool
    sharpClusterAccuracyDemandOwnedIsTrue : sharpClusterAccuracyDemandOwned ≡ true
    gammaUniformBoundOwned : Bool
    gammaUniformBoundOwnedIsTrue : gammaUniformBoundOwned ≡ true
    gammaUniformBoundFitsRequiredWindow : Bool
    gammaUniformBoundFitsRequiredWindowIsFalse :
      gammaUniformBoundFitsRequiredWindow ≡ false
    budgetCircularityNoGoOwned : Bool
    budgetCircularityNoGoOwnedIsTrue : budgetCircularityNoGoOwned ≡ true
    offOrdinateEvaluationOwned : Bool
    offOrdinateEvaluationOwnedIsFalse : offOrdinateEvaluationOwned ≡ false
    transportedIntoAgda : Bool
    transportedIntoAgdaIsFalse : transportedIntoAgda ≡ false

open CheckedLeanPoleQuotientReturn8889 public

canonicalCheckedLeanPoleQuotientReturn8889 : CheckedLeanPoleQuotientReturn8889
canonicalCheckedLeanPoleQuotientReturn8889 =
  checked-lean-pole-quotient-return-8889
    "8889"
    true refl
    true refl
    true refl
    false refl
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- Exact target-side attachments.
------------------------------------------------------------------------

record QuantitativeClusterSameObjectAttachment : Set₁ where
  field
    target : Cluster.PoleQuotientClusterMarginTarget
    sameLiteralPoleQuotientTaperAsLeanOwner : Set
    leanTheoremReference : String

open QuantitativeClusterSameObjectAttachment public

record GammaPrecisionRepair : Set₁ where
  field
    target : Gamma.PoleQuotientGammaBudgetTarget
    sameLiteralPoleQuotientTaperAsFinalConsumer : Set
    fitsSharpClusterAccuracyWindow : Set
    producerReference : String

open GammaPrecisionRepair public

record QuarterPeriodOffOrdinateAttachment : Set₁ where
  field
    target : Off.PoleQuotientOffOrdinateBudgetTarget
    crossingCutoffFeedsThisExactOffProducer : Set
    sameLiteralPoleQuotientTaperAsFinalConsumer : Set
    producerReference : String

open QuarterPeriodOffOrdinateAttachment public

------------------------------------------------------------------------
-- Search priority after reconciling the 8889 return with the 8890 regime cut.
------------------------------------------------------------------------

data PoleQuotientLeaf : Set where
  reproveClusterPositivity
  deriveFreshClusterMargin
  attachOwnedQuantitativeClusterMargin
  findAnyGammaUpperBound
  repairGammaToSharpWindow
  proveQuarterPeriodOffOrdinateBound
  rebuildFinalComplementCompiler
  proveStrictCombinedBudget
  : PoleQuotientLeaf

LeafRelevant : PoleQuotientLeaf -> Set
LeafRelevant reproveClusterPositivity = ⊥
LeafRelevant deriveFreshClusterMargin = ⊥
LeafRelevant attachOwnedQuantitativeClusterMargin = ⊤
LeafRelevant findAnyGammaUpperBound = ⊥
LeafRelevant repairGammaToSharpWindow = ⊤
LeafRelevant proveQuarterPeriodOffOrdinateBound = ⊤
LeafRelevant rebuildFinalComplementCompiler = ⊥
LeafRelevant proveStrictCombinedBudget = ⊤

reproveClusterPositivityPruned : LeafRelevant reproveClusterPositivity -> ⊥
reproveClusterPositivityPruned x = x

deriveFreshClusterMarginPruned : LeafRelevant deriveFreshClusterMargin -> ⊥
deriveFreshClusterMarginPruned x = x

findAnyGammaUpperBoundPruned : LeafRelevant findAnyGammaUpperBound -> ⊥
findAnyGammaUpperBoundPruned x = x

rebuildFinalComplementCompilerPruned :
  LeafRelevant rebuildFinalComplementCompiler -> ⊥
rebuildFinalComplementCompilerPruned x = x

currentAgdaCutStillMarksGammaOpen :
  Current.gammaResidualBudgetClosed Current.canonicalPoleQuotientCurrentCut ≡ false
currentAgdaCutStillMarksGammaOpen =
  Current.gammaResidualBudgetClosedIsFalse Current.canonicalPoleQuotientCurrentCut

currentAgdaCutStillMarksClusterSocketOpen :
  Current.quantitativePoleQuotientClusterMarginClosed
    Current.canonicalPoleQuotientCurrentCut ≡ false
currentAgdaCutStillMarksClusterSocketOpen =
  Current.quantitativePoleQuotientClusterMarginClosedIsFalse
    Current.canonicalPoleQuotientCurrentCut

currentAgdaCutStillMarksOffOpen :
  Current.poleQuotientSignedOffOrdinateBoundClosed
    Current.canonicalPoleQuotientCurrentCut ≡ false
currentAgdaCutStillMarksOffOpen =
  Current.poleQuotientSignedOffOrdinateBoundClosedIsFalse
    Current.canonicalPoleQuotientCurrentCut

record PoleQuotientProducerReconciliationBoundary : Set where
  constructor pole-quotient-producer-reconciliation-boundary
  field
    clusterMathematicsNeedsFreshDerivation : Bool
    clusterMathematicsNeedsFreshDerivationIsFalse :
      clusterMathematicsNeedsFreshDerivation ≡ false

    clusterStillNeedsSameObjectAgdaAttachment : Bool
    clusterStillNeedsSameObjectAgdaAttachmentIsTrue :
      clusterStillNeedsSameObjectAgdaAttachment ≡ true

    arbitraryGammaUpperBoundIsAUsefulLeaf : Bool
    arbitraryGammaUpperBoundIsAUsefulLeafIsFalse :
      arbitraryGammaUpperBoundIsAUsefulLeaf ≡ false

    gammaPrecisionRepairIsLive : Bool
    gammaPrecisionRepairIsLiveIsTrue : gammaPrecisionRepairIsLive ≡ true

    quarterPeriodOffOrdinateBoundIsLive : Bool
    quarterPeriodOffOrdinateBoundIsLiveIsTrue :
      quarterPeriodOffOrdinateBoundIsLive ≡ true

    finalComplementCompilerNeedsRebuilding : Bool
    finalComplementCompilerNeedsRebuildingIsFalse :
      finalComplementCompilerNeedsRebuilding ≡ false

    highestAlphaReading : String

canonicalPoleQuotientProducerReconciliationBoundary :
  PoleQuotientProducerReconciliationBoundary
canonicalPoleQuotientProducerReconciliationBoundary =
  pole-quotient-producer-reconciliation-boundary
    false refl
    true refl
    false refl
    true refl
    true refl
    false refl
    "The 8889 checked-Lean return upgrades the pole-quotient cluster leaf from fresh analysis to same-object attachment: a quantitative cluster margin is already owned in Lean, but its proof term is not transported into Agda. The Gamma channel is not 'find any bound' either: a uniform bound exists but is too coarse for the sharp cluster window, so only precision repair on the literal universal pole-quotient taper is live. In parallel, the 8890 quarter-period regime cut leaves the signed off-ordinate bound live only at a crossing cutoff. Once those exact inputs satisfy B_off + B_Gamma < M_cluster, the existing final compiler is reused unchanged."
