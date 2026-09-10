{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLangevinAnchoredInfluenceRound268Exact where

------------------------------------------------------------------------
-- ROUND268 / R260 ANCHOR -> R266 TYPED LANGEVIN INFLUENCE
--
-- R260 separates a marked CMP comparison from a reference Hessian anchor before
-- taking an absolute value.  R266 requires the rational influence matrix to
-- majorize the ACTUAL typed Langevin action-Hessian entry.
--
-- Choose each influence entry to be R260's rational `absoluteDebt`.  Then the
-- real absolute-entry bound and nonnegativity are theorem output.  Remaining
-- spatial source work is only the same-object comparison/reference realization
-- and one weighted row bound for those rational debts.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Foundations.RealAnalysisAxioms using (absℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.CompactLieLangevinSkewConnectionCancellationExact as Langevin
import DASHI.Physics.YangMills.BalabanA2RationalShellBudgetToRealRound108Exact as Embed
import DASHI.Physics.YangMills.BalabanCMP116AnchoredHessianMajorantRound260Exact as Anchor
import DASHI.Physics.YangMills.BalabanCMP109LangevinTypedSecondVariationRound267Exact as CMP
import DASHI.Physics.YangMills.BalabanLangevinHessianBidirectionalWeldRound262Exact as Bidi
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanThreeHalvesMetricWeightExact as Metric

record LiteralAnchoredLangevinInfluence
    (Scale Volume Root : Set) : Set₁ where
  field
    cmpLangevin : CMP.LiteralCMP109LangevinSecondVariationWeld
    shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root
    scale : Scale
    volume : Volume
    root : Root

    embedding : Embed.OrderedRationalRealRingEmbedding

    sites : List (Langevin.Site (CMP.frame cmpLangevin))
    metric : Metric.NatMetricTriangle (Langevin.Site (CMP.frame cmpLangevin))

    anchoredEntry :
      Langevin.Site (CMP.frame cmpLangevin) →
      Langevin.Site (CMP.frame cmpLangevin) →
      Anchor.AnchoredRealHessianMajorant embedding

    selectedIsTypedCMP109Hessian : ∀ x y →
      Anchor.selected (anchoredEntry x y)
      ≡ Langevin.actionHessianEntry
          (CMP.asTypedLangevinCommutator cmpLangevin) x y

    weightedAnchoredDebtBelowSharedHessian : ∀ x →
      Sums.sumRational sites
        (λ y → Metric.metricWeight metric x y
          * Anchor.absoluteDebt (anchoredEntry x y))
      ≤ Shared.hessianAnalyticConstant shared

    curvatureDebt : Nat → ℚ
    curvatureDebtNonnegative : ∀ n → 0ℚ ≤ curvatureDebt n
    sameHessianIsHeatDoobNegativeCurvatureShell : ∀ n →
      curvatureDebt n
      ≡ Shared.hessianInfluenceShell shared scale volume root n

open LiteralAnchoredLangevinInfluence public

anchoredInfluence :
  ∀ {Scale Volume Root}
    (dataSet : LiteralAnchoredLangevinInfluence Scale Volume Root) →
  Langevin.Site (CMP.frame (cmpLangevin dataSet)) →
  Langevin.Site (CMP.frame (cmpLangevin dataSet)) → ℚ
anchoredInfluence dataSet x y =
  Anchor.absoluteDebt (anchoredEntry dataSet x y)

anchoredInfluenceNonnegative :
  ∀ {Scale Volume Root}
    (dataSet : LiteralAnchoredLangevinInfluence Scale Volume Root) →
  ∀ x y → 0ℚ ≤ anchoredInfluence dataSet x y
anchoredInfluenceNonnegative dataSet x y =
  Anchor.absoluteDebtNonnegative (anchoredEntry dataSet x y)

typedActionHessianAbsBelowAnchoredInfluence :
  ∀ {Scale Volume Root}
    (dataSet : LiteralAnchoredLangevinInfluence Scale Volume Root) →
  ∀ x y →
  absℝ
    (Langevin.actionHessianEntry
      (CMP.asTypedLangevinCommutator (cmpLangevin dataSet)) x y)
  ≤ℝ Embed.embed (embedding dataSet) (anchoredInfluence dataSet x y)
typedActionHessianAbsBelowAnchoredInfluence dataSet x y =
  subst
    (λ value →
      absℝ value
      ≤ℝ Embed.embed (embedding dataSet) (anchoredInfluence dataSet x y))
    (selectedIsTypedCMP109Hessian dataSet x y)
    (Anchor.selectedAbsMajorized (anchoredEntry dataSet x y))

asBidirectionalWeld :
  ∀ {Scale Volume Root} →
  LiteralAnchoredLangevinInfluence Scale Volume Root →
  Bidi.LiteralLangevinHessianBidirectionalWeld Scale Volume Root
asBidirectionalWeld dataSet = record
  { Bidi.LiteralLangevinHessianBidirectionalWeld.shared = shared dataSet
  ; Bidi.LiteralLangevinHessianBidirectionalWeld.scale = scale dataSet
  ; Bidi.LiteralLangevinHessianBidirectionalWeld.volume = volume dataSet
  ; Bidi.LiteralLangevinHessianBidirectionalWeld.root = root dataSet
  ; Bidi.LiteralLangevinHessianBidirectionalWeld.langevin =
      CMP.asTypedLangevinCommutator (cmpLangevin dataSet)
  ; Bidi.LiteralLangevinHessianBidirectionalWeld.sites = sites dataSet
  ; Bidi.LiteralLangevinHessianBidirectionalWeld.metric = metric dataSet
  ; Bidi.LiteralLangevinHessianBidirectionalWeld.influence =
      anchoredInfluence dataSet
  ; Bidi.LiteralLangevinHessianBidirectionalWeld.influenceNonnegative =
      anchoredInfluenceNonnegative dataSet
  ; Bidi.LiteralLangevinHessianBidirectionalWeld.embedding = embedding dataSet
  ; Bidi.LiteralLangevinHessianBidirectionalWeld.actionHessianAbsBelowInfluence =
      typedActionHessianAbsBelowAnchoredInfluence dataSet
  ; Bidi.LiteralLangevinHessianBidirectionalWeld.symmetricLangevinWeightedRowBelowSharedHessian =
      weightedAnchoredDebtBelowSharedHessian dataSet
  ; Bidi.LiteralLangevinHessianBidirectionalWeld.curvatureDebt =
      curvatureDebt dataSet
  ; Bidi.LiteralLangevinHessianBidirectionalWeld.curvatureDebtNonnegative =
      curvatureDebtNonnegative dataSet
  ; Bidi.LiteralLangevinHessianBidirectionalWeld.sameHessianIsHeatDoobNegativeCurvatureShell =
      sameHessianIsHeatDoobNegativeCurvatureShell dataSet
  }

round268AnchoredEntryToInfluenceCompilerLevel : ProofLevel
round268AnchoredEntryToInfluenceCompilerLevel = machineChecked

round268BidirectionalConsumerCompilerLevel : ProofLevel
round268BidirectionalConsumerCompilerLevel = Bidi.round262BidiCompilerLevel

round268SameObjectAnchoredSourceLevel : ProofLevel
round268SameObjectAnchoredSourceLevel = conditional

round268WeightedAnchoredDebtRowLevel : ProofLevel
round268WeightedAnchoredDebtRowLevel = conditional
