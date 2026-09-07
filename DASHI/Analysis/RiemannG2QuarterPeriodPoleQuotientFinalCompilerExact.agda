module DASHI.Analysis.RiemannG2QuarterPeriodPoleQuotientFinalCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannG2QuarterPeriodScalingPropagationExact as Scaling
import DASHI.Analysis.RiemannG2CutoffComplementCoordinateSeparationExact as Separation
import DASHI.Analysis.RiemannAristotlePoleQuotientSplitComplementBudgetExact as Split
import DASHI.Analysis.RiemannAristotlePoleQuotientComplementMarginCompilerExact as Complement
import DASHI.Analysis.RiemannAristotlePoleQuotientBidiMeetingExact as Meeting
import DASHI.Analysis.RiemannG2PoleQuotientChannelAllowanceExact as Allowance

------------------------------------------------------------------------
-- QUARTER-PERIOD -> POLE-QUOTIENT FINAL COMPILER
--
-- Under the standing BIDI assumption that ordinary analytic machinery already
-- exists, there is no reason to build a new final contradiction calculus.
-- The repository already owns exactly the needed split-complement compiler.
--
-- The only cutoff-dependent attachment introduced by quarter-period crossing is
-- upstream: B_off must be produced on the literal oscillatory near/far carrier
-- using the chosen crossing cutoff. Gamma and cluster remain taper-only.
--
-- Newer allowance machinery also removes `B_off + B_Gamma < M_cluster` as an
-- independent research theorem: producer payments establish B_off <= A_off and
-- B_Gamma <= A_Gamma, while the final consumer supplies
-- A_off + A_Gamma < M_cluster; composition is compiler output.
------------------------------------------------------------------------

record QuarterPeriodOffBudgetAttachment
    (W : Scaling.LiteralHighOrdinateWidthLaw) : Set₁ where
  field
    scalingAdmission : Scaling.QuarterPeriodScalingAdmission W
    sameLiteralPoleQuotientTaperUsed : Set
    chosenCrossingCutoffFeedsOffOrdinateProducer : Set
    offBudgetReference : String

open QuarterPeriodOffBudgetAttachment public

record QuarterPeriodPoleQuotientRun : Set₁ where
  field
    widthLaw : Scaling.LiteralHighOrdinateWidthLaw
    offAttachment : QuarterPeriodOffBudgetAttachment widthLaw

    surface : Split.OrderedAdditiveComplementSurface
    splitMargin : Split.SplitPoleQuotientComplementMargin surface

    sameLiteralOffBudgetAsQuarterPeriodProducer : Set
    sameLiteralGammaAsPoleQuotientConsumer : Set
    sameLiteralClusterAsPoleQuotientConsumer : Set
    sameLiteralTaperAcrossAllThreeChannels : Set

open QuarterPeriodPoleQuotientRun public

quarterPeriodPoleQuotientContradiction :
  (R : QuarterPeriodPoleQuotientRun) -> ⊥
quarterPeriodPoleQuotientContradiction R =
  Split.splitPoleQuotientComplementContradiction
    (surface R)
    (splitMargin R)

existingComplementCompilerAlreadyClosed :
  Complement.complementMarginCompilerClosedInAgda
    Complement.canonicalPoleQuotientComplementMarginBoundary ≡ true
existingComplementCompilerAlreadyClosed =
  Complement.complementMarginCompilerClosedInAgdaIsTrue
    Complement.canonicalPoleQuotientComplementMarginBoundary

existingPoleQuotientBidiCompilerAlreadyClosed :
  Meeting.complementContradictionCompilerClosed
    Meeting.canonicalPoleQuotientBidiMeetingBoundary ≡ true
existingPoleQuotientBidiCompilerAlreadyClosed = refl

allowanceCompositionAlreadyClosed :
  Allowance.PoleQuotientChannelAllowanceBoundary.allowanceCompilerClosed
    Allowance.canonicalPoleQuotientChannelAllowanceBoundary ≡ true
allowanceCompositionAlreadyClosed = refl

------------------------------------------------------------------------
-- Historical BIDI cut, reconciled with the final allowance architecture.
------------------------------------------------------------------------

data LiveLeaf : Set where
  literalWidthLaw
  quarterPeriodOffBudget
  sameTaperGammaBudget
  quantitativeClusterMargin
  strictCombinedBudget
  rebuildFinalContradictionCompiler
  : LiveLeaf

LeafRelevant : LiveLeaf -> Set
LeafRelevant literalWidthLaw = ⊤
LeafRelevant quarterPeriodOffBudget = ⊤
LeafRelevant sameTaperGammaBudget = ⊤
LeafRelevant quantitativeClusterMargin = ⊤
LeafRelevant strictCombinedBudget = ⊥
LeafRelevant rebuildFinalContradictionCompiler = ⊥

strictCombinedBudgetRebuildPruned :
  LeafRelevant strictCombinedBudget -> ⊥
strictCombinedBudgetRebuildPruned x = x

finalCompilerRebuildPruned :
  LeafRelevant rebuildFinalContradictionCompiler -> ⊥
finalCompilerRebuildPruned x = x

record QuarterPeriodPoleQuotientBoundary : Set where
  constructor quarter-period-pole-quotient-boundary
  field
    quarterPeriodCrossingChangesFinalCompilerShape : Bool
    quarterPeriodCrossingChangesFinalCompilerShapeIsFalse :
      quarterPeriodCrossingChangesFinalCompilerShape ≡ false

    cutoffGrowthMustEnterGammaConsumerDirectly : Bool
    cutoffGrowthMustEnterGammaConsumerDirectlyIsFalse :
      cutoffGrowthMustEnterGammaConsumerDirectly ≡ false

    cutoffGrowthMustEnterClusterConsumerDirectly : Bool
    cutoffGrowthMustEnterClusterConsumerDirectlyIsFalse :
      cutoffGrowthMustEnterClusterConsumerDirectly ≡ false

    crossingCutoffMustFeedLiteralOffOrdinateProducer : Bool
    crossingCutoffMustFeedLiteralOffOrdinateProducerIsTrue :
      crossingCutoffMustFeedLiteralOffOrdinateProducer ≡ true

    existingSplitComplementCompilerIsReusable : Bool
    existingSplitComplementCompilerIsReusableIsTrue :
      existingSplitComplementCompilerIsReusable ≡ true

    remainingPaymentIsOnlyLiteralInputAssembly : Bool
    remainingPaymentIsOnlyLiteralInputAssemblyIsTrue :
      remainingPaymentIsOnlyLiteralInputAssembly ≡ true

    highestAlphaReading : String

canonicalQuarterPeriodPoleQuotientBoundary : QuarterPeriodPoleQuotientBoundary
canonicalQuarterPeriodPoleQuotientBoundary =
  quarter-period-pole-quotient-boundary
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
    "After quarter-period crossing, feed the chosen cutoff only into the literal signed Off producer. Gamma and cluster remain same-taper, cutoff-free coordinates. Do not schedule a fresh proof of B_off + B_Gamma < M_cluster: the final allowance architecture derives it from B_off <= A_off, B_Gamma <= A_Gamma and A_off + A_Gamma < M_cluster. The existing split-complement contradiction remains reusable. Remaining research is literal Off/Gamma producer payment plus same-object cluster attachment, not final contradiction algebra."
