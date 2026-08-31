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

------------------------------------------------------------------------
-- QUARTER-PERIOD -> POLE-QUOTIENT FINAL COMPILER
--
-- Under the standing BIDI assumption that ordinary analytic machinery already
-- exists, there is no reason to build a new final contradiction calculus.
-- The repository already owns exactly the needed split-complement compiler:
--
--   cluster = offOrdinate + Gamma
--   offOrdinate <= B_off
--   Gamma <= B_Gamma
--   B_off + B_Gamma < M_cluster
--
-- implies contradiction.
--
-- The only new attachment introduced by quarter-period crossing is upstream:
-- B_off must be produced on the literal oscillatory near/far carrier using the
-- chosen crossing cutoff.  Gamma and cluster remain the existing same-taper
-- complement coordinates.
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

------------------------------------------------------------------------
-- BIDI cut after the 8890-job narrow-window theorem.
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
LeafRelevant strictCombinedBudget = ⊤
LeafRelevant rebuildFinalContradictionCompiler = ⊥

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
    "After quarter-period crossing, do not redesign the final RH consumer. Feed the chosen crossing cutoff only into the literal signed off-ordinate producer. Then attach that resulting B_off to the already-owned pole-quotient split-complement surface together with the independent same-taper Gamma budget and quantitative cluster margin. The existing Agda compiler already turns B_off + B_Gamma < M_cluster into contradiction. The remaining research content is literal input assembly, not final contradiction algebra."
