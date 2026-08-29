module DASHI.Physics.Foundations.BalabanCommonActionVariationValidation where

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.CommonEffectiveActionVariationExact as Variation
import DASHI.Physics.Foundations.BalabanCommonActionVariationFrontierExact as BalabanVariation
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4BetaSplitPositivityExact as Split
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity

balabanDensityVariationProducesQFTIdentification :
  ∀ {U : Weld.UnifiedCandidate}
    (variation : Variation.CommonEffectiveActionVariation U)
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {split : Split.FiniteLatticeBetaSplit trajectory}
    (inputs : BetaDensity.BetaDrivenCompleteDensityInputs {trajectory} {split}) →
  BalabanVariation.BalabanQFTVariationReceipt variation inputs →
  Variation.QFTVariationIdentification variation
balabanDensityVariationProducesQFTIdentification =
  BalabanVariation.balabanReceiptBuildsQFTVariationIdentification
