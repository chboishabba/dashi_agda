{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLevel2R129LiteralOPECoefficientWeldExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as R123
import DASHI.Physics.YangMills.BalabanSectorQFTRecoveryExportRound129Exact as R129
import DASHI.Physics.YangMills.BalabanCanonicalMetricStressLaneRound120Exact as R120
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanMarkedSourceNuclearCompositeFieldExact as Marked
import DASHI.Physics.YangMills.BalabanCompositeOperatorRGParallelTransportExact as Transport
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YMClayLevel2SameFamilyStressRecoveryExact as Recovery
import DASHI.Physics.YangMills.YMClayLevel2CompositeOperatorCoefficientWeldExact as D2
import DASHI.Physics.YangMills.YMClayLevel2LiteralOPECoefficientScaleAttachmentExact as D2c
import DASHI.Physics.YangMills.YMClayLevel2R129CompositeOperatorAttachmentExact as SameFamily

------------------------------------------------------------------------
-- LEVEL-2 D2: FINAL R129/LITERAL SAME-OBJECT WELD
--
-- D2c attaches the literal position-dependent Clay coefficient to the physical
-- operator coefficient at one certified short-distance RG depth.
--
-- The R129 same-family firewall separately proves that the physical operator
-- coefficient at THAT SAME depth is the operator extracted from the actual
-- R129 completed composite.
--
-- Combining them removes the last parallel-composite loophole:
--
--   literal Clay OPE coefficient
--     = projection(physical operator coefficient at selected depth)
--     = projection(operator of R129 completed composite).
------------------------------------------------------------------------

record R129LiteralOPECoefficientWeld
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    (group : Top.CompactSimpleGroup C)
    {Scale Volume : Set}
    {activity : Chain.SubstitutedActivitySecondVariation}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation}
    (export : R129.BalabanSectorQFTRecoveryExport stressLane)
    {Operator : Set}
    {transport : Transport.CompositeRGParallelTransport Operator}
    (recurrence : D2.SameCompositeOperatorCoefficientRecurrence Operator transport)
    (literal : D2c.LiteralOPECoefficientScaleAttachment Y group recurrence)
    : Set₁ where
  field
    sameFamilyOperator :
      SameFamily.R129CompositeOperatorAttachment
        export recurrence (D2c.shortDistanceDepth literal)

open R129LiteralOPECoefficientWeld public

literalClayCoefficientIsProjectionOfR129CompletedComposite :
  ∀ {trajectory split inputs C S}
    (Y : Top.LiteralYangMillsConstruction C S)
    (group : Top.CompactSimpleGroup C)
    {Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation}
    {export : R129.BalabanSectorQFTRecoveryExport stressLane}
    {Operator}
    {transport : Transport.CompositeRGParallelTransport Operator}
    {recurrence : D2.SameCompositeOperatorCoefficientRecurrence Operator transport}
    {literal : D2c.LiteralOPECoefficientScaleAttachment Y group recurrence}
    (weld : R129LiteralOPECoefficientWeld Y group export recurrence literal) →
  let selected = R120.coordinate (R123.stressLane stressLane)
      completion = R114.asMarkedCompletion selected (R114.coordinate selected)
      compositeData = Recovery.r129ExportsCompositeMarkedSourceData export
      completedComposite =
        Marked.compositeProjection compositeData
          (Marked.completedState compositeData)
      sameFamily = sameFamilyOperator weld
  in
  Top.opeCoefficient Y group
      (D2c.left literal) (D2c.right literal)
      (D2c.output literal) (D2c.position literal)
  ≡
  D2c.projectOPECoefficient literal
    (SameFamily.operatorOfCompletedComposite sameFamily completedComposite)
literalClayCoefficientIsProjectionOfR129CompletedComposite
    Y group {recurrence = recurrence} {literal = literal} weld =
  trans
    (D2c.literalCoefficientIsProjectedRGCoordinate literal)
    (cong
      (D2c.projectOPECoefficient literal)
      (SameFamily.selectedOperatorIsCompletedR129Composite
        (sameFamilyOperator weld)))

literalClayCoefficientMatchesProjectedAFAtSameSelectedDepth :
  ∀ {trajectory split inputs C S}
    (Y : Top.LiteralYangMillsConstruction C S)
    (group : Top.CompactSimpleGroup C)
    {Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation}
    {export : R129.BalabanSectorQFTRecoveryExport stressLane}
    {Operator}
    {transport : Transport.CompositeRGParallelTransport Operator}
    {recurrence : D2.SameCompositeOperatorCoefficientRecurrence Operator transport}
    {literal : D2c.LiteralOPECoefficientScaleAttachment Y group recurrence} →
  R129LiteralOPECoefficientWeld Y group export recurrence literal →
  Top.opeCoefficient Y group
      (D2c.left literal) (D2c.right literal)
      (D2c.output literal) (D2c.position literal)
  ≡
  D2c.projectedAFCoefficientAtLiteralDepth Y group literal
literalClayCoefficientMatchesProjectedAFAtSameSelectedDepth
    Y group {literal = literal} weld =
  D2c.literalClayCoefficientMatchesProjectedAFAtSelectedDepth
    Y group literal

------------------------------------------------------------------------
-- Frontier classification.
------------------------------------------------------------------------

parallelCompositeOperatorTheoryAllowedByD2 : Bool
parallelCompositeOperatorTheoryAllowedByD2 = false

parallelCompositeOperatorTheoryAllowedByD2IsFalse :
  parallelCompositeOperatorTheoryAllowedByD2 ≡ false
parallelCompositeOperatorTheoryAllowedByD2IsFalse = refl

r129SameFamilyOperatorAttachmentStillPhysical : Bool
r129SameFamilyOperatorAttachmentStillPhysical = true

r129SameFamilyOperatorAttachmentStillPhysicalIsTrue :
  r129SameFamilyOperatorAttachmentStillPhysical ≡ true
r129SameFamilyOperatorAttachmentStillPhysicalIsTrue = refl

r129LiteralCoefficientWeldCompilerLevel : ProofLevel
r129LiteralCoefficientWeldCompilerLevel = machineChecked

physicalR129LiteralCoefficientWeldLevel : ProofLevel
physicalR129LiteralCoefficientWeldLevel = conditional

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
