{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLevel2R129CompositeOperatorAttachmentExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

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

------------------------------------------------------------------------
-- LEVEL-2 D2 SAME-FAMILY FIREWALL
--
-- Round66 supplies the correct composite-operator RG transport ABI, but the repo
-- currently has no inhabitant connecting that transport to the R129 completed
-- composite family.  This record names exactly that missing same-object seam.
--
-- A valid D2 transport must not merely be any CompositeRGParallelTransport.  Its
-- physical coefficient trajectory must be certified as the operator-mixing view
-- of the SAME R129 composite RG family, and the selected short-distance operator
-- coordinate must agree with the operator extracted from the actual R129
-- completed composite.
------------------------------------------------------------------------

record R129CompositeOperatorAttachment
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
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
    (selectedDepth : Nat)
    : Set₁ where

  private
    selected = R120.coordinate (R123.stressLane stressLane)
    completion = R114.asMarkedCompletion selected (R114.coordinate selected)
    compositeData = Recovery.r129ExportsCompositeMarkedSourceData export
    completedComposite =
      Marked.compositeProjection compositeData
        (Marked.completedState compositeData)

  field
    operatorOfCompletedComposite :
      R109.Composite completion → Operator

    PhysicalOperatorTrajectoryIsR129CompositeRG : Set
    physicalOperatorTrajectoryIsR129CompositeRG :
      PhysicalOperatorTrajectoryIsR129CompositeRG

    selectedOperatorIsCompletedR129Composite :
      D2.physicalOperatorCoefficient recurrence selectedDepth
      ≡ operatorOfCompletedComposite completedComposite

open R129CompositeOperatorAttachment public

------------------------------------------------------------------------
-- Frontier classification.
------------------------------------------------------------------------

arbitraryCompositeOperatorTransportSufficesForLevel2D2 : Bool
arbitraryCompositeOperatorTransportSufficesForLevel2D2 = false

arbitraryCompositeOperatorTransportSufficesForLevel2D2IsFalse :
  arbitraryCompositeOperatorTransportSufficesForLevel2D2 ≡ false
arbitraryCompositeOperatorTransportSufficesForLevel2D2IsFalse = refl

r129CompositeOperatorSameFamilyAttachmentStillPhysical : Bool
r129CompositeOperatorSameFamilyAttachmentStillPhysical = true

r129CompositeOperatorSameFamilyAttachmentStillPhysicalIsTrue :
  r129CompositeOperatorSameFamilyAttachmentStillPhysical ≡ true
r129CompositeOperatorSameFamilyAttachmentStillPhysicalIsTrue = refl

physicalR129CompositeOperatorAttachmentLevel : ProofLevel
physicalR129CompositeOperatorAttachmentLevel = conditional

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
