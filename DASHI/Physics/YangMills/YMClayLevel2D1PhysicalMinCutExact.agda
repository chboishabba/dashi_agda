{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLevel2D1PhysicalMinCutExact where

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
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YMClayLevel2R129CompositeTailAttachmentExact as Compat
import DASHI.Physics.YangMills.YangMillsContinuumLocalOperatorOPEStressTensorExact as Local

------------------------------------------------------------------------
-- LEVEL-2 D1 LEAST-PRIVILEGE PHYSICAL CUT
--
-- R129 already fixes the completed same-family composite carrier.  The older
-- compatibility record introduced an auxiliary
--
--   productRemainder : Composite -> Nat -> Rational
--
-- and required both
--
--   productRemainder(completedComposite,n) = Top.opeRemainder(...)
--   productRemainder(completedComposite,n) = compositeInsertionTail(...)
--
-- Because productRemainder itself is freely supplied, that intermediate
-- function adds no proof strength.  The physical content is exactly the direct
-- same-object equality below.
--
-- This owner keeps the R129 export in the type so the equality cannot float to
-- an unrelated continuum family, but it introduces no second remainder carrier.
------------------------------------------------------------------------

record D1PhysicalMinCut
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    {Scale Volume Root : Set}
    {activity : Chain.SubstitutedActivitySecondVariation}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation}
    (export : R129.BalabanSectorQFTRecoveryExport stressLane)
    (shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root)
    (scale : Scale) (volume : Volume) (root : Root)
    : Set₁ where
  field
    left right : Top.LocalOperator C
    position : Top.Position C
    remaining : Nat → Nat

    literalClayOPERemainderIsSelectedR129CompositeTail :
      ∀ depth →
      Top.opeRemainder Y group left right position depth
      ≡ Shared.compositeInsertionTail
          shared scale volume root depth (remaining depth)

open D1PhysicalMinCut public

asCompatibilityAttachment :
  ∀ {trajectory split inputs C S Y group Scale Volume Root activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation}
    {export : R129.BalabanSectorQFTRecoveryExport stressLane}
    {shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root}
    {scale : Scale} {volume : Volume} {root : Root} →
  D1PhysicalMinCut export shared scale volume root →
  Compat.R129CompositeTailAttachment export shared scale volume root
asCompatibilityAttachment {Y = Y} {group = group} cut = record
  { Compat.R129CompositeTailAttachment.left = left cut
  ; Compat.R129CompositeTailAttachment.right = right cut
  ; Compat.R129CompositeTailAttachment.position = position cut
  ; Compat.R129CompositeTailAttachment.productRemainder =
      λ _ depth → Top.opeRemainder Y group
        (left cut) (right cut) (position cut) depth
  ; Compat.R129CompositeTailAttachment.remaining = remaining cut
  ; Compat.R129CompositeTailAttachment.completedCompositeProductRemainderIsLiteralClay =
      λ depth → refl
  ; Compat.R129CompositeTailAttachment.completedCompositeProductRemainderIsSelectedTail =
      literalClayOPERemainderIsSelectedR129CompositeTail cut
  }

d1BuildsLiteralDyadicOPERemainder :
  ∀ {trajectory split inputs C S Y group Scale Volume Root activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation}
    {export : R129.BalabanSectorQFTRecoveryExport stressLane}
    {shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root}
    {scale : Scale} {volume : Volume} {root : Root} →
  D1PhysicalMinCut export shared scale volume root →
  Local.DyadicOPERemainderMajorant
d1BuildsLiteralDyadicOPERemainder cut =
  Compat.r129AttachmentBuildsLiteralDyadicOPERemainder
    (asCompatibilityAttachment cut)

------------------------------------------------------------------------
-- Anti-double-counting / WrongType classification.
------------------------------------------------------------------------

auxiliaryProductRemainderFunctionRequiredByD1 : Bool
auxiliaryProductRemainderFunctionRequiredByD1 = false

auxiliaryProductRemainderFunctionRequiredByD1IsFalse :
  auxiliaryProductRemainderFunctionRequiredByD1 ≡ false
auxiliaryProductRemainderFunctionRequiredByD1IsFalse = refl

independentCompositeCarrierRequiredAfterR129 : Bool
independentCompositeCarrierRequiredAfterR129 = false

independentCompositeCarrierRequiredAfterR129IsFalse :
  independentCompositeCarrierRequiredAfterR129 ≡ false
independentCompositeCarrierRequiredAfterR129IsFalse = refl

newD1AnalyticInequalityRequired : Bool
newD1AnalyticInequalityRequired = false

newD1AnalyticInequalityRequiredIsFalse :
  newD1AnalyticInequalityRequired ≡ false
newD1AnalyticInequalityRequiredIsFalse = refl

directSameObjectRemainderEqualityStillPhysical : Bool
directSameObjectRemainderEqualityStillPhysical = true

directSameObjectRemainderEqualityStillPhysicalIsTrue :
  directSameObjectRemainderEqualityStillPhysical ≡ true
directSameObjectRemainderEqualityStillPhysicalIsTrue = refl

d1CompatibilityCompilerLevel : ProofLevel
d1CompatibilityCompilerLevel = machineChecked

physicalD1DirectRemainderEqualityLevel : ProofLevel
physicalD1DirectRemainderEqualityLevel = conditional

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
