{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLevel2R129CompositeTailAttachmentExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ)

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
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YMClayLevel2SameFamilyStressRecoveryExact as Recovery
import DASHI.Physics.YangMills.YMClayLevel2CompositeTailWeldExact as D1

------------------------------------------------------------------------
-- R129-SPECIALIZED LEVEL-2 D1 ATTACHMENT
--
-- The generic D1 weld allows any SameFamilyMarkedSourceData.  The literal
-- Level-2 route is sharper: R129's selected stress completion already contains
-- the composite marked-source data from the SAME completed state.
--
-- Therefore the only physical D1 payload remaining after R129 is:
--
--   the literal OPE product remainder evaluated on that already-selected
--   completed composite projection
--
--       =
--
--   the selected SharedMarkedAnalyticShell compositeInsertionTail.
--
-- No independent composite completion/carrier is accepted here.
------------------------------------------------------------------------

record R129CompositeTailAttachment
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

  private
    selected = R120.coordinate (R123.stressLane stressLane)
    completion = R114.asMarkedCompletion selected (R114.coordinate selected)
    compositeData = Recovery.r129ExportsCompositeMarkedSourceData export

  field
    literalProductRemainder :
      R109.Composite completion → Nat → ℚ

    remaining : Nat → Nat

    literalProductRemainderIsSelectedR129CompositeTail :
      ∀ depth →
      literalProductRemainder
        (Marked.compositeProjection compositeData
          (Marked.completedState compositeData))
        depth
      ≡ Shared.compositeInsertionTail
          shared scale volume root depth (remaining depth)

open R129CompositeTailAttachment public

asCompositeProductTailWeld :
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
  R129CompositeTailAttachment export shared scale volume root →
  D1.CompositeProductTailWeld
    (Recovery.r129ExportsCompositeMarkedSourceData export)
    shared scale volume root
asCompositeProductTailWeld attachment = record
  { D1.CompositeProductTailWeld.literalProductRemainder =
      literalProductRemainder attachment
  ; D1.CompositeProductTailWeld.remaining =
      remaining attachment
  ; D1.CompositeProductTailWeld.literalProductRemainderIsCompositeTail =
      literalProductRemainderIsSelectedR129CompositeTail attachment
  }

r129AttachmentBuildsLiteralDyadicOPERemainder :
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
  (attachment : R129CompositeTailAttachment export shared scale volume root) →
  DASHI.Physics.YangMills.YangMillsContinuumLocalOperatorOPEStressTensorExact.DyadicOPERemainderMajorant
r129AttachmentBuildsLiteralDyadicOPERemainder attachment =
  D1.literalCompletedCompositeOPERemainderMajorant
    (asCompositeProductTailWeld attachment)

------------------------------------------------------------------------
-- Frontier classification.
------------------------------------------------------------------------

independentCompositeMarkedSourceAfterR129 : Bool
independentCompositeMarkedSourceAfterR129 = false

independentCompositeMarkedSourceAfterR129IsFalse :
  independentCompositeMarkedSourceAfterR129 ≡ false
independentCompositeMarkedSourceAfterR129IsFalse = refl

independentCompositeCompletionAfterR129 : Bool
independentCompositeCompletionAfterR129 = false

independentCompositeCompletionAfterR129IsFalse :
  independentCompositeCompletionAfterR129 ≡ false
independentCompositeCompletionAfterR129IsFalse = refl

d1PhysicalResidueIsSingleTailEquality : Bool
d1PhysicalResidueIsSingleTailEquality = true

d1PhysicalResidueIsSingleTailEqualityIsTrue :
  d1PhysicalResidueIsSingleTailEquality ≡ true
d1PhysicalResidueIsSingleTailEqualityIsTrue = refl

r129CompositeTailAdapterCompilerLevel : ProofLevel
r129CompositeTailAdapterCompilerLevel = machineChecked

physicalD1R129TailEqualityLevel : ProofLevel
physicalD1R129TailEqualityLevel = conditional

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
