{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLevel2LiteralOPECoefficientScaleAttachmentExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCompositeOperatorRGParallelTransportExact as Transport
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YMClayLevel2CompositeOperatorCoefficientWeldExact as D2

------------------------------------------------------------------------
-- LEVEL-2 D2c: LITERAL POSITION-DEPENDENT OPE COEFFICIENT -> RG DEPTH
--
-- The literal Clay API is position-indexed:
--
--   Top.opeCoefficient Y G left right output position
--
-- while the RG recurrence is depth-indexed:
--
--   Nat -> Operator.
--
-- These indices are not definitionally interchangeable.  In particular, it
-- would be wrong to make the literal continuum coefficient a constant Nat-
-- indexed family and demand equality at every RG depth.
--
-- This owner keeps the required physical scale semantics explicit.  A supplied
-- short-distance depth for the literal insertion position must be certified by
-- a physical position/depth relation, and only at that selected depth is the
-- literal Clay coefficient attached to the projected physical RG coordinate.
------------------------------------------------------------------------

record LiteralOPECoefficientScaleAttachment
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    (group : Top.CompactSimpleGroup C)
    {Operator : Set}
    {transport : Transport.CompositeRGParallelTransport Operator}
    (recurrence : D2.SameCompositeOperatorCoefficientRecurrence Operator transport)
    : Set₁ where
  field
    left right output : Top.LocalOperator C
    position : Top.Position C

    projectOPECoefficient : Operator → Top.OPECoefficient C

    shortDistanceDepth : Nat
    DepthRepresentsPositionScale : Top.Position C → Nat → Set
    shortDistanceDepthRepresentsPosition :
      DepthRepresentsPositionScale position shortDistanceDepth

    literalCoefficientIsProjectedRGCoordinate :
      Top.opeCoefficient Y group left right output position
      ≡ projectOPECoefficient
          (D2.physicalOperatorCoefficient recurrence shortDistanceDepth)

open LiteralOPECoefficientScaleAttachment public

projectedAFCoefficientAtLiteralDepth :
  ∀ {C S}
    (Y : Top.LiteralYangMillsConstruction C S)
    (group : Top.CompactSimpleGroup C)
    {Operator}
    {transport : Transport.CompositeRGParallelTransport Operator}
    {recurrence : D2.SameCompositeOperatorCoefficientRecurrence Operator transport} →
  LiteralOPECoefficientScaleAttachment Y group recurrence →
  Top.OPECoefficient C
projectedAFCoefficientAtLiteralDepth Y group {recurrence = recurrence} attachment =
  projectOPECoefficient attachment
    (D2.asymptoticFreedomOperatorCoefficient recurrence
      (shortDistanceDepth attachment))

literalClayCoefficientMatchesProjectedAFAtSelectedDepth :
  ∀ {C S}
    (Y : Top.LiteralYangMillsConstruction C S)
    (group : Top.CompactSimpleGroup C)
    {Operator}
    {transport : Transport.CompositeRGParallelTransport Operator}
    {recurrence : D2.SameCompositeOperatorCoefficientRecurrence Operator transport}
    (attachment : LiteralOPECoefficientScaleAttachment Y group recurrence) →
  Top.opeCoefficient Y group
    (left attachment) (right attachment) (output attachment) (position attachment)
  ≡ projectedAFCoefficientAtLiteralDepth Y group attachment
literalClayCoefficientMatchesProjectedAFAtSelectedDepth
    Y group {recurrence = recurrence} attachment =
  trans
    (literalCoefficientIsProjectedRGCoordinate attachment)
    (cong
      (projectOPECoefficient attachment)
      (D2.operatorCoefficientsEqualAtEveryDepth recurrence
        (shortDistanceDepth attachment)))

------------------------------------------------------------------------
-- Frontier classification.
------------------------------------------------------------------------

literalClayOPECoefficientIsNatIndexed : Bool
literalClayOPECoefficientIsNatIndexed = false

literalClayOPECoefficientIsNatIndexedIsFalse :
  literalClayOPECoefficientIsNatIndexed ≡ false
literalClayOPECoefficientIsNatIndexedIsFalse = refl

positionDepthSemanticsRequired : Bool
positionDepthSemanticsRequired = true

positionDepthSemanticsRequiredIsTrue :
  positionDepthSemanticsRequired ≡ true
positionDepthSemanticsRequiredIsTrue = refl

secondAllDepthCoefficientComparisonRequired : Bool
secondAllDepthCoefficientComparisonRequired = false

secondAllDepthCoefficientComparisonRequiredIsFalse :
  secondAllDepthCoefficientComparisonRequired ≡ false
secondAllDepthCoefficientComparisonRequiredIsFalse = refl

scaleAttachmentCompilerLevel : ProofLevel
scaleAttachmentCompilerLevel = machineChecked

physicalPositionDepthAttachmentLevel : ProofLevel
physicalPositionDepthAttachmentLevel = conditional

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
