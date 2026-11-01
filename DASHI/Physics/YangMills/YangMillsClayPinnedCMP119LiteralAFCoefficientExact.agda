{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119LiteralAFCoefficientExact where

------------------------------------------------------------------------
-- C / LITERAL CLAY OPE COEFFICIENT -> AF COEFFICIENT ON THE SAME RG COORDINATE
--
-- The all-depth equality is already compiler-owned.  This owner quantifies the
-- existing Level-2 scale attachment over every literal OPE insertion tuple and
-- exposes the exact coefficient family consumed by the pinned C presentation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (_×_; _,_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.BalabanCompositeOperatorRGParallelTransportExact as Transport
import DASHI.Physics.YangMills.YMClayLevel2CompositeOperatorCoefficientWeldExact as D2
import DASHI.Physics.YangMills.YMClayLevel2LiteralOPECoefficientScaleAttachmentExact as D2c

record LiteralPinnedAFCoefficientFamily
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    (group : Top.CompactSimpleGroup C)
    (Operator : Set)
    (transport : Transport.CompositeRGParallelTransport Operator)
    : Set₁ where
  field
    recurrence :
      D2.SameCompositeOperatorCoefficientRecurrence Operator transport

    attachment :
      ∀ left right output position →
      D2c.LiteralOPECoefficientScaleAttachment
        Y group recurrence

    attachmentHasRequestedCoordinates :
      ∀ left right output position →
      let selected = attachment left right output position
      in
      D2c.left selected ≡ left
      × D2c.right selected ≡ right
      × D2c.output selected ≡ output
      × D2c.position selected ≡ position

open LiteralPinnedAFCoefficientFamily public

asymptoticallyFreeCoefficient :
  ∀ {C S}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    {Operator}
    {transport : Transport.CompositeRGParallelTransport Operator} →
  LiteralPinnedAFCoefficientFamily Y group Operator transport →
  Top.LocalOperator C →
  Top.LocalOperator C →
  Top.LocalOperator C →
  Top.Position C →
  Top.OPECoefficient C
asymptoticallyFreeCoefficient {Y = Y} {group = group} family left right output position =
  D2c.projectedAFCoefficientAtLiteralDepth
    Y group (attachment family left right output position)

literalCoefficientMatchesAF :
  ∀ {C S}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    {Operator}
    {transport : Transport.CompositeRGParallelTransport Operator}
    (family : LiteralPinnedAFCoefficientFamily Y group Operator transport) →
  ∀ left right output position →
  Top.opeCoefficient Y group left right output position
  ≡ asymptoticallyFreeCoefficient family left right output position
literalCoefficientMatchesAF {Y = Y} {group = group}
    family left right output position
  with attachmentHasRequestedCoordinates family left right output position
... | leftEq , (rightEq , (outputEq , positionEq))
  rewrite leftEq | rightEq | outputEq | positionEq =
  D2c.literalClayCoefficientMatchesProjectedAFAtSelectedDepth
    Y group (attachment family left right output position)

literalPinnedAFCoefficientCompilerLevel : ProofLevel
literalPinnedAFCoefficientCompilerLevel = machineChecked

-- Remaining AF physics after this universalization:
-- * instantiate the same composite-operator RG recurrence;
-- * attach each literal short-distance position to its physical RG depth and
--   the selected same-family coefficient coordinate.
-- No second all-depth coefficient comparison remains.
literalPinnedAFCoefficientCoordinateAttachmentLevel : ProofLevel
literalPinnedAFCoefficientCoordinateAttachmentLevel = conditional
