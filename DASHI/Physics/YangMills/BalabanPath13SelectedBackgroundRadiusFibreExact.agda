{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPath13SelectedBackgroundRadiusFibreExact where

------------------------------------------------------------------------
-- PATH13 SELECTED BACKGROUND + NATIVE SMALL-FIELD RADIUS: SAME-OBJECT FIBRE
--
-- The variational Path13 target and the Path13 coercivity lane previously
-- exposed two independently supplied objects:
--
--   SelectedPhysicalBackground13Instantiation
--   SelectedInverseLinkRadius13 (path13Background selected)
--
-- They are logically distinct receipts: variational selection does not by
-- itself prove the numerical radius.  But they must refer to the SAME literal
-- side-13 background.  This record makes that dependency structural, so a
-- consumer cannot accidentally pair the selected background from one physical
-- realization with a radius certificate for another.
--
-- No new small-field theorem is asserted here.  This is a dependent fibre over
-- the selected physical background, not a constructor of the radius receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPath13SelectedPhysicalBackgroundTargetExact as Selected
import DASHI.Physics.YangMills.BalabanPath13BackgroundGaugeAdjointDefectExact as Background
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie

record SelectedPath13BackgroundWithRadius
    (CoarseField : Set) : Set₁ where
  field
    selectedPhysical :
      Selected.SelectedPhysicalBackground13Instantiation
        CoarseField Lie.SU2LieAlgebra

    nativeInverseLinkRadius :
      Background.SelectedInverseLinkRadius13
        (Selected.path13Background selectedPhysical)

open SelectedPath13BackgroundWithRadius public

selectedBackground13 :
  ∀ {CoarseField} →
  SelectedPath13BackgroundWithRadius CoarseField →
  Background.RationalSU2Background13
selectedBackground13 fibre =
  Selected.path13Background (selectedPhysical fibre)

radiusIsOnSelectedBackground :
  ∀ {CoarseField}
    (fibre : SelectedPath13BackgroundWithRadius CoarseField) →
  Background.SelectedInverseLinkRadius13
    (selectedBackground13 fibre)
radiusIsOnSelectedBackground = nativeInverseLinkRadius

selectedObjectExact :
  ∀ {CoarseField}
    (fibre : SelectedPath13BackgroundWithRadius CoarseField) →
  selectedBackground13 fibre
  ≡ Selected.path13Background (selectedPhysical fibre)
selectedObjectExact fibre = refl

cmp98Path13SelectedBackgroundRadiusFibreLevel : ProofLevel
cmp98Path13SelectedBackgroundRadiusFibreLevel = machineChecked

-- The fibre is a same-object ownership compiler only.  An inhabitant still
-- requires the physical Path13 selected background AND its native radius.
literalCMP98Path13SelectedBackgroundWithRadiusLevel : ProofLevel
literalCMP98Path13SelectedBackgroundWithRadiusLevel = conditional
