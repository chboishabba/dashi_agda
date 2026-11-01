{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPath13SelectedBackgroundRadiusFibreExact where

------------------------------------------------------------------------
-- PATH13 SELECTED BACKGROUND + NATIVE SMALL-FIELD RADIUS: SAME-OBJECT FIBRE
--
-- Compatibility consumers still use one dependent fibre containing the
-- selected Path13 physical background and `SelectedInverseLinkRadius13` on that
-- exact object.
--
-- The preferred producer is now stronger: the native radius is derived from
-- `Path13SelectedVariationalRadiusRepresentation`.  Thus a caller may still
-- supply the historical fibre directly, but the source-facing route need not
-- pay an independent radius receipt once the variational/physical defect
-- representation has been identified.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPath13SelectedPhysicalBackgroundTargetExact as Selected
import DASHI.Physics.YangMills.BalabanPath13BackgroundGaugeAdjointDefectExact as Background
import DASHI.Physics.YangMills.BalabanPath13SelectedVariationalRadiusExact as VariationalRadius
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

fromSelectedVariationalRadius :
  ∀ {CoarseField} →
  VariationalRadius.Path13SelectedVariationalRadiusRepresentation CoarseField →
  SelectedPath13BackgroundWithRadius CoarseField
fromSelectedVariationalRadius inputs = record
  { selectedPhysical = VariationalRadius.selected inputs
  ; nativeInverseLinkRadius =
      VariationalRadius.selectedPath13NativeRadius inputs
  }

variationalRadiusFibreSelectedObjectExact :
  ∀ {CoarseField}
    (inputs : VariationalRadius.Path13SelectedVariationalRadiusRepresentation
      CoarseField) →
  selectedPhysical (fromSelectedVariationalRadius inputs)
  ≡ VariationalRadius.selected inputs
variationalRadiusFibreSelectedObjectExact inputs = refl

cmp98Path13SelectedBackgroundRadiusFibreLevel : ProofLevel
cmp98Path13SelectedBackgroundRadiusFibreLevel = machineChecked

cmp98Path13SelectedVariationalRadiusFibreCompilerLevel : ProofLevel
cmp98Path13SelectedVariationalRadiusFibreCompilerLevel = machineChecked

-- Compatibility fibre inhabitance is no longer itself a primitive source
-- payment on the preferred route.  The remaining source obligation is the
-- variational/physical representation consumed by `fromSelectedVariationalRadius`.
literalCMP98Path13SelectedBackgroundWithRadiusLevel : ProofLevel
literalCMP98Path13SelectedBackgroundWithRadiusLevel = conditional
