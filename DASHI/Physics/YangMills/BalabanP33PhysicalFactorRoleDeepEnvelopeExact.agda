module DASHI.Physics.YangMills.BalabanP33PhysicalFactorRoleDeepEnvelopeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Give the physical deep-envelope proof one finite role language.  Every one
-- of the four plaquette slots has exactly one orientation role (positive or
-- inverse) and one placement-dependent jet selection (value, first or second).
-- The actual and flat factors and their selected-factor envelopes are obtained
-- only by dispatching this role.  The exhaustive four-role list prevents a
-- placement proof from silently omitting or duplicating a slot.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (length)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33WilsonPlaquetteSecondVariationPlacementsExact as Placement
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonPlacementTelescopeExact as Named
import DASHI.Physics.YangMills.BalabanP33PhysicalSelectedFactorEnvelopeExact as Envelope
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Radius
import DASHI.Physics.YangMills.BalabanP33WilsonPairDeepBudgetExact as Budget

data LinkOrientationRole : Set where
  positiveOrientation inverseOrientation : LinkOrientationRole

record PhysicalFactorRole : Set where
  constructor factorRole
  field
    slot : Placement.PlaquetteLinkSlot4
    orientation : LinkOrientationRole
    selection : Named.FactorSelection

open PhysicalFactorRole public

roleOfSlot :
  Placement.PlaquetteSecondVariationPlacement4 →
  Placement.PlaquetteLinkSlot4 → PhysicalFactorRole
roleOfSlot placement Placement.slot0 =
  factorRole Placement.slot0 positiveOrientation (Named.selection0 placement)
roleOfSlot placement Placement.slot1 =
  factorRole Placement.slot1 positiveOrientation (Named.selection1 placement)
roleOfSlot placement Placement.slot2 =
  factorRole Placement.slot2 inverseOrientation (Named.selection2 placement)
roleOfSlot placement Placement.slot3 =
  factorRole Placement.slot3 inverseOrientation (Named.selection3 placement)

placementRoles :
  Placement.PlaquetteSecondVariationPlacement4 → List PhysicalFactorRole
placementRoles placement =
  roleOfSlot placement Placement.slot0
  ∷ roleOfSlot placement Placement.slot1
  ∷ roleOfSlot placement Placement.slot2
  ∷ roleOfSlot placement Placement.slot3
  ∷ []

placementRoleCountExact : ∀ placement →
  length (placementRoles placement) ≡ 4
placementRoleCountExact placement = refl

roleActualFactor :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 →
  Physical.Plaquette4 → PhysicalFactorRole →
  Q.RationalQuaternion
roleActualFactor background field plaquette role =
  Envelope.slotActualFactor background field plaquette
    (slot role) (selection role)

roleFlatFactor :
  Coordinates.PhysicalSU2BondField4 →
  Physical.Plaquette4 → PhysicalFactorRole →
  Q.RationalQuaternion
roleFlatFactor field plaquette role =
  Envelope.slotFlatFactor field plaquette
    (slot role) (selection role)

roleSelectedEnvelope :
  ∀ background field plaquette role →
  Radius.RelaxedInverseLinkRadius background →
  Envelope.SelectedFactorEnvelope
    (roleActualFactor background field plaquette role)
    (roleFlatFactor field plaquette role)
    Budget.epsilon
roleSelectedEnvelope background field plaquette role radius =
  Envelope.slotSelectedEnvelope
    background field plaquette (slot role) (selection role) radius

record FourRoleEnvelopeFamily
    (background : Physical.RationalSU2Background4)
    (field : Coordinates.PhysicalSU2BondField4)
    (plaquette : Physical.Plaquette4)
    (placement : Placement.PlaquetteSecondVariationPlacement4) : Set₁ where
  field
    radius : Radius.RelaxedInverseLinkRadius background

    envelope0 : Envelope.SelectedFactorEnvelope
      (roleActualFactor background field plaquette
        (roleOfSlot placement Placement.slot0))
      (roleFlatFactor field plaquette
        (roleOfSlot placement Placement.slot0))
      Budget.epsilon

    envelope1 : Envelope.SelectedFactorEnvelope
      (roleActualFactor background field plaquette
        (roleOfSlot placement Placement.slot1))
      (roleFlatFactor field plaquette
        (roleOfSlot placement Placement.slot1))
      Budget.epsilon

    envelope2 : Envelope.SelectedFactorEnvelope
      (roleActualFactor background field plaquette
        (roleOfSlot placement Placement.slot2))
      (roleFlatFactor field plaquette
        (roleOfSlot placement Placement.slot2))
      Budget.epsilon

    envelope3 : Envelope.SelectedFactorEnvelope
      (roleActualFactor background field plaquette
        (roleOfSlot placement Placement.slot3))
      (roleFlatFactor field plaquette
        (roleOfSlot placement Placement.slot3))
      Budget.epsilon

open FourRoleEnvelopeFamily public

physicalFourRoleEnvelopeFamily :
  ∀ background field plaquette placement →
  Radius.RelaxedInverseLinkRadius background →
  FourRoleEnvelopeFamily background field plaquette placement
physicalFourRoleEnvelopeFamily background field plaquette placement radius = record
  { radius = radius
  ; envelope0 = roleSelectedEnvelope background field plaquette
      (roleOfSlot placement Placement.slot0) radius
  ; envelope1 = roleSelectedEnvelope background field plaquette
      (roleOfSlot placement Placement.slot1) radius
  ; envelope2 = roleSelectedEnvelope background field plaquette
      (roleOfSlot placement Placement.slot2) radius
  ; envelope3 = roleSelectedEnvelope background field plaquette
      (roleOfSlot placement Placement.slot3) radius
  }

positiveRole0Exact : ∀ placement →
  orientation (roleOfSlot placement Placement.slot0)
  ≡ positiveOrientation
positiveRole0Exact placement = refl

positiveRole1Exact : ∀ placement →
  orientation (roleOfSlot placement Placement.slot1)
  ≡ positiveOrientation
positiveRole1Exact placement = refl

inverseRole2Exact : ∀ placement →
  orientation (roleOfSlot placement Placement.slot2)
  ≡ inverseOrientation
inverseRole2Exact placement = refl

inverseRole3Exact : ∀ placement →
  orientation (roleOfSlot placement Placement.slot3)
  ≡ inverseOrientation
inverseRole3Exact placement = refl

physicalFactorRoleEnumerationLevel : ProofLevel
physicalFactorRoleEnumerationLevel = machineChecked

physicalFactorRoleEnvelopeDispatchLevel : ProofLevel
physicalFactorRoleEnvelopeDispatchLevel = machineChecked
