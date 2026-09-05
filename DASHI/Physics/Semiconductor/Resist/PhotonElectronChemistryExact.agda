{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Resist.PhotonElectronChemistryExact where

open import Agda.Builtin.Nat using (Nat; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)

-- First finite carrier for the EUV resist interaction chain.  The coordinates
-- intentionally separate incident photons, absorbed photons, electron events,
-- chemical events and developed sites.  No fixed yield between these levels is
-- assumed.

record ResistInteraction : Set where
  constructor resistInteraction
  field
    incidentPhotons   : Nat
    absorbedPhotons   : Nat
    primaryElectrons  : Nat
    secondaryEvents   : Nat
    chemicalEvents    : Nat
    developedSites    : Nat

open ResistInteraction public

-- Constructive <= witness over naturals: a + gap = b.
record BoundedBy (a b : Nat) : Set where
  constructor boundedBy
  field
    gap      : Nat
    equation : a + gap ≡ b

open BoundedBy public

AbsorptionBounded : ResistInteraction → Set
AbsorptionBounded x = BoundedBy (absorbedPhotons x) (incidentPhotons x)

DevelopmentBoundedByChemistry : ResistInteraction → Set
DevelopmentBoundedByChemistry x = BoundedBy (developedSites x) (chemicalEvents x)

-- Two synthetic outcomes with the same incident photon count but different
-- downstream chemistry.  This is a finite non-determinacy fixture, not a claim
-- about probabilities or a specific resist formulation.
interactionA : ResistInteraction
interactionA = resistInteraction 100 60 55 120 80 70

interactionB : ResistInteraction
interactionB = resistInteraction 100 60 55 100 65 55

sameIncidentCount : incidentPhotons interactionA ≡ incidentPhotons interactionB
sameIncidentCount = refl

sameAbsorbedCount : absorbedPhotons interactionA ≡ absorbedPhotons interactionB
sameAbsorbedCount = refl

samePrimaryElectronCount : primaryElectrons interactionA ≡ primaryElectrons interactionB
samePrimaryElectronCount = refl

-- Explicit witnesses that the final developed-site counts differ despite the
-- same incident/absorbed/primary-electron counts.
record StrictDifference (a b : Nat) : Set where
  constructor strictDifference
  field
    delta    : Nat
    equation : a + suc delta ≡ b

open StrictDifference public

developedSiteDifference :
  StrictDifference (developedSites interactionB) (developedSites interactionA)
developedSiteDifference = strictDifference 14 refl

-- Therefore the coarse photon-count surface is intentionally insufficient to
-- identify the downstream chemical/development state.  A later stochastic
-- model can replace these synthetic witnesses with distributions and bounds.
record SamePhotonSurfaceDifferentDevelopment : Set where
  constructor samePhotonSurfaceDifferentDevelopment
  field
    sameIncident : incidentPhotons interactionA ≡ incidentPhotons interactionB
    sameAbsorbed : absorbedPhotons interactionA ≡ absorbedPhotons interactionB
    differentDeveloped :
      StrictDifference (developedSites interactionB) (developedSites interactionA)

nonDescentFixture : SamePhotonSurfaceDifferentDevelopment
nonDescentFixture =
  samePhotonSurfaceDifferentDevelopment sameIncidentCount sameAbsorbedCount developedSiteDifference
