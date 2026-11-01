module DASHI.Physics.DarkSector.SectorCarrier where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Collider-facing sector carrier.  Gauge singlet status, sector membership,
-- and detector visibility are distinct labels.

data Sector : Set where
  visibleSector : Sector
  darkSector : Sector

data SMChargeClass : Set where
  smSinglet : SMChargeClass
  smCharged : SMChargeClass

data DecayVisibility : Set where
  noVisibleDaughters : DecayVisibility
  hasVisibleDaughters : DecayVisibility

data DetectorVisibility : Set where
  detectorInvisible : DetectorVisibility
  detectorVisible : DetectorVisibility

record ParticleState : Set where
  constructor particleState
  field
    sector : Sector
    mass : Nat
    momentumMagnitude : Nat
    smCharge : SMChargeClass
    decayVisibility : DecayVisibility
    lifetimeTicks : Nat

open ParticleState public

classifyDetectorVisibility : ParticleState → DetectorVisibility
classifyDetectorVisibility
  (particleState visibleSector mass momentum smCharged daughters lifetime) =
  detectorVisible
classifyDetectorVisibility
  (particleState visibleSector mass momentum smSinglet hasVisibleDaughters lifetime) =
  detectorVisible
classifyDetectorVisibility
  (particleState visibleSector mass momentum smSinglet noVisibleDaughters lifetime) =
  detectorInvisible
classifyDetectorVisibility
  (particleState darkSector mass momentum charge hasVisibleDaughters lifetime) =
  detectorVisible
classifyDetectorVisibility
  (particleState darkSector mass momentum charge noVisibleDaughters lifetime) =
  detectorInvisible

canonicalHiddenLLP : ParticleState
canonicalHiddenLLP =
  particleState darkSector 4 8 smSinglet hasVisibleDaughters 4

canonicalStableDarkState : ParticleState
canonicalStableDarkState =
  particleState darkSector 3 2 smSinglet noVisibleDaughters 0

canonicalMuonDaughter : ParticleState
canonicalMuonDaughter =
  particleState visibleSector 1 5 smCharged hasVisibleDaughters 0

hiddenLLPBecomesVisibleThroughDaughters :
  classifyDetectorVisibility canonicalHiddenLLP ≡ detectorVisible
hiddenLLPBecomesVisibleThroughDaughters = refl

stableDarkStateRemainsDetectorInvisible :
  classifyDetectorVisibility canonicalStableDarkState ≡ detectorInvisible
stableDarkStateRemainsDetectorInvisible = refl

muonDaughterIsVisible :
  classifyDetectorVisibility canonicalMuonDaughter ≡ detectorVisible
muonDaughterIsVisible = refl

record SectorCarrierBoundary : Set where
  constructor sectorCarrierBoundary
  field
    smSingletMeansNoPossibleDetectorSignature : Bool
    smSingletMeansNoPossibleDetectorSignatureIsFalse :
      smSingletMeansNoPossibleDetectorSignature ≡ false

    darkSectorMembershipImpliesCosmologicalDarkMatter : Bool
    darkSectorMembershipImpliesCosmologicalDarkMatterIsFalse :
      darkSectorMembershipImpliesCosmologicalDarkMatter ≡ false

    detectorInvisibilityImpliesZeroStressEnergy : Bool
    detectorInvisibilityImpliesZeroStressEnergyIsFalse :
      detectorInvisibilityImpliesZeroStressEnergy ≡ false

open SectorCarrierBoundary public

canonicalSectorCarrierBoundary : SectorCarrierBoundary
canonicalSectorCarrierBoundary =
  sectorCarrierBoundary false refl false refl false refl
