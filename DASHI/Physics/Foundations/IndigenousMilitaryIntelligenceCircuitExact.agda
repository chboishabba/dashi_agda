module DASHI.Physics.Foundations.IndigenousMilitaryIntelligenceCircuitExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Pine Gap and Borneo Barracks are related as military-intelligence sites on
-- Indigenous Country, but their institutional scales and functions are not
-- identified.

data IntelligenceSite : Set where
  pineGap : IntelligenceSite
  borneoBarracksCabarlah : IntelligenceSite

data CountryCarrier : Set where
  arrernteCountry : CountryCarrier
  cabarlahUnderlyingCountry : CountryCarrier

data IntelligenceScale : Set where
  jointGlobalStrategic : IntelligenceScale
  australianRegionalElectronicWarfare : IntelligenceScale

siteCountry : IntelligenceSite → CountryCarrier
siteCountry pineGap = arrernteCountry
siteCountry borneoBarracksCabarlah = cabarlahUnderlyingCountry

siteScale : IntelligenceSite → IntelligenceScale
siteScale pineGap = jointGlobalStrategic
siteScale borneoBarracksCabarlah = australianRegionalElectronicWarfare

pineGapIsNotBorneoBarracks :
  pineGap ≡ borneoBarracksCabarlah → ⊥
pineGapIsNotBorneoBarracks ()

jointGlobalIsNotRegionalADF :
  jointGlobalStrategic ≡ australianRegionalElectronicWarfare → ⊥
jointGlobalIsNotRegionalADF ()

siteCountryIsNotCollapsed :
  siteCountry pineGap ≡ siteCountry borneoBarracksCabarlah → ⊥
siteCountryIsNotCollapsed ()

------------------------------------------------------------------------
-- The protest programme explicitly joins two demands.  This exact finite fact
-- is kept separate from claims about the use of intelligence in any particular
-- strike, which are not publicly established by the attached evidence.

data ProtestDemand : Set where
  returnArrernteLand : ProtestDemand
  endPalestineComplicity : ProtestDemand

pineGapPalestineDemands : List ProtestDemand
pineGapPalestineDemands =
  returnArrernteLand ∷ endPalestineComplicity ∷ []

hasReturnDemand : List ProtestDemand → Bool
hasReturnDemand [] = false
hasReturnDemand (returnArrernteLand ∷ _) = true
hasReturnDemand (endPalestineComplicity ∷ demands) =
  hasReturnDemand demands

hasPalestineDemand : List ProtestDemand → Bool
hasPalestineDemand [] = false
hasPalestineDemand (returnArrernteLand ∷ demands) =
  hasPalestineDemand demands
hasPalestineDemand (endPalestineComplicity ∷ _) = true

pineGapProtestHasReturnDemand :
  hasReturnDemand pineGapPalestineDemands ≡ true
pineGapProtestHasReturnDemand = refl

pineGapProtestHasPalestineDemand :
  hasPalestineDemand pineGapPalestineDemands ≡ true
pineGapProtestHasPalestineDemand = refl

data OperationalLinkStatus : Set where
  protestAllegationAndStructuralConcern : OperationalLinkStatus
  publiclyVerifiedSpecificStrikeLink : OperationalLinkStatus

openSourceOperationalStatus : OperationalLinkStatus
openSourceOperationalStatus = protestAllegationAndStructuralConcern

openSourceStatusIsNotSpecificStrikeVerification :
  openSourceOperationalStatus ≡ publiclyVerifiedSpecificStrikeLink → ⊥
openSourceStatusIsNotSpecificStrikeVerification ()

------------------------------------------------------------------------
-- Shared abstract circuit, preserving site-specific endpoints.

data CircuitStage : Set where
  indigenousCountryStage : CircuitStage
  militaryInstallationStage : CircuitStage
  remoteConflictLegibilityStage : CircuitStage

nextCircuitStage : CircuitStage → CircuitStage
nextCircuitStage indigenousCountryStage = militaryInstallationStage
nextCircuitStage militaryInstallationStage = remoteConflictLegibilityStage
nextCircuitStage remoteConflictLegibilityStage = remoteConflictLegibilityStage

countryToRemoteLegibility :
  nextCircuitStage (nextCircuitStage indigenousCountryStage)
  ≡ remoteConflictLegibilityStage
countryToRemoteLegibility = refl

record IntelligenceCircuitBoundary : Set where
  constructor intelligenceCircuitBoundary
  field
    sharedTopologyMakesSitesInstitutionallyIdentical : Bool
    sharedTopologyMakesSitesInstitutionallyIdenticalIsFalse :
      sharedTopologyMakesSitesInstitutionallyIdentical ≡ false

    protestDemandProvesSpecificTargetingChain : Bool
    protestDemandProvesSpecificTargetingChainIsFalse :
      protestDemandProvesSpecificTargetingChain ≡ false

    indigenousPlaceNameTransfersSovereigntyToMilitarySite : Bool
    indigenousPlaceNameTransfersSovereigntyToMilitarySiteIsFalse :
      indigenousPlaceNameTransfersSovereigntyToMilitarySite ≡ false

open IntelligenceCircuitBoundary public

canonicalIntelligenceCircuitBoundary : IntelligenceCircuitBoundary
canonicalIntelligenceCircuitBoundary =
  intelligenceCircuitBoundary
    false refl
    false refl
    false refl
