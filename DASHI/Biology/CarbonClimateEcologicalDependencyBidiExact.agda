module DASHI.Biology.CarbonClimateEcologicalDependencyBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Core.ActiveBidiDiscriminatorLoopExact as Bidi
import DASHI.Chemistry.DeepTimeCarbonReservoirFluxBalanceExact as Carbon
import DASHI.Chemistry.OceanCarbonateSaltTemperatureStressBidiExact as Ocean
import DASHI.Biology.ClimateCarryingCapacityDeepTimeCrossPollinationExact as Ecology

------------------------------------------------------------------------
-- CARBON -> CLIMATE/OCEAN -> ECOLOGICAL SELECTIVE REOPENING
--
-- A changed carbon-flow observation does not invalidate every ecological or
-- climate statement.  It reopens only certificates connected by a proof-bearing
-- dependency path.  The chain below is deliberately typed as an application
-- fixture; real climate attribution still requires empirical process receipts.
------------------------------------------------------------------------

data ClimateEcologyArtifact : Set where
  fossilReleaseCertificate
  atmosphericCarbonCertificate
  oceanCarbonateCertificate
  temperatureStressCertificate
  salinityHydrologyCertificate
  oxygenNutrientCertificate
  habitatSuitabilityCertificate
  carryingCapacityCertificate
  ecologicalFutureConeCertificate
  unrelatedTaxonomyCertificate
  : ClimateEcologyArtifact

data Depends : ClimateEcologyArtifact → ClimateEcologyArtifact → Set where
  fossilReleaseToAtmosphere :
    Depends fossilReleaseCertificate atmosphericCarbonCertificate
  atmosphereToOceanCarbonate :
    Depends atmosphericCarbonCertificate oceanCarbonateCertificate
  atmosphereToTemperatureStress :
    Depends atmosphericCarbonCertificate temperatureStressCertificate
  oceanCarbonateToHabitat :
    Depends oceanCarbonateCertificate habitatSuitabilityCertificate
  temperatureToHabitat :
    Depends temperatureStressCertificate habitatSuitabilityCertificate
  salinityToHabitat :
    Depends salinityHydrologyCertificate habitatSuitabilityCertificate
  oxygenNutrientToHabitat :
    Depends oxygenNutrientCertificate habitatSuitabilityCertificate
  habitatToCarryingCapacity :
    Depends habitatSuitabilityCertificate carryingCapacityCertificate
  carryingCapacityToFutureCone :
    Depends carryingCapacityCertificate ecologicalFutureConeCertificate

fossilReleaseReopensAtmosphere :
  Dependency.ReopeningObligation
    Depends fossilReleaseCertificate atmosphericCarbonCertificate
fossilReleaseReopensAtmosphere =
  Dependency.oneEdgeCreatesReopeningObligation fossilReleaseToAtmosphere

atmosphereReopensOceanCarbonate :
  Dependency.ReopeningObligation
    Depends atmosphericCarbonCertificate oceanCarbonateCertificate
atmosphereReopensOceanCarbonate =
  Dependency.oneEdgeCreatesReopeningObligation atmosphereToOceanCarbonate

oceanCarbonateReopensHabitat :
  Dependency.ReopeningObligation
    Depends oceanCarbonateCertificate habitatSuitabilityCertificate
oceanCarbonateReopensHabitat =
  Dependency.oneEdgeCreatesReopeningObligation oceanCarbonateToHabitat

habitatReopensCarryingCapacity :
  Dependency.ReopeningObligation
    Depends habitatSuitabilityCertificate carryingCapacityCertificate
habitatReopensCarryingCapacity =
  Dependency.oneEdgeCreatesReopeningObligation habitatToCarryingCapacity

carryingCapacityReopensFutureCone :
  Dependency.ReopeningObligation
    Depends carryingCapacityCertificate ecologicalFutureConeCertificate
carryingCapacityReopensFutureCone =
  Dependency.oneEdgeCreatesReopeningObligation carryingCapacityToFutureCone

fossilReleaseReopensEcologicalFutureCone :
  Dependency.ReopeningObligation
    Depends fossilReleaseCertificate ecologicalFutureConeCertificate
fossilReleaseReopensEcologicalFutureCone =
  Dependency.obligationsCompose
    fossilReleaseReopensAtmosphere
    (Dependency.obligationsCompose
      atmosphereReopensOceanCarbonate
      (Dependency.obligationsCompose
        oceanCarbonateReopensHabitat
        (Dependency.obligationsCompose
          habitatReopensCarryingCapacity
          carryingCapacityReopensFutureCone)))

------------------------------------------------------------------------
-- Existing-owner welds.
------------------------------------------------------------------------

carbonBoundary : Carbon.DeepTimeCarbonReservoirFluxBoundary
carbonBoundary = Carbon.canonicalDeepTimeCarbonReservoirFluxBoundary

oceanBoundary : Ocean.OceanCarbonateSaltTemperatureStressBoundary
oceanBoundary = Ocean.canonicalOceanCarbonateSaltTemperatureStressBoundary

ecologyBoundary : Ecology.ClimateCarryingCapacityDeepTimeBoundary
ecologyBoundary = Ecology.canonicalClimateCarryingCapacityDeepTimeBoundary

activeBidiBoundary : Bidi.ActiveBidiDiscriminatorLoopBoundary
activeBidiBoundary = Bidi.canonicalActiveBidiDiscriminatorLoopBoundary

record CarbonClimateEcologicalDependencyBoundary : Set where
  constructor carbon-climate-ecological-dependency-boundary
  field
    changedCarbonObservationReopensEveryRepositoryCertificate : Bool
    changedCarbonObservationReopensEveryRepositoryCertificateIsFalse :
      changedCarbonObservationReopensEveryRepositoryCertificate ≡ false
    proofBearingDependencyPathCanReopenEcologicalFutureConeTransitively : Bool
    proofBearingDependencyPathCanReopenEcologicalFutureConeTransitivelyIsTrue :
      proofBearingDependencyPathCanReopenEcologicalFutureConeTransitively ≡ true
    atmosphericCarbonAloneDeterminesEcologicalOutcome : Bool
    atmosphericCarbonAloneDeterminesEcologicalOutcomeIsFalse :
      atmosphericCarbonAloneDeterminesEcologicalOutcome ≡ false
    oceanStressRequiresMultipleCoordinates : Bool
    oceanStressRequiresMultipleCoordinatesIsTrue :
      oceanStressRequiresMultipleCoordinates ≡ true
    carryingCapacityIsIndependentOfHabitatState : Bool
    carryingCapacityIsIndependentOfHabitatStateIsFalse :
      carryingCapacityIsIndependentOfHabitatState ≡ false
    unrelatedCertificateNeedsReopeningWithoutDependencyPath : Bool
    unrelatedCertificateNeedsReopeningWithoutDependencyPathIsFalse :
      unrelatedCertificateNeedsReopeningWithoutDependencyPath ≡ false
    reading : String

canonicalCarbonClimateEcologicalDependencyBoundary :
  CarbonClimateEcologicalDependencyBoundary
canonicalCarbonClimateEcologicalDependencyBoundary =
  carbon-climate-ecological-dependency-boundary
    false refl
    true refl
    false refl
    true refl
    false refl
    false refl
    "Deep-time carbon remobilisation feeds a proof-bearing selective-reopening chain through atmospheric carbon, ocean carbonate/temperature stress, habitat suitability, carrying capacity and ecological future cones. This chain does not make atmospheric carbon a unique sufficient cause of ecological outcome and does not reopen unrelated certificates without a dependency path."
