module DASHI.Physics.Plasma.DynamicZeroBounceAdmissibilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AuthorityBoundary as Authority
import DASHI.Physics.Plasma.ZeroBouncePopulationExact as ZeroBounce

------------------------------------------------------------------------
-- DYNAMIC ZERO-BOUNCE ADMISSIBILITY
--
-- A time-dependent magnetic-control proposal must pass three distinct gates:
--   (1) phase advance before the nominal mirror turning event,
--   (2) an explicitly declared sub-cyclotron / guiding-centre regime,
--   (3) resonance / heating / transport exclusion for the same population.
--
-- These are receipts, not silently promoted analytic theorems.
------------------------------------------------------------------------

record DynamicDetrappingAdmissibility
    (population : ZeroBounce.DeclaredParticlePopulation) : Set₁ where
  constructor dynamic-detrapping-admissibility
  field
    controlAngularFrequencyReceipt : Set
    nominalTurningTimeReceipt : Set
    requiredPhaseAdvanceReceipt : Set
    phaseAdvanceBeforeTurningReceipt : Set

    cyclotronFrequencyReceipt : Set
    declaredAdiabaticFractionReceipt : Set
    belowCyclotronAdiabaticCeilingReceipt : Set

    bounceFrequencySpectrumReceipt : Set
    cyclotronHarmonicSpectrumReceipt : Set
    lowOrderBounceResonanceClearanceReceipt : Set
    lowOrderCyclotronResonanceClearanceReceipt : Set

    inducedElectricFieldReceipt : Set
    stochasticHeatingExclusionReceipt : Set
    secularParticleHeatingExclusionReceipt : Set
    radialTransportPenaltyReceipt : Set
    torqueAndMomentumTransferReceipt : Set
    RFOrControlPowerReceipt : Set

    sameSpeciesEnergyPitchPopulationReceipt : Set
    sameFiniteBetaEquilibriumReceipt : Set
    sameOrbitModelReceipt : Set
    measurementAuthority : Authority.ArtifactAuthorityBoundary
    admissibilityReference : String

open DynamicDetrappingAdmissibility public

record DynamicZeroBounceWindowBoundary : Set where
  constructor dynamic-zero-bounce-window-boundary
  field
    fasterControlAlwaysBetter : Bool
    fasterControlAlwaysBetterIsFalse :
      fasterControlAlwaysBetter ≡ false

    phaseAdvanceBeforeTurningAloneProvesZeroBounce : Bool
    phaseAdvanceBeforeTurningAloneProvesZeroBounceIsFalse :
      phaseAdvanceBeforeTurningAloneProvesZeroBounce ≡ false

    subCyclotronControlAloneExcludesHeating : Bool
    subCyclotronControlAloneExcludesHeatingIsFalse :
      subCyclotronControlAloneExcludesHeating ≡ false

    resonanceClearanceMustBePopulationIndexed : Bool
    resonanceClearanceMustBePopulationIndexedIsTrue :
      resonanceClearanceMustBePopulationIndexed ≡ true

    empiricalDynamicPerformanceRequiresArtifactAuthority : Bool
    empiricalDynamicPerformanceRequiresArtifactAuthorityIsTrue :
      empiricalDynamicPerformanceRequiresArtifactAuthority ≡ true

canonicalDynamicZeroBounceWindowBoundary : DynamicZeroBounceWindowBoundary
canonicalDynamicZeroBounceWindowBoundary =
  dynamic-zero-bounce-window-boundary
    false refl
    false refl
    false refl
    true refl
    true refl

rmfIonHeatingSource : String
rmfIonHeatingSource =
  "Cohen and Glasser, Phys. Rev. Lett. 85, 5114 (2000), doi:10.1103/PhysRevLett.85.5114: rotating magnetic fields near ion-cyclotron resonance can produce explosive ion heating in an FRC model."

adiabaticitySource : String
adiabaticitySource =
  "Electron cyclotron resonance plasma review, J. Appl. Phys. (2025): magnetic-moment adiabatic invariance assumes field variation slow relative to cyclotron motion and can fail near cyclotron resonance."
