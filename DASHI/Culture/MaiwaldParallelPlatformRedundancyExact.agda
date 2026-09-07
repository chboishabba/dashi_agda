module DASHI.Culture.MaiwaldParallelPlatformRedundancyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- MAIWALD PARALLEL PLATFORM REDUNDANCY
--
-- The 2023/2024 SURP line uses the Weber-group cryogenic apparatus at the
-- University of Colorado Boulder.  A separate 2024 Caltech/JPL paper reports
-- a benchtop implementation based on a minimally modified commercial ESI linear
-- ion-trap mass spectrometer coupled to a broadly tunable CW QCL source.
-- This is evidence for more than one hardware implementation of the application
-- concept before Maiwald's death; it does not prove duplicate mission-qualified
-- capability, calibration state, or JPL qualification ownership.
------------------------------------------------------------------------

record ParallelPlatformReceipt : Set where
  constructor parallel-platform-receipt
  field
    applicationDomain : String
    platformA : String
    platformB : String
    platformAReference : String
    platformBReference : String
    distinctHardwareImplementation : Bool
    distinctHardwareImplementationIsTrue : distinctHardwareImplementation ≡ true
    sameApplicationConcept : Bool
    sameApplicationConceptIsTrue : sameApplicationConcept ≡ true
    duplicateMissionQualifiedCapability : Bool
    duplicateMissionQualifiedCapabilityIsFalse : duplicateMissionQualifiedCapability ≡ false
    sameCalibrationStateTransferred : Bool
    sameCalibrationStateTransferredIsFalse : sameCalibrationStateTransferred ≡ false
    boundedReading : String

maiwaldParallelPlatformReceipt : ParallelPlatformReceipt
maiwaldParallelPlatformReceipt = parallel-platform-receipt
  "messenger-assisted IR photodissociation/action spectroscopy for planetary biosignature discrimination"
  "University of Colorado Boulder / Weber-group cryogenic ion apparatus"
  "Caltech/JPL benchtop ESI linear-ion-trap + tunable quantum-cascade-laser implementation"
  "JPL FY23/FY24 SURP posters: Unambiguous Detection of Biosignatures by Action Spectroscopy"
  "Nguyen, Ober, Balaji, Maiwald, Hodyss, Madzunkov, Okumura, Nemchick; Infrared Photodissociation Spectroscopy of Water-Tagged Ions with a Widely Tunable Quantum Cascade Laser for Planetary Science Applications; 2024; CaltechAUTHORS / PMC11155675"
  true refl
  true refl
  false refl
  false refl
  "Two hardware implementations of the action-spectroscopy concept are source-backed before Maiwald's death. This weakens a single-platform hypothesis. It does not establish duplication of JPL mission qualification, calibration archives, failure history, or tacit integration workflow."

record MaiwaldParallelPlatformBoundary : Set where
  constructor maiwald-parallel-platform-boundary
  field
    twoPlatformsImpliesSameCalibration : Bool
    twoPlatformsImpliesSameCalibrationIsFalse : twoPlatformsImpliesSameCalibration ≡ false
    twoPlatformsImpliesMissionQualificationRedundant : Bool
    twoPlatformsImpliesMissionQualificationRedundantIsFalse : twoPlatformsImpliesMissionQualificationRedundant ≡ false
    publicationCoauthorshipImpliesCurrentCustody : Bool
    publicationCoauthorshipImpliesCurrentCustodyIsFalse : publicationCoauthorshipImpliesCurrentCustody ≡ false

canonicalMaiwaldParallelPlatformBoundary : MaiwaldParallelPlatformBoundary
canonicalMaiwaldParallelPlatformBoundary = maiwald-parallel-platform-boundary
  false refl
  false refl
  false refl
