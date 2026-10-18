{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.EinsteinPhysicalCouplingCalibrationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Promotion.NumericMeasuredAuthorityTokenNormalization as Numeric

------------------------------------------------------------------------
-- PHYSICAL EINSTEIN COUPLING: EXACT SI CONVENTION + MEASURED G
--
-- c is exact in the SI.  Newton's G is not: it is a measured CODATA input.
-- For an energy-density stress tensor the conventional field equation is
--
--   G_mu_nu = (8*pi*G/c^4) T_mu_nu.
--
-- The values below are a deterministic diagnostic from the vendored CODATA
-- 2022 row.  They are NOT a promoted value token.
------------------------------------------------------------------------

record EinsteinPhysicalCouplingCandidate : Set where
  constructor einsteinPhysicalCouplingCandidate
  field
    convention : String
    codataSourcePath : String
    codataArtifactSha256 : String
    gravitationalConstantSI : String
    gravitationalConstantStandardUncertaintySI : String
    exactSpeedOfLightSI : String
    eightPiGSI : String
    eightPiGStandardUncertaintySI : String
    eightPiGOverC4SI : String
    eightPiGOverC4StandardUncertaintySI : String
    relativeStandardUncertainty : String
    gAuthorityMetadataPresent : Bool
    gAuthorityMetadataPresentIsTrue :
      gAuthorityMetadataPresent ≡ true
    acceptedGAuthorityTokenPresent : Bool
    acceptedGAuthorityTokenPresentIsFalse :
      acceptedGAuthorityTokenPresent ≡ false
    gNumericValueLoadedInTypedAuthority : Bool
    gNumericValueLoadedInTypedAuthorityIsFalse :
      gNumericValueLoadedInTypedAuthority ≡ false
    physicalEinsteinCouplingPromoted : Bool
    physicalEinsteinCouplingPromotedIsFalse :
      physicalEinsteinCouplingPromoted ≡ false
    boundary : List String

open EinsteinPhysicalCouplingCandidate public

canonicalEinsteinPhysicalCouplingCandidate :
  EinsteinPhysicalCouplingCandidate
canonicalEinsteinPhysicalCouplingCandidate =
  einsteinPhysicalCouplingCandidate
    "energy-density convention: G_mu_nu = (8*pi*G/c^4) T_mu_nu"
    "data/authority/si_metrology_20260615/nist_constants_allascii_2022.txt"
    "77fb90e66c40db3e6eb16630bc9c88e4c7c8beddbe5e71be406f2f26e3f67e67"
    "6.67430e-11 m^3 kg^-1 s^-2"
    "1.5e-15 m^3 kg^-1 s^-2"
    "299792458 m s^-1 exact"
    "1.6774345478283484e-9 m^3 kg^-1 s^-2"
    "3.769911184307751e-14 m^3 kg^-1 s^-2"
    "2.0766474428449717e-43 m J^-1"
    "4.667112902128249e-48 m J^-1"
    "2.2474266964325848e-5"
    true refl
    (Numeric.acceptedAuthorityTokenPresent Numeric.gNormalizedToken)
    (Numeric.acceptedAuthorityTokenPresentIsFalse Numeric.gNormalizedToken)
    (Numeric.numericValueLoaded Numeric.gNormalizedToken)
    (Numeric.numericValueLoadedIsFalse Numeric.gNormalizedToken)
    false refl
    ( "The SI metre/second/c carrier is not the blocker here."
    ∷ "G is measured rather than an exact SI defining constant."
    ∷ "The vendored CODATA row can be replayed numerically before promotion."
    ∷ "Typed physical use still requires accepted G authority/value ingestion with uncertainty."
    ∷ "A stress-tensor unit convention must be fixed before comparing the normalized finite kappa=1 fixture with the SI coupling."
    ∷ [] )

gCandidateAvailableButNotPromoted :
  gAuthorityMetadataPresent canonicalEinsteinPhysicalCouplingCandidate ≡ true
gCandidateAvailableButNotPromoted = refl

physicalCouplingStillUnpromoted :
  physicalEinsteinCouplingPromoted canonicalEinsteinPhysicalCouplingCandidate
  ≡ false
physicalCouplingStillUnpromoted = refl
