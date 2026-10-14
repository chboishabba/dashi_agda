{-# OPTIONS --safe #-}
module DASHI.Physics.ExoticGravity.AntigravityCODATA2022GAuthorityAdmissionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Integer.Base using (+_)
open import Data.List.Base using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _/_)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Promotion.NumericAuthorityPayloadValidator as Payload
import DASHI.Promotion.NumericMeasuredAuthorityTokenNormalization as Numeric
import DASHI.Physics.Closure.EinsteinPhysicalCouplingCalibrationExact as Einstein
import DASHI.Physics.Foundations.CMP119AntigravityPhysicalEinsteinCalibrationExact as Physical

------------------------------------------------------------------------
-- ATTRIBUTED SOURCE LAYER
--
-- Acquired 2026-10-14 from primary NIST/CODATA surfaces.
--
-- Source-entitled claims only:
--   * NIST Web Version 9.0 identifies the 2022 CODATA set as the latest
--     available/current recommended set and records the 9 May 2024 update;
--   * NIST SP 961 / the CODATA tables report
--       G = 6.674 30(15) x 10^-11 m^3 kg^-1 s^-2,
--       relative standard uncertainty 2.2 x 10^-5;
--   * Mohr-Newell-Taylor-Tiesinga 2025 reports the 2022 adjustment and its
--     international CODATA recommendation context.
--
-- Attribution is deliberately non-promoting: the source atlas does not itself
-- create repository authority.  The antigravity-consumer admission below is a
-- separate explicit repository decision over this exact source/value object.
------------------------------------------------------------------------

nistCODATA2022DatabaseSource : Source.AttributedSource
nistCODATA2022DatabaseSource =
  Source.mkNoDOISource
    "Eite Tiesinga; Peter J. Mohr; David B. Newell; Barry N. Taylor; NIST database maintainers"
    "2022 CODATA Recommended Values of the Fundamental Physical Constants, Web Version 9.0"
    "NIST Standard Reference Database 121 / Fundamental Physical Constants"
    "2024"
    "https://physics.nist.gov/constants"
    Source.governmentSource
    "primary authority surface for the current 2022 CODATA recommended constants; used here only for source identity, version status, G value, uncertainty and SI unit"
    Source.publicAttribution

codata2022RMPSource : Source.AttributedSource
codata2022RMPSource =
  Source.mkDOISource
    "Peter J. Mohr; David B. Newell; Barry N. Taylor; Eite Tiesinga"
    "CODATA recommended values of the fundamental physical constants: 2022"
    "Reviews of Modern Physics 97, 025002"
    "2025"
    "10.1103/RevModPhys.97.025002"
    "https://doi.org/10.1103/RevModPhys.97.025002"
    Source.academicArticleSource
    "primary CODATA adjustment publication supporting the provenance and recommendation status of the 2022 constants; not a theorem import"
    Source.publicAttribution

codata2022GSourceAtlas : Source.AttributedSourceAtlas
codata2022GSourceAtlas =
  Source.mkSourceAtlas
    "CODATA 2022 Newtonian-G authority atlas"
    "DASHI.Physics.ExoticGravity.AntigravityCODATA2022GAuthorityAdmissionExact"
    (nistCODATA2022DatabaseSource ∷ codata2022RMPSource ∷ [])
    "bounded provenance for the current CODATA-2022 G value, standard uncertainty, SI unit and adjustment provenance"

sourceAtlasDoesNotCreateAuthority :
  Source.atlasCreatesAuthority codata2022GSourceAtlas ≡ false
sourceAtlasDoesNotCreateAuthority =
  Source.atlasCreatesAuthorityIsFalse codata2022GSourceAtlas

nistCitationDoesNotCreateAuthority :
  Source.citationCreatesAuthority nistCODATA2022DatabaseSource ≡ false
nistCitationDoesNotCreateAuthority =
  Source.citationCreatesAuthorityIsFalse nistCODATA2022DatabaseSource

sourceEntitlesCurrent2022CODATAStatus : Bool
sourceEntitlesCurrent2022CODATAStatus = true

sourceEntitlesGValueAndStandardUncertainty : Bool
sourceEntitlesGValueAndStandardUncertainty = true

------------------------------------------------------------------------
-- EXACT FINITE INGESTION CARRIER
--
-- These rationals exactly encode the decimal strings printed by the authority.
-- They do NOT claim that G is an exact physical constant: the uncertainty is
-- retained as an independent exact finite carrier.
------------------------------------------------------------------------

gValueSI : ℚ
gValueSI = (+ 667430) / 10000000000000000

gStandardUncertaintySI : ℚ
gStandardUncertaintySI = (+ 15) / 10000000000000000

gLowerSI : ℚ
gLowerSI = (+ 667415) / 10000000000000000

gUpperSI : ℚ
gUpperSI = (+ 667445) / 10000000000000000

gRawValueText : String
gRawValueText = "6.674 30 x 10^-11 m^3 kg^-1 s^-2"

gRawStandardUncertaintyText : String
gRawStandardUncertaintyText = "0.000 15 x 10^-11 m^3 kg^-1 s^-2 (one standard uncertainty)"

gRelativeStandardUncertaintyText : String
gRelativeStandardUncertaintyText = "2.2 x 10^-5"

exactNewtonianGClaimed : Bool
exactNewtonianGClaimed = false

------------------------------------------------------------------------
-- SOURCE -> NORMALIZED TOKEN -> CONSUMER ADMISSION
--
-- This is the explicit promotion step that the generic source atlas refuses to
-- perform.  The exact normalized G token, exact SI dimension vector, authority
-- source, parsed value and retained uncertainty are bound on the same object.
------------------------------------------------------------------------

record NISTCODATA2022GSourceEntitlement : Set where
  constructor nist-codata-2022-g-source-entitlement
  field
    authoritySource : Source.AttributedSource
    authoritySourceIsNISTDatabase :
      authoritySource ≡ nistCODATA2022DatabaseSource
    authorityVersion : String
    authorityAccessDate : String
    rawValueText : String
    rawStandardUncertaintyText : String
    relativeStandardUncertaintyText : String

open NISTCODATA2022GSourceEntitlement public

canonicalNISTCODATA2022GSourceEntitlement :
  NISTCODATA2022GSourceEntitlement
canonicalNISTCODATA2022GSourceEntitlement =
  nist-codata-2022-g-source-entitlement
    nistCODATA2022DatabaseSource
    refl
    "NIST CODATA Web Version 9.0; 2022 recommended values; database update 9 May 2024"
    "2026-10-14"
    gRawValueText
    gRawStandardUncertaintyText
    gRelativeStandardUncertaintyText

record AntigravityGAuthorityAdmission : Set₁ where
  constructor antigravity-g-authority-admission
  field
    sourceEntitlement : NISTCODATA2022GSourceEntitlement

    normalizedToken : Numeric.NormalizedMeasuredAuthorityToken
    normalizedTokenIsG : normalizedToken ≡ Numeric.gNormalizedToken

    dimensionVector : Payload.SIBaseDimensionVector
    dimensionVectorIsNewtonianG :
      dimensionVector ≡ Payload.newtonianGDimensionVector

    parsedValueSI : ℚ
    parsedValueIsAuthorityG : parsedValueSI ≡ gValueSI

    parsedStandardUncertaintySI : ℚ
    parsedStandardUncertaintyIsAuthorityG :
      parsedStandardUncertaintySI ≡ gStandardUncertaintySI

    lowerSI : ℚ
    lowerIsAuthorityOneSigmaLower : lowerSI ≡ gLowerSI

    upperSI : ℚ
    upperIsAuthorityOneSigmaUpper : upperSI ≡ gUpperSI

    admittedForEinsteinCalibration : Bool
    admittedForEinsteinCalibrationIsTrue :
      admittedForEinsteinCalibration ≡ true

open AntigravityGAuthorityAdmission public

canonicalAntigravityGAuthorityAdmission : AntigravityGAuthorityAdmission
canonicalAntigravityGAuthorityAdmission =
  antigravity-g-authority-admission
    canonicalNISTCODATA2022GSourceEntitlement
    Numeric.gNormalizedToken
    refl
    Payload.newtonianGDimensionVector
    refl
    gValueSI
    refl
    gStandardUncertaintySI
    refl
    gLowerSI
    refl
    gUpperSI
    refl
    true
    refl

------------------------------------------------------------------------
-- ADAPTER INTO THE EXISTING PHYSICAL EINSTEIN-COUPLING ABI
--
-- The master ABI intentionally used abstract receipt types.  We instantiate
-- those slots with concrete source/value provenance objects rather than fresh
-- arbitrary Set tokens.
------------------------------------------------------------------------

record EnergyDensityConventionAdmission : Set where
  constructor energy-density-convention-admission
  field
    candidate : Einstein.EinsteinPhysicalCouplingCandidate
    candidateIsCanonical :
      candidate ≡ Einstein.canonicalEinsteinPhysicalCouplingCandidate

open EnergyDensityConventionAdmission public

canonicalEnergyDensityConventionAdmission : EnergyDensityConventionAdmission
canonicalEnergyDensityConventionAdmission =
  energy-density-convention-admission
    Einstein.canonicalEinsteinPhysicalCouplingCandidate refl

record KappaDiagnosticDefinitionAdmission : Set where
  constructor kappa-diagnostic-definition-admission
  field
    provenance : Physical.TypedKappaDiagnosticProvenance
    sourceGAdmission : AntigravityGAuthorityAdmission
    intervalIsCanonical :
      Physical.interval provenance ≡ Physical.codataCandidateKappaInterval

open KappaDiagnosticDefinitionAdmission public

canonicalKappaDiagnosticDefinitionAdmission :
  KappaDiagnosticDefinitionAdmission
canonicalKappaDiagnosticDefinitionAdmission =
  kappa-diagnostic-definition-admission
    Physical.canonicalTypedKappaDiagnosticProvenance
    canonicalAntigravityGAuthorityAdmission
    (Physical.intervalIsCanonical
      Physical.canonicalTypedKappaDiagnosticProvenance)

canonicalAcceptedPhysicalEinsteinCoupling :
  Physical.AcceptedPhysicalEinsteinCoupling
    Physical.codataCandidateKappaInterval
canonicalAcceptedPhysicalEinsteinCoupling = record
  { Physical.AcceptedPhysicalEinsteinCoupling.authorityCandidate =
      Einstein.canonicalEinsteinPhysicalCouplingCandidate
  ; Physical.AcceptedPhysicalEinsteinCoupling.AcceptedMeasuredAuthority =
      AntigravityGAuthorityAdmission
  ; Physical.AcceptedPhysicalEinsteinCoupling.acceptedMeasuredAuthority =
      canonicalAntigravityGAuthorityAdmission
  ; Physical.AcceptedPhysicalEinsteinCoupling.UncertaintyContained =
      KappaDiagnosticDefinitionAdmission
  ; Physical.AcceptedPhysicalEinsteinCoupling.uncertaintyContained =
      canonicalKappaDiagnosticDefinitionAdmission
  ; Physical.AcceptedPhysicalEinsteinCoupling.EnergyDensityConventionWeld =
      EnergyDensityConventionAdmission
  ; Physical.AcceptedPhysicalEinsteinCoupling.energyDensityConventionWeld =
      canonicalEnergyDensityConventionAdmission
  ; Physical.AcceptedPhysicalEinsteinCoupling.KappaDefinitionWeld =
      KappaDiagnosticDefinitionAdmission
  ; Physical.AcceptedPhysicalEinsteinCoupling.kappaDefinitionWeld =
      canonicalKappaDiagnosticDefinitionAdmission
  }

acceptedMeasuredGAuthorityPaid : Bool
acceptedMeasuredGAuthorityPaid = true

acceptedMeasuredGAuthorityStillRequired : Bool
acceptedMeasuredGAuthorityStillRequired = false

acceptedPhysicalEinsteinCouplingAvailable : Bool
acceptedPhysicalEinsteinCouplingAvailable = true

exactNewtonianGClaimedIsFalse : exactNewtonianGClaimed ≡ false
exactNewtonianGClaimedIsFalse = refl

acceptedMeasuredGAuthorityStillRequiredIsFalse :
  acceptedMeasuredGAuthorityStillRequired ≡ false
acceptedMeasuredGAuthorityStillRequiredIsFalse = refl
