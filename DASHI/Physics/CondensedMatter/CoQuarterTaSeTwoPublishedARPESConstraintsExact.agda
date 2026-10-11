module DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoPublishedARPESConstraintsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- PUBLISHED ARPES CONSTRAINT SURFACE
--
-- Source:
--   Sprague et al., Nature Communications (2026)
--   DOI 10.1038/s41467-026-76784-x
--   arXiv:2508.12985
--
-- These values are literal publication-summary targets.  They are not a raw
-- Igor-wave observer, not a figure digitisation and not an independently
-- reproduced material Hamiltonian.
------------------------------------------------------------------------

record PublishedARPESConstraints : Set where
  constructor published-arpes-constraints
  field
    sourceDOI : String
    lowTemperatureK : Nat
    highTemperatureK : Nat
    neelTemperatureK : Nat
    energyResolutionMeV : Nat
    angularResolutionTenthDegree : Nat
    mdcIntegrationHalfWindowMeV : Nat
    photonEnergySplitPlaneEV : Nat
    photonEnergyIntermediateEV : Nat
    photonEnergyNodalPlaneEV : Nat
    dftFermiCrossingSeparationMilliInverseAngstrom : Nat
    voigtPeakSeparationMilliInverseAngstrom : Nat
    instrumentalGaussianWidthMilliInverseAngstrom : Nat
    gammaPrimeKPrimeDegenerateReported : Bool
    gammaPrimeMPrimeSplitReported : Bool
    kzZeroNodalReported : Bool
    kzPiNodalReported : Bool
    lowTemperatureTwoPeakReported : Bool
    highTemperatureNarrowerSpectrumReported : Bool

open PublishedARPESConstraints public

canonicalPublishedARPESConstraints : PublishedARPESConstraints
canonicalPublishedARPESConstraints =
  published-arpes-constraints
    "10.1038/s41467-026-76784-x"
    7
    200
    178
    20
    1
    13
    55
    51
    48
    10
    90
    80
    true true true true true true

------------------------------------------------------------------------
-- Non-collapse / measurement-role boundary.
------------------------------------------------------------------------

record PublishedConstraintPromotionBoundary : Set where
  constructor published-constraint-promotion-boundary
  field
    sourceSummaryIsRawIntensityArray : Bool
    sourceVoigtFitIsRawSpectrum : Bool
    dftCrossingSeparationEqualsVoigtPeakSeparation : Bool
    sourceReportedAgreementConstructsHamiltonian : Bool
    sourceReportedAgreementConstructsSpectralObserver : Bool
    rawIgorStillRequiredForLiteralObserver : Bool
    electronicStructureArtifactStillRequiredForMaterialH : Bool

canonicalPublishedConstraintPromotionBoundary :
  PublishedConstraintPromotionBoundary
canonicalPublishedConstraintPromotionBoundary =
  published-constraint-promotion-boundary
    false false false false false true true

------------------------------------------------------------------------
-- Current payment status.  The publication target is now explicit enough to
-- test a future same-object producer without fabricating the producer itself.
------------------------------------------------------------------------

record PublishedTargetStatus : Set where
  constructor published-target-status
  field
    temperatureOrderingTargetPinned : Bool
    photonEnergyKzTargetsPinned : Bool
    directionalNodalSplitTargetsPinned : Bool
    mdcFitTargetPinned : Bool
    instrumentalResolutionTargetPinned : Bool
    rawIntensityTargetClosed : Bool
    materialHamiltonianTargetClosed : Bool
    quantitativeRawDataFitClosed : Bool

canonicalPublishedTargetStatus : PublishedTargetStatus
canonicalPublishedTargetStatus =
  published-target-status
    true true true true true
    false false false
