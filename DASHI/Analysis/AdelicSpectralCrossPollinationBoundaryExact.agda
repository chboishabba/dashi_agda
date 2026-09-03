module DASHI.Analysis.AdelicSpectralCrossPollinationBoundaryExact where

------------------------------------------------------------------------
-- CROSS-POLLINATION BOUNDARY
--
-- This module does not re-prove the external Lean theorems.  It records which
-- DASHI mechanisms they may legitimately feed and which identifications remain
-- forbidden without a same-object receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.NonArchimedeanSpectralOrbitHypervoxelExact as Spectral
import DASHI.Core.RelationalHypervoxelBraidCore as Hypervoxel
import DASHI.Interop.AdicHypervoxelArgumentTransportBridgeExact as AdicTransport
import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C3

------------------------------------------------------------------------
-- Phase/norm cross-pollination.
--
-- The external dyadic theorem and DASHI's C3 amplitude algebra live over
-- different cyclotomic carriers.  What cross-pollinates is the discipline:
-- preserve phase/conjugation information until the consumer explicitly asks
-- for a norm or fixed-field descent.
------------------------------------------------------------------------

record CyclotomicPhaseDisciplineBoundary : Set where
  constructor cyclotomicPhaseDisciplineBoundary
  field
    c3CarrierEqualsDyadicCarrier : Bool
    phaseBeforeNormDisciplineTransfers : Bool
    conjugatePairingBeforeScalarDescentTransfers : Bool
    numericCyclotomicIdentitiesTransferAcrossOrders : Bool

canonicalCyclotomicPhaseDisciplineBoundary : CyclotomicPhaseDisciplineBoundary
canonicalCyclotomicPhaseDisciplineBoundary =
  cyclotomicPhaseDisciplineBoundary false true true false

------------------------------------------------------------------------
-- Hypervoxel cross-pollination.
--
-- Orbit coordinate, local weight, return selector, orbit amplitude and trace
-- amplitude are treated as braided strands.  Their coexistence in one local
-- spectral cell does not make them definitionally equal.
------------------------------------------------------------------------

record SpectralHypervoxelBoundary : Set where
  constructor spectralHypervoxelBoundary
  field
    orbitIsWeight : Bool
    weightIsTrace : Bool
    returnSupportIsAmplitude : Bool
    strandsMayBeRecombinedByTypedConsumer : Bool
    braidDisciplineTransfers : Bool

canonicalSpectralHypervoxelBoundary : SpectralHypervoxelBoundary
canonicalSpectralHypervoxelBoundary =
  spectralHypervoxelBoundary false false false true true

------------------------------------------------------------------------
-- Adic refinement transport cross-pollination.
--
-- DASHI already treats an adic refinement as a typed source-target transport
-- and explicitly rejects projected-shadow = definitional-identity.  The same
-- discipline is used here for character-space -> spatial-block transport.
------------------------------------------------------------------------

record CharacterSpatialTransportBoundary : Set where
  constructor characterSpatialTransportBoundary
  field
    changeOfChartMayPreserveSpectrum : Bool
    chartChangeCreatesSameObjectReceiptAutomatically : Bool
    sourceTargetTransportMustRemainExplicit : Bool
    projectedAnalogyMayReplaceUnitaryIntertwiner : Bool

canonicalCharacterSpatialTransportBoundary : CharacterSpatialTransportBoundary
canonicalCharacterSpatialTransportBoundary =
  characterSpatialTransportBoundary true false true false

------------------------------------------------------------------------
-- Cross-domain consequences that are safe to export.
------------------------------------------------------------------------

record SafeCrossPollinationExport : Set where
  constructor safeCrossPollinationExport
  field
    signedCancellationBeforeNorm : Bool
    supportBeforeAmplitude : Bool
    returnSelectorBeforeTrace : Bool
    refinementNeedsTypedTransport : Bool
    cyclotomicOrderMustRemainIndexed : Bool
    analogyDoesNotCreateIdentity : Bool

canonicalSafeCrossPollinationExport : SafeCrossPollinationExport
canonicalSafeCrossPollinationExport =
  safeCrossPollinationExport true true true true true true

phaseCarrierNonIdentityIsCanonical :
  CyclotomicPhaseDisciplineBoundary.c3CarrierEqualsDyadicCarrier
    canonicalCyclotomicPhaseDisciplineBoundary
  ≡ false
phaseCarrierNonIdentityIsCanonical = refl

supportAmplitudeNonCollapseIsCanonical :
  SpectralHypervoxelBoundary.returnSupportIsAmplitude
    canonicalSpectralHypervoxelBoundary
  ≡ false
supportAmplitudeNonCollapseIsCanonical = refl

sameObjectTransportIsFailClosed :
  CharacterSpatialTransportBoundary.chartChangeCreatesSameObjectReceiptAutomatically
    canonicalCharacterSpatialTransportBoundary
  ≡ false
sameObjectTransportIsFailClosed = refl
