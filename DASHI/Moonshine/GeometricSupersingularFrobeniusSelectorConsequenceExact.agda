module DASHI.Moonshine.GeometricSupersingularFrobeniusSelectorConsequenceExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Andrew P. Ogg,
-- "Automorphismes de courbes modulaires",
-- Seminaire Delange-Pisot-Poitou 16 (1974-1975), expose 7,
-- MR 417184; no DOI asserted.
--
-- John F. R. Duncan and Ken Ono,
-- "The Jack Daniels Problem", Journal of Number Theory 161 (2016), 230--239.
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
-- Finite involution orbit decomposition context.
--
-- DASHI CONTRIBUTION
--
-- SupersingularFrobeniusOrbitSpectrumExact already computes, on the exact
-- odd-prime control carrier under 72,
--
--   pairedOrbitCount = g(X0+(p))
--
-- and packages the missing geometric producer as an
-- `InvolutionNormalFormRealization` from an ACTUAL supersingular/Frobenius
-- carrier to the fixed+paired normal form.
--
-- This file proves all downstream selector consequences from that one
-- realization witness.  If R is an actual Frobenius-equivariant normal-form
-- realization, then
--
--   geometric Frobenius is pointwise identity
--     <=> pairedOrbitCount = 0
--     <=> g(X0+(p)) = 0.
--
-- On the existing finite control scan this is moreover equivalent to the
-- external Ogg label.  Thus once a source-native geometric realization is
-- built for a prime, NO additional selector theorem is required.
--
-- IMPORTANT AUTHORITY BOUNDARY
-- This module does not manufacture such a realization.  p=11,p=37,p=43 have
-- source-facing realizations elsewhere in the live arithmetic branch; the
-- all-prime realization remains the genuine geometric producer.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin; zero)
open import Data.Sum using (inj₁; inj₂)

import DASHI.Foundations.FiniteInvolutionOrbitNormalFormExact as Orbit
import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix
import DASHI.Moonshine.PrimeFrickeGenusControlExact as Fricke
import DASHI.Moonshine.SupersingularFrobeniusOrbitSpectrumExact as Spectrum

------------------------------------------------------------------------
-- Geometric pointwise fixedness on an actual carrier.
------------------------------------------------------------------------

GeometricallyFullyFixed :
  {prime : Matrix.OddPrimeCandidateUnder72} →
  (carrier : Spectrum.SupersingularFrobeniusCarrier prime) → Set
GeometricallyFullyFixed carrier =
  (x : Spectrum.Carrier carrier) →
  Spectrum.frobenius carrier x ≡ x

------------------------------------------------------------------------
-- Generic realization theorem: pointwise fixed iff there are no paired orbits.
------------------------------------------------------------------------

realizationNoPairsImpliesAllFixed :
  {prime : Matrix.OddPrimeCandidateUnder72} →
  (carrier : Spectrum.SupersingularFrobeniusCarrier prime) →
  (R : Spectrum.SupersingularFrobeniusNormalFormRealization prime carrier) →
  Orbit.pairedOrbitCount (Spectrum.supersingularOrbitSpectrum prime) ≡ 0 →
  GeometricallyFullyFixed carrier
realizationNoPairsImpliesAllFixed {prime} carrier R pairZero x
  with Orbit.toNormal (Spectrum.realization R) x
... | inj₁ fixedIndex =
  let
    realization = Spectrum.realization R
    fxNormal :
      Orbit.toNormal realization (Spectrum.frobenius carrier x)
      ≡ Orbit.toNormal realization x
    fxNormal =
      trans
        (Orbit.intertwinesInvolution realization x)
        (trans
          (cong Orbit.orbitInvolution refl)
          refl)
  in
  trans
    (sym (Orbit.fromAfterTo realization (Spectrum.frobenius carrier x)))
    (trans
      (cong (Orbit.fromNormal realization)
        (trans
          (Orbit.intertwinesInvolution realization x)
          (Orbit.fixedSummandReallyFixed fixedIndex)))
      (Orbit.fromAfterTo realization x))
... | inj₂ (pairIndex , bit) with pairZero
... | ()

-- If even one paired normal-form orbit exists, pull one of its points back to
-- the geometric carrier.  Pointwise geometric fixedness would force the
-- fixed-point-free bit flip to have a fixed point.
realizationAllFixedImpliesNoPairs :
  {prime : Matrix.OddPrimeCandidateUnder72} →
  (carrier : Spectrum.SupersingularFrobeniusCarrier prime) →
  (R : Spectrum.SupersingularFrobeniusNormalFormRealization prime carrier) →
  GeometricallyFullyFixed carrier →
  Orbit.pairedOrbitCount (Spectrum.supersingularOrbitSpectrum prime) ≡ 0
realizationAllFixedImpliesNoPairs {prime} carrier R allFixed
  with Orbit.pairedOrbitCount (Spectrum.supersingularOrbitSpectrum prime)
... | zero = refl
... | suc paired =
  let
    realization = Spectrum.realization R
    normalPoint = inj₂ (zero , Orbit.bit0)
    x = Orbit.fromNormal realization normalPoint

    geometricFixed : Spectrum.frobenius carrier x ≡ x
    geometricFixed = allFixed x

    normalFixed : Orbit.orbitInvolution normalPoint ≡ normalPoint
    normalFixed =
      trans
        (sym (Orbit.intertwinesInvolution realization x))
        (trans
          (cong (Orbit.toNormal realization) geometricFixed)
          (Orbit.toAfterFrom realization normalPoint))
  in
  ⊥-elim (Orbit.pairedSummandHasNoFixedPoint zero Orbit.bit0 normalFixed)

------------------------------------------------------------------------
-- Since pairedOrbitCount is DEFINITIONALLY genusX0Plus in the spectrum, the
-- geometric theorem immediately becomes the desired genus statement.
------------------------------------------------------------------------

realizationGenusZeroImpliesAllFixed :
  {prime : Matrix.OddPrimeCandidateUnder72} →
  (carrier : Spectrum.SupersingularFrobeniusCarrier prime) →
  (R : Spectrum.SupersingularFrobeniusNormalFormRealization prime carrier) →
  Fricke.genusX0Plus (Fricke.frickeRow prime) ≡ 0 →
  GeometricallyFullyFixed carrier
realizationGenusZeroImpliesAllFixed carrier R genusZero =
  realizationNoPairsImpliesAllFixed carrier R genusZero

realizationAllFixedImpliesGenusZero :
  {prime : Matrix.OddPrimeCandidateUnder72} →
  (carrier : Spectrum.SupersingularFrobeniusCarrier prime) →
  (R : Spectrum.SupersingularFrobeniusNormalFormRealization prime carrier) →
  GeometricallyFullyFixed carrier →
  Fricke.genusX0Plus (Fricke.frickeRow prime) ≡ 0
realizationAllFixedImpliesGenusZero = realizationAllFixedImpliesNoPairs

------------------------------------------------------------------------
-- Boolean bridge to the existing Ogg control label.
------------------------------------------------------------------------

noPairsImpliesFullyFixedTrue :
  (spectrum : Orbit.InvolutionOrbitSpectrum) →
  Orbit.pairedOrbitCount spectrum ≡ 0 →
  Orbit.fullyFixed spectrum ≡ true
noPairsImpliesFullyFixedTrue spectrum pairZero
  rewrite pairZero = refl

fullyFixedTrueImpliesNoPairs :
  (spectrum : Orbit.InvolutionOrbitSpectrum) →
  Orbit.fullyFixed spectrum ≡ true →
  Orbit.pairedOrbitCount spectrum ≡ 0
fullyFixedTrueImpliesNoPairs spectrum fullyTrue
  with Orbit.pairedOrbitCount spectrum
... | zero = refl
... | suc _ = ⊥-elim (falseIsNotTrue fullyTrue)
  where
  falseIsNotTrue : false ≡ true → ⊥
  falseIsNotTrue ()

realizationExternalOggImpliesAllFixed :
  {prime : Matrix.OddPrimeCandidateUnder72} →
  (carrier : Spectrum.SupersingularFrobeniusCarrier prime) →
  (R : Spectrum.SupersingularFrobeniusNormalFormRealization prime carrier) →
  Matrix.externalOggLabel prime ≡ true →
  GeometricallyFullyFixed carrier
realizationExternalOggImpliesAllFixed {prime} carrier R externalTrue =
  realizationNoPairsImpliesAllFixed carrier R
    (fullyFixedTrueImpliesNoPairs
      (Spectrum.supersingularOrbitSpectrum prime)
      (trans (Spectrum.allFixedMatchesExternalOgg prime) externalTrue))

realizationAllFixedImpliesExternalOgg :
  {prime : Matrix.OddPrimeCandidateUnder72} →
  (carrier : Spectrum.SupersingularFrobeniusCarrier prime) →
  (R : Spectrum.SupersingularFrobeniusNormalFormRealization prime carrier) →
  GeometricallyFullyFixed carrier →
  Matrix.externalOggLabel prime ≡ true
realizationAllFixedImpliesExternalOgg {prime} carrier R allFixed =
  let
    noPairs = realizationAllFixedImpliesNoPairs carrier R allFixed
    fullyTrue = noPairsImpliesFullyFixedTrue
      (Spectrum.supersingularOrbitSpectrum prime) noPairs
  in
  trans
    (sym (Spectrum.allFixedMatchesExternalOgg prime))
    fullyTrue

record GeometricSupersingularFrobeniusSelectorBoundary : Set where
  field
    realizationAllFixedIffNoPairsProved : Bool
    realizationAllFixedIffGenusZeroProved : Bool
    realizationAllFixedIffExternalOggOnControlScanProved : Bool
    downstreamSelectorAlgebraStillMissingAfterRealization : Bool
    allPrimeGeometricRealizationConstructedHere : Bool

canonicalGeometricSupersingularFrobeniusSelectorBoundary :
  GeometricSupersingularFrobeniusSelectorBoundary
canonicalGeometricSupersingularFrobeniusSelectorBoundary = record
  { realizationAllFixedIffNoPairsProved = true
  ; realizationAllFixedIffGenusZeroProved = true
  ; realizationAllFixedIffExternalOggOnControlScanProved = true
  ; downstreamSelectorAlgebraStillMissingAfterRealization = false
  ; allPrimeGeometricRealizationConstructedHere = false
  }
