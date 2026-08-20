module DASHI.Moonshine.P11TwoIsogenyFrobeniusNormalFormBridgeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Andrew P. Ogg,
-- "Automorphismes de courbes modulaires",
-- Seminaire Delange-Pisot-Poitou 16 (1974-1975), expose 7, pp. 1--8.
-- MR 417184; no DOI assigned.
--
-- Reinier Bröker, Kristin Lauter and Andrew V. Sutherland,
-- "Modular polynomials via isogeny volcanoes",
-- Mathematics of Computation 81 (2012), 1201--1231.
-- DOI: 10.1090/S0025-5718-2011-02508-1.
--
-- DASHI CONTRIBUTION
--
-- Cross-pollinate the new exact p=11 modular-polynomial correspondence with the
-- repository's existing finite Frobenius orbit normal form.
--
-- The existing modular/class-number scan gives p=11 orbit spectrum
--
--   fixed = 2, paired = 0, total = 2.
--
-- Hence its generic normal-form carrier is Fin 2.  The two modular-polynomial
-- labels {j0,j1} admit an explicit two-way chart to that normal form, and the
-- normal-form involution is pointwise identity.  Therefore the p=11 degree-two
-- correspondence is equivariant with that *normal-form* Frobenius action.
--
-- This does NOT upgrade the chart into a geometric supersingular realization:
-- proving that j0/j1 are exactly the geometric supersingular j-invariants and
-- that the normal-form involution is geometric Frobenius remains separate.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin; zero; suc)
open import Data.Sum using (inj₁; inj₂)

import DASHI.Foundations.FiniteInvolutionOrbitNormalFormExact as Orbit
import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix
import DASHI.Moonshine.SupersingularFrobeniusOrbitSpectrumExact as Frobenius
import DASHI.Moonshine.P11ClassicalTwoIsogenyCorrespondenceExact as P11

p11ExistingSpectrum : Orbit.InvolutionOrbitSpectrum
p11ExistingSpectrum = Frobenius.supersingularOrbitSpectrum Matrix.prime11

p11FixedCountIsTwo : Orbit.fixedOrbitCount p11ExistingSpectrum ≡ 2
p11FixedCountIsTwo = refl

p11PairedCountIsZero : Orbit.pairedOrbitCount p11ExistingSpectrum ≡ 0
p11PairedCountIsZero = refl

p11TotalCountIsTwo : Orbit.totalCarrierCount p11ExistingSpectrum ≡ 2
p11TotalCountIsTwo = refl

P11OrbitNormal : Set
P11OrbitNormal = Orbit.OrbitNormalFormCarrier 2 0

toNormal : P11.J11Class → P11OrbitNormal
toNormal P11.j0 = inj₁ zero
toNormal P11.j1 = inj₁ (suc zero)

fromNormal : P11OrbitNormal → P11.J11Class
fromNormal (inj₁ zero) = P11.j0
fromNormal (inj₁ (suc zero)) = P11.j1
fromNormal (inj₂ (() , bit))

fromAfterTo : (state : P11.J11Class) → fromNormal (toNormal state) ≡ state
fromAfterTo P11.j0 = refl
fromAfterTo P11.j1 = refl

toAfterFrom : (state : P11OrbitNormal) → toNormal (fromNormal state) ≡ state
toAfterFrom (inj₁ zero) = refl
toAfterFrom (inj₁ (suc zero)) = refl
toAfterFrom (inj₂ (() , bit))

p11NormalFrobeniusIsIdentity :
  (state : P11OrbitNormal) → Orbit.orbitInvolution state ≡ state
p11NormalFrobeniusIsIdentity (inj₁ zero) = refl
p11NormalFrobeniusIsIdentity (inj₁ (suc zero)) = refl
p11NormalFrobeniusIsIdentity (inj₂ (() , bit))

jClassNormalFrobenius : P11.J11Class → P11.J11Class
jClassNormalFrobenius state =
  fromNormal (Orbit.orbitInvolution (toNormal state))

jClassNormalFrobeniusIsIdentity :
  (state : P11.J11Class) → jClassNormalFrobenius state ≡ state
jClassNormalFrobeniusIsIdentity P11.j0 = refl
jClassNormalFrobeniusIsIdentity P11.j1 = refl

twoIsogenyCommutesWithNormalFrobenius :
  (state : P11.J11Class) →
  (edge : Fin 3) →
  jClassNormalFrobenius (P11.twoIsogenyNeighbour state edge)
  ≡
  P11.twoIsogenyNeighbour (jClassNormalFrobenius state) edge
twoIsogenyCommutesWithNormalFrobenius P11.j0 zero = refl
twoIsogenyCommutesWithNormalFrobenius P11.j0 (suc zero) = refl
twoIsogenyCommutesWithNormalFrobenius P11.j0 (suc (suc zero)) = refl
twoIsogenyCommutesWithNormalFrobenius P11.j1 zero = refl
twoIsogenyCommutesWithNormalFrobenius P11.j1 (suc zero) = refl
twoIsogenyCommutesWithNormalFrobenius P11.j1 (suc (suc zero)) = refl

record P11FrobeniusNormalFormBoundary : Set where
  field
    exactTwoFixedZeroPairedNormalFormUsed : Bool
    exactTwoFixedZeroPairedNormalFormUsedIsTrue :
      exactTwoFixedZeroPairedNormalFormUsed ≡ true

    twoWayFiniteCarrierChartConstructed : Bool
    twoWayFiniteCarrierChartConstructedIsTrue :
      twoWayFiniteCarrierChartConstructed ≡ true

    correspondenceNormalFormFrobeniusEquivariant : Bool
    correspondenceNormalFormFrobeniusEquivariantIsTrue :
      correspondenceNormalFormFrobeniusEquivariant ≡ true

    chartPromotedToGeometricSupersingularRealization : Bool
    chartPromotedToGeometricSupersingularRealizationIsFalse :
      chartPromotedToGeometricSupersingularRealization ≡ false

canonicalP11FrobeniusNormalFormBoundary : P11FrobeniusNormalFormBoundary
canonicalP11FrobeniusNormalFormBoundary =
  record
    { exactTwoFixedZeroPairedNormalFormUsed = true
    ; exactTwoFixedZeroPairedNormalFormUsedIsTrue = refl
    ; twoWayFiniteCarrierChartConstructed = true
    ; twoWayFiniteCarrierChartConstructedIsTrue = refl
    ; correspondenceNormalFormFrobeniusEquivariant = true
    ; correspondenceNormalFormFrobeniusEquivariantIsTrue = refl
    ; chartPromotedToGeometricSupersingularRealization = false
    ; chartPromotedToGeometricSupersingularRealizationIsFalse = refl
    }
