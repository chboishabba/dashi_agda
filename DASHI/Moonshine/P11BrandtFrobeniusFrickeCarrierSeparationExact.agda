module DASHI.Moonshine.P11BrandtFrobeniusFrickeCarrierSeparationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John Voight,
-- "Quaternion Algebras", Graduate Texts in Mathematics 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
-- Chapter 42, "Supersingular elliptic curves".
-- DOI: 10.1007/978-3-030-56694-4_42.
--
-- Joseph H. Silverman,
-- "The Arithmetic of Elliptic Curves", 2nd ed., Springer, 2009.
-- DOI: 10.1007/978-0-387-09494-6.
--
-- Andrew P. Ogg,
-- "Automorphismes de courbes modulaires",
-- Seminaire Delange-Pisot-Poitou 16 (1974-1975), expose 7.
-- MR 417184; no DOI asserted.
--
-- John F. R. Duncan and Ken Ono,
-- "The Jack Daniels Problem", Journal of Number Theory 161 (2016), 230--239.
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- DASHI CONTRIBUTION
--
-- Put the p=11 Hecke/Frobenius and Fricke data next to each other without
-- forcing them onto the same carrier.
--
-- The source-certified supersingular Brandt carrier has exactly the two
-- j-classes 0 and 1728=1 mod 11.  Both are F_11-rational, so the geometric
-- Frobenius action on this j-class carrier is pointwise identity.  Consequently
-- the already-constructed positive T2,T3,T5 neighbour correspondences commute
-- with Frobenius definitionally.
--
-- By contrast, the independently constructed Fricke row for X_0(11) has FOUR
-- Fricke fixed points.  Therefore those four modular-curve fixed points cannot
-- literally be identified with the fixed points of a self-involution on the
-- two-element Brandt j-class carrier.  The correct joint architecture is
-- braided/multi-carrier: Hecke+Frobenius on supersingular/ideal classes, Fricke
-- on the modular-curve carrier, with explicit bridges rather than carrier
-- identity.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin)

import DASHI.Moonshine.P11GeometricSupersingularCarrierExact as Geo
import DASHI.Moonshine.P11PositiveBrandtNeighbourSystemsExact as Brandt
import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix
import DASHI.Moonshine.PrimeFrickeGenusControlExact as Fricke

------------------------------------------------------------------------
-- Source-certified p=11 Frobenius on supersingular j-classes.
------------------------------------------------------------------------

p11GeometricFrobenius : Geo.P11SupersingularJ → Geo.P11SupersingularJ
p11GeometricFrobenius Geo.jZeroSS = Geo.jZeroSS
p11GeometricFrobenius Geo.j1728SS = Geo.j1728SS

p11FrobeniusIsIdentity :
  (j : Geo.P11SupersingularJ) → p11GeometricFrobenius j ≡ j
p11FrobeniusIsIdentity Geo.jZeroSS = refl
p11FrobeniusIsIdentity Geo.j1728SS = refl

p11FrobeniusInvolutive :
  (j : Geo.P11SupersingularJ) →
  p11GeometricFrobenius (p11GeometricFrobenius j) ≡ j
p11FrobeniusInvolutive Geo.jZeroSS = refl
p11FrobeniusInvolutive Geo.j1728SS = refl

identityFrobeniusCommutesWithNeighbour :
  ∀ {Edge : Set}
    (neighbour : Geo.P11SupersingularJ → Edge → Geo.P11SupersingularJ)
    (j : Geo.P11SupersingularJ)
    (edge : Edge) →
  p11GeometricFrobenius (neighbour j edge)
  ≡ neighbour (p11GeometricFrobenius j) edge
identityFrobeniusCommutesWithNeighbour neighbour Geo.jZeroSS edge = refl
identityFrobeniusCommutesWithNeighbour neighbour Geo.j1728SS edge = refl

p11T2CommutesWithFrobenius :
  (j : Geo.P11SupersingularJ) → (edge : Fin 3) →
  p11GeometricFrobenius (Brandt.ell2Neighbour j edge)
  ≡ Brandt.ell2Neighbour (p11GeometricFrobenius j) edge
p11T2CommutesWithFrobenius =
  identityFrobeniusCommutesWithNeighbour Brandt.ell2Neighbour

p11T3CommutesWithFrobenius :
  (j : Geo.P11SupersingularJ) → (edge : Fin 4) →
  p11GeometricFrobenius (Brandt.ell3Neighbour j edge)
  ≡ Brandt.ell3Neighbour (p11GeometricFrobenius j) edge
p11T3CommutesWithFrobenius =
  identityFrobeniusCommutesWithNeighbour Brandt.ell3Neighbour

p11T5CommutesWithFrobenius :
  (j : Geo.P11SupersingularJ) → (edge : Fin 6) →
  p11GeometricFrobenius (Brandt.ell5Neighbour j edge)
  ≡ Brandt.ell5Neighbour (p11GeometricFrobenius j) edge
p11T5CommutesWithFrobenius =
  identityFrobeniusCommutesWithNeighbour Brandt.ell5Neighbour

------------------------------------------------------------------------
-- Fricke lives on a different geometric carrier.
------------------------------------------------------------------------

p11BrandtJClassCount : Nat
p11BrandtJClassCount = 2

p11FrickeFixedPointCount : Nat
p11FrickeFixedPointCount =
  Fricke.frickeFixedPointCount (Fricke.frickeRow Matrix.prime11)

p11FrickeFixedPointCountIsFour : p11FrickeFixedPointCount ≡ 4
p11FrickeFixedPointCountIsFour = refl

p11BrandtJClassCountIsTwo : p11BrandtJClassCount ≡ 2
p11BrandtJClassCountIsTwo = refl

record P11SameCarrierFrickeIdentification : Set where
  field
    allFrickeFixedPointsAreExactlyBrandtJClasses :
      p11FrickeFixedPointCount ≡ p11BrandtJClassCount

sameCarrierFrickeIdentificationImpossible :
  P11SameCarrierFrickeIdentification → ⊥
sameCarrierFrickeIdentificationImpossible record
  { allFrickeFixedPointsAreExactlyBrandtJClasses = () }

record P11BrandtFrobeniusFrickeBoundary : Set where
  field
    sourceCertifiedBrandtCarrierUsed : Bool
    sourceCertifiedBrandtCarrierUsedIsTrue :
      sourceCertifiedBrandtCarrierUsed ≡ true

    frobeniusOnBrandtJClassesConstructed : Bool
    frobeniusOnBrandtJClassesConstructedIsTrue :
      frobeniusOnBrandtJClassesConstructed ≡ true

    t2t3t5FrobeniusEquivarianceConstructed : Bool
    t2t3t5FrobeniusEquivarianceConstructedIsTrue :
      t2t3t5FrobeniusEquivarianceConstructed ≡ true

    frickeFixedPointsIdentifiedWithBrandtCarrier : Bool
    frickeFixedPointsIdentifiedWithBrandtCarrierIsFalse :
      frickeFixedPointsIdentifiedWithBrandtCarrier ≡ false

    braidedMultiCarrierArchitectureRequired : Bool
    braidedMultiCarrierArchitectureRequiredIsTrue :
      braidedMultiCarrierArchitectureRequired ≡ true

canonicalP11BrandtFrobeniusFrickeBoundary : P11BrandtFrobeniusFrickeBoundary
canonicalP11BrandtFrobeniusFrickeBoundary = record
  { sourceCertifiedBrandtCarrierUsed = true
  ; sourceCertifiedBrandtCarrierUsedIsTrue = refl
  ; frobeniusOnBrandtJClassesConstructed = true
  ; frobeniusOnBrandtJClassesConstructedIsTrue = refl
  ; t2t3t5FrobeniusEquivarianceConstructed = true
  ; t2t3t5FrobeniusEquivarianceConstructedIsTrue = refl
  ; frickeFixedPointsIdentifiedWithBrandtCarrier = false
  ; frickeFixedPointsIdentifiedWithBrandtCarrierIsFalse = refl
  ; braidedMultiCarrierArchitectureRequired = true
  ; braidedMultiCarrierArchitectureRequiredIsTrue = refl
  }
