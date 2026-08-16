module DASHI.Moonshine.SupersingularFrobeniusOrbitSpectrumExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / AUTHORITY
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
-- DASHI CONTRIBUTION
--
-- Repackage the exact finite Fricke/class-number control data as an involution
-- orbit spectrum.  For the odd-prime scan define
--
--   total supersingular slots   = g(X0(p)) + 1,
--   rational/fixed slots        = r_p / 2,
--   conjugate Frobenius pairs   = g(X0+(p)).
--
-- The already-checked Riemann-Hurwitz rows become exactly
--
--   total = fixed + 2 * paired.
--
-- Thus the modular defect g(X0+(p)) is literally the number of nontrivial
-- two-orbits in this normalized C2 orbit spectrum.  The finite scan is fully
-- fixed exactly on the odd Ogg locus.
--
-- IMPORTANT AUTHORITY BOUNDARY:
-- this module constructs the *normal-form orbit spectrum* from exact finite
-- modular counts.  It does not internally construct supersingular elliptic
-- curves, geometric Frobenius, or a bijection from actual supersingular
-- j-invariants to these normal-form slots.  Such a realization is separately
-- typed below and remains unconstructed here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Foundations.FiniteInvolutionOrbitNormalFormExact as Orbit
import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix
import DASHI.Moonshine.PrimeFrickeGenusControlExact as Fricke
import DASHI.Moonshine.PrimeFrickeOrbitSaturationExact as Saturation

rationalSupersingularCount : Matrix.OddPrimeCandidateUnder72 → Nat
rationalSupersingularCount Matrix.prime3 = 1
rationalSupersingularCount Matrix.prime5 = 1
rationalSupersingularCount Matrix.prime7 = 1
rationalSupersingularCount Matrix.prime11 = 2
rationalSupersingularCount Matrix.prime13 = 1
rationalSupersingularCount Matrix.prime17 = 2
rationalSupersingularCount Matrix.prime19 = 2
rationalSupersingularCount Matrix.prime23 = 3
rationalSupersingularCount Matrix.prime29 = 3
rationalSupersingularCount Matrix.prime31 = 3
rationalSupersingularCount Matrix.prime37 = 1
rationalSupersingularCount Matrix.prime41 = 4
rationalSupersingularCount Matrix.prime43 = 2
rationalSupersingularCount Matrix.prime47 = 5
rationalSupersingularCount Matrix.prime53 = 3
rationalSupersingularCount Matrix.prime59 = 6
rationalSupersingularCount Matrix.prime61 = 3
rationalSupersingularCount Matrix.prime67 = 2
rationalSupersingularCount Matrix.prime71 = 7

rationalCountDoublesToFrickeFixedPoints :
  (prime : Matrix.OddPrimeCandidateUnder72) →
  2 * rationalSupersingularCount prime
  ≡ Fricke.frickeFixedPointCount (Fricke.frickeRow prime)
rationalCountDoublesToFrickeFixedPoints Matrix.prime3 = refl
rationalCountDoublesToFrickeFixedPoints Matrix.prime5 = refl
rationalCountDoublesToFrickeFixedPoints Matrix.prime7 = refl
rationalCountDoublesToFrickeFixedPoints Matrix.prime11 = refl
rationalCountDoublesToFrickeFixedPoints Matrix.prime13 = refl
rationalCountDoublesToFrickeFixedPoints Matrix.prime17 = refl
rationalCountDoublesToFrickeFixedPoints Matrix.prime19 = refl
rationalCountDoublesToFrickeFixedPoints Matrix.prime23 = refl
rationalCountDoublesToFrickeFixedPoints Matrix.prime29 = refl
rationalCountDoublesToFrickeFixedPoints Matrix.prime31 = refl
rationalCountDoublesToFrickeFixedPoints Matrix.prime37 = refl
rationalCountDoublesToFrickeFixedPoints Matrix.prime41 = refl
rationalCountDoublesToFrickeFixedPoints Matrix.prime43 = refl
rationalCountDoublesToFrickeFixedPoints Matrix.prime47 = refl
rationalCountDoublesToFrickeFixedPoints Matrix.prime53 = refl
rationalCountDoublesToFrickeFixedPoints Matrix.prime59 = refl
rationalCountDoublesToFrickeFixedPoints Matrix.prime61 = refl
rationalCountDoublesToFrickeFixedPoints Matrix.prime67 = refl
rationalCountDoublesToFrickeFixedPoints Matrix.prime71 = refl

totalSupersingularCount : Matrix.OddPrimeCandidateUnder72 → Nat
totalSupersingularCount prime =
  Fricke.genusX0 (Fricke.frickeRow prime) + 1

frobeniusTwoOrbitCount : Matrix.OddPrimeCandidateUnder72 → Nat
frobeniusTwoOrbitCount prime =
  Fricke.genusX0Plus (Fricke.frickeRow prime)

supersingularOrbitCountExact :
  (prime : Matrix.OddPrimeCandidateUnder72) →
  totalSupersingularCount prime
  ≡ rationalSupersingularCount prime
    + 2 * frobeniusTwoOrbitCount prime
supersingularOrbitCountExact Matrix.prime3 = refl
supersingularOrbitCountExact Matrix.prime5 = refl
supersingularOrbitCountExact Matrix.prime7 = refl
supersingularOrbitCountExact Matrix.prime11 = refl
supersingularOrbitCountExact Matrix.prime13 = refl
supersingularOrbitCountExact Matrix.prime17 = refl
supersingularOrbitCountExact Matrix.prime19 = refl
supersingularOrbitCountExact Matrix.prime23 = refl
supersingularOrbitCountExact Matrix.prime29 = refl
supersingularOrbitCountExact Matrix.prime31 = refl
supersingularOrbitCountExact Matrix.prime37 = refl
supersingularOrbitCountExact Matrix.prime41 = refl
supersingularOrbitCountExact Matrix.prime43 = refl
supersingularOrbitCountExact Matrix.prime47 = refl
supersingularOrbitCountExact Matrix.prime53 = refl
supersingularOrbitCountExact Matrix.prime59 = refl
supersingularOrbitCountExact Matrix.prime61 = refl
supersingularOrbitCountExact Matrix.prime67 = refl
supersingularOrbitCountExact Matrix.prime71 = refl

supersingularOrbitSpectrum :
  Matrix.OddPrimeCandidateUnder72 → Orbit.InvolutionOrbitSpectrum
supersingularOrbitSpectrum prime =
  Orbit.involution-orbit-spectrum
    (rationalSupersingularCount prime)
    (frobeniusTwoOrbitCount prime)
    (totalSupersingularCount prime)
    (supersingularOrbitCountExact prime)

allSupersingularSlotsFixed : Matrix.OddPrimeCandidateUnder72 → Bool
allSupersingularSlotsFixed prime =
  Orbit.fullyFixed (supersingularOrbitSpectrum prime)

allFixedMatchesFrickeSaturation :
  (prime : Matrix.OddPrimeCandidateUnder72) →
  allSupersingularSlotsFixed prime ≡ Saturation.frickeOrbitSaturated prime
allFixedMatchesFrickeSaturation Matrix.prime3 = refl
allFixedMatchesFrickeSaturation Matrix.prime5 = refl
allFixedMatchesFrickeSaturation Matrix.prime7 = refl
allFixedMatchesFrickeSaturation Matrix.prime11 = refl
allFixedMatchesFrickeSaturation Matrix.prime13 = refl
allFixedMatchesFrickeSaturation Matrix.prime17 = refl
allFixedMatchesFrickeSaturation Matrix.prime19 = refl
allFixedMatchesFrickeSaturation Matrix.prime23 = refl
allFixedMatchesFrickeSaturation Matrix.prime29 = refl
allFixedMatchesFrickeSaturation Matrix.prime31 = refl
allFixedMatchesFrickeSaturation Matrix.prime37 = refl
allFixedMatchesFrickeSaturation Matrix.prime41 = refl
allFixedMatchesFrickeSaturation Matrix.prime43 = refl
allFixedMatchesFrickeSaturation Matrix.prime47 = refl
allFixedMatchesFrickeSaturation Matrix.prime53 = refl
allFixedMatchesFrickeSaturation Matrix.prime59 = refl
allFixedMatchesFrickeSaturation Matrix.prime61 = refl
allFixedMatchesFrickeSaturation Matrix.prime67 = refl
allFixedMatchesFrickeSaturation Matrix.prime71 = refl

allFixedMatchesExternalOgg :
  (prime : Matrix.OddPrimeCandidateUnder72) →
  allSupersingularSlotsFixed prime ≡ Matrix.externalOggLabel prime
allFixedMatchesExternalOgg prime =
  trans
    (allFixedMatchesFrickeSaturation prime)
    (Saturation.saturationMatchesExternalOgg prime)

------------------------------------------------------------------------
-- Concrete non-Ogg orbit spectra.
------------------------------------------------------------------------

prime37OrbitSpectrum :
  supersingularOrbitSpectrum Matrix.prime37
  ≡ Orbit.involution-orbit-spectrum 1 1 3 refl
prime37OrbitSpectrum = refl

prime43OrbitSpectrum :
  supersingularOrbitSpectrum Matrix.prime43
  ≡ Orbit.involution-orbit-spectrum 2 1 4 refl
prime43OrbitSpectrum = refl

prime53OrbitSpectrum :
  supersingularOrbitSpectrum Matrix.prime53
  ≡ Orbit.involution-orbit-spectrum 3 1 5 refl
prime53OrbitSpectrum = refl

prime61OrbitSpectrum :
  supersingularOrbitSpectrum Matrix.prime61
  ≡ Orbit.involution-orbit-spectrum 3 1 5 refl
prime61OrbitSpectrum = refl

prime67OrbitSpectrum :
  supersingularOrbitSpectrum Matrix.prime67
  ≡ Orbit.involution-orbit-spectrum 2 2 6 refl
prime67OrbitSpectrum = refl

prime71OrbitSpectrum :
  supersingularOrbitSpectrum Matrix.prime71
  ≡ Orbit.involution-orbit-spectrum 7 0 7 refl
prime71OrbitSpectrum = refl

------------------------------------------------------------------------
-- Actual geometric Frobenius realization target.
------------------------------------------------------------------------

record SupersingularFrobeniusCarrier
    (prime : Matrix.OddPrimeCandidateUnder72) : Set₁ where
  field
    Carrier : Set
    frobenius : Carrier → Carrier
    frobeniusInvolutive :
      (x : Carrier) → frobenius (frobenius x) ≡ x
    carrierReceipt : String

open SupersingularFrobeniusCarrier public

record SupersingularFrobeniusNormalFormRealization
    (prime : Matrix.OddPrimeCandidateUnder72)
    (carrier : SupersingularFrobeniusCarrier prime) : Set₁ where
  field
    realization :
      Orbit.InvolutionNormalFormRealization
        (Carrier carrier)
        (frobenius carrier)
        (supersingularOrbitSpectrum prime)
    realizationReceipt : String

open SupersingularFrobeniusNormalFormRealization public

data ConstructedGeometricFrobeniusRealization : Set where

noGeometricFrobeniusRealizationConstructedHere :
  ConstructedGeometricFrobeniusRealization → ⊥
noGeometricFrobeniusRealizationConstructedHere ()

record SupersingularFrobeniusOrbitBoundary : Set where
  field
    finiteOrbitSpectrumConstructed : Bool
    finiteOrbitSpectrumConstructedIsTrue :
      finiteOrbitSpectrumConstructed ≡ true

    twoOrbitDefectEqualsFrickePlusGenus : Bool
    twoOrbitDefectEqualsFrickePlusGenusIsTrue :
      twoOrbitDefectEqualsFrickePlusGenus ≡ true

    fullyFixedSpectrumMatchesOggOnFiniteScan : Bool
    fullyFixedSpectrumMatchesOggOnFiniteScanIsTrue :
      fullyFixedSpectrumMatchesOggOnFiniteScan ≡ true

    actualSupersingularEllipticCurveCarrierConstructed : Bool
    actualSupersingularEllipticCurveCarrierConstructedIsFalse :
      actualSupersingularEllipticCurveCarrierConstructed ≡ false

    actualGeometricFrobeniusRealizationConstructed : Bool
    actualGeometricFrobeniusRealizationConstructedIsFalse :
      actualGeometricFrobeniusRealizationConstructed ≡ false

    SO3RestrictionClaimedToExplainFrobeniusSpectrum : Bool
    SO3RestrictionClaimedToExplainFrobeniusSpectrumIsFalse :
      SO3RestrictionClaimedToExplainFrobeniusSpectrum ≡ false

canonicalSupersingularFrobeniusOrbitBoundary :
  SupersingularFrobeniusOrbitBoundary
canonicalSupersingularFrobeniusOrbitBoundary =
  record
    { finiteOrbitSpectrumConstructed = true
    ; finiteOrbitSpectrumConstructedIsTrue = refl
    ; twoOrbitDefectEqualsFrickePlusGenus = true
    ; twoOrbitDefectEqualsFrickePlusGenusIsTrue = refl
    ; fullyFixedSpectrumMatchesOggOnFiniteScan = true
    ; fullyFixedSpectrumMatchesOggOnFiniteScanIsTrue = refl
    ; actualSupersingularEllipticCurveCarrierConstructed = false
    ; actualSupersingularEllipticCurveCarrierConstructedIsFalse = refl
    ; actualGeometricFrobeniusRealizationConstructed = false
    ; actualGeometricFrobeniusRealizationConstructedIsFalse = refl
    ; SO3RestrictionClaimedToExplainFrobeniusSpectrum = false
    ; SO3RestrictionClaimedToExplainFrobeniusSpectrumIsFalse = refl
    }
