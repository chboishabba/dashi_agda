module DASHI.Moonshine.P43GeometricFrobeniusRealizationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Josep Gonzalez,
-- "On the p-th division polynomial", Journal of Number Theory 233 (2022),
-- 285--300. DOI: 10.1016/j.jnt.2021.06.011.
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
--
-- John Voight,
-- "Quaternion Algebras", GTM 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
--
-- DASHI CONTRIBUTION
--
-- P43NonOggFullLevel2DeuringControlExact independently constructs the p=43
-- coarse supersingular j carrier from the exact Deuring/full-level-2 chart:
--
--   j=8, j=41, and one irreducible quadratic j-pair
--       J^2+19J+16.
--
-- Arithmetic Frobenius fixes the two rational classes and exchanges the
-- quadratic pair.  This file closes the generic normal-form realization seam by
-- giving an explicit equivalence with the independently existing finite orbit
-- spectrum fixed=2, paired=1, total=4.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (zero; suc)
open import Data.Sum using (inj₁; inj₂)

import DASHI.Foundations.FiniteInvolutionOrbitNormalFormExact as Orbit
import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix
import DASHI.Moonshine.SupersingularFrobeniusOrbitSpectrumExact as Spectrum
import DASHI.Moonshine.P43NonOggFullLevel2DeuringControlExact as P43

p43FrobeniusCarrier : Spectrum.SupersingularFrobeniusCarrier Matrix.prime43
p43FrobeniusCarrier = record
  { Spectrum.Carrier = P43.P43GeometricJ
  ; Spectrum.frobenius = P43.p43CoarseFrobenius
  ; Spectrum.frobeniusInvolutive = P43.p43CoarseFrobeniusInvolution
  ; Spectrum.carrierReceipt =
      "Exact H43/Legendre-j chart: j=8, j=41, and roots of J^2+19J+16"
  }

P43Normal : Set
P43Normal = Orbit.OrbitNormalFormCarrier 2 1

p43ToNormal : P43.P43GeometricJ → P43Normal
p43ToNormal P43.j1728 = inj₁ zero
p43ToNormal P43.j41 = inj₁ (suc zero)
p43ToNormal P43.jQuadratic0 = inj₂ (zero , Orbit.bit0)
p43ToNormal P43.jQuadratic1 = inj₂ (zero , Orbit.bit1)

p43FromNormal : P43Normal → P43.P43GeometricJ
p43FromNormal (inj₁ zero) = P43.j1728
p43FromNormal (inj₁ (suc zero)) = P43.j41
p43FromNormal (inj₂ (zero , Orbit.bit0)) = P43.jQuadratic0
p43FromNormal (inj₂ (zero , Orbit.bit1)) = P43.jQuadratic1

p43FromAfterTo :
  (j : P43.P43GeometricJ) → p43FromNormal (p43ToNormal j) ≡ j
p43FromAfterTo P43.j1728 = refl
p43FromAfterTo P43.j41 = refl
p43FromAfterTo P43.jQuadratic0 = refl
p43FromAfterTo P43.jQuadratic1 = refl

p43ToAfterFrom :
  (j : P43Normal) → p43ToNormal (p43FromNormal j) ≡ j
p43ToAfterFrom (inj₁ zero) = refl
p43ToAfterFrom (inj₁ (suc zero)) = refl
p43ToAfterFrom (inj₂ (zero , Orbit.bit0)) = refl
p43ToAfterFrom (inj₂ (zero , Orbit.bit1)) = refl

p43IntertwinesFrobenius :
  (j : P43.P43GeometricJ) →
  p43ToNormal (P43.p43CoarseFrobenius j)
  ≡ Orbit.orbitInvolution (p43ToNormal j)
p43IntertwinesFrobenius P43.j1728 = refl
p43IntertwinesFrobenius P43.j41 = refl
p43IntertwinesFrobenius P43.jQuadratic0 = refl
p43IntertwinesFrobenius P43.jQuadratic1 = refl

p43NormalFormRealization :
  Orbit.InvolutionNormalFormRealization
    P43.P43GeometricJ
    P43.p43CoarseFrobenius
    (Spectrum.supersingularOrbitSpectrum Matrix.prime43)
p43NormalFormRealization = record
  { Orbit.toNormal = p43ToNormal
  ; Orbit.fromNormal = p43FromNormal
  ; Orbit.fromAfterTo = p43FromAfterTo
  ; Orbit.toAfterFrom = p43ToAfterFrom
  ; Orbit.intertwinesInvolution = p43IntertwinesFrobenius
  }

p43GeometricSpectrumRealization :
  Spectrum.SupersingularFrobeniusNormalFormRealization
    Matrix.prime43 p43FrobeniusCarrier
p43GeometricSpectrumRealization = record
  { Spectrum.realization = p43NormalFormRealization
  ; Spectrum.realizationReceipt =
      "Explicit p43 Deuring/Legendre j chart to fixed=2 paired=1 normal form"
  }

p43PairedOrbitDefectIsOne :
  Orbit.pairedOrbitCount (Spectrum.supersingularOrbitSpectrum Matrix.prime43) ≡ 1
p43PairedOrbitDefectIsOne = refl

record P43GeometricFrobeniusBoundary : Set where
  field
    independentDeuringCarrierConsumed : Bool
    actualFrobeniusActionConstructed : Bool
    normalFormRealizationConstructed : Bool
    pairedOrbitDefectOneConstructed : Bool
    p43MarkedHeckeConstructedHere : Bool

canonicalP43GeometricFrobeniusBoundary : P43GeometricFrobeniusBoundary
canonicalP43GeometricFrobeniusBoundary = record
  { independentDeuringCarrierConsumed = true
  ; actualFrobeniusActionConstructed = true
  ; normalFormRealizationConstructed = true
  ; pairedOrbitDefectOneConstructed = true
  ; p43MarkedHeckeConstructedHere = false
  }
