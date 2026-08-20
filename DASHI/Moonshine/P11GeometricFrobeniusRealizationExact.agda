module DASHI.Moonshine.P11GeometricFrobeniusRealizationExact where

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
-- DASHI CONTRIBUTION
--
-- Close the p=11 geometric-realization seam left deliberately open by the
-- generic supersingular Frobenius spectrum.  The source-certified p=11 carrier
-- consists exactly of j=0 and j=1728=1 mod 11; both are F_11-rational and are
-- fixed by arithmetic Frobenius.  We construct that action on the actual typed
-- carrier and give the explicit equivalence with the existing normal form
-- fixed=2, paired=0, total=2.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (zero; suc)
open import Data.Sum using (inj₁; inj₂)

import DASHI.Foundations.FiniteInvolutionOrbitNormalFormExact as Orbit
import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix
import DASHI.Moonshine.SupersingularFrobeniusOrbitSpectrumExact as Spectrum
import DASHI.Moonshine.P11GeometricSupersingularCarrierExact as Geo
import DASHI.Moonshine.P11BrandtFrobeniusFrickeCarrierSeparationExact as Joint

p11FrobeniusCarrier : Spectrum.SupersingularFrobeniusCarrier Matrix.prime11
p11FrobeniusCarrier = record
  { Spectrum.Carrier = Geo.P11SupersingularJ
  ; Spectrum.frobenius = Joint.p11GeometricFrobenius
  ; Spectrum.frobeniusInvolutive = Joint.p11FrobeniusInvolutive
  ; Spectrum.carrierReceipt =
      "Voight Ch.42 Example 42.3.11 / Silverman V.4.3: ss j=0,1728=1 over F11"
  }

P11Normal : Set
P11Normal = Orbit.OrbitNormalFormCarrier 2 0

p11ToNormal : Geo.P11SupersingularJ → P11Normal
p11ToNormal Geo.jZeroSS = inj₁ zero
p11ToNormal Geo.j1728SS = inj₁ (suc zero)

p11FromNormal : P11Normal → Geo.P11SupersingularJ
p11FromNormal (inj₁ zero) = Geo.jZeroSS
p11FromNormal (inj₁ (suc zero)) = Geo.j1728SS
p11FromNormal (inj₂ (() , bit))

p11FromAfterTo :
  (j : Geo.P11SupersingularJ) → p11FromNormal (p11ToNormal j) ≡ j
p11FromAfterTo Geo.jZeroSS = refl
p11FromAfterTo Geo.j1728SS = refl

p11ToAfterFrom :
  (j : P11Normal) → p11ToNormal (p11FromNormal j) ≡ j
p11ToAfterFrom (inj₁ zero) = refl
p11ToAfterFrom (inj₁ (suc zero)) = refl
p11ToAfterFrom (inj₂ (() , bit))

p11IntertwinesFrobenius :
  (j : Geo.P11SupersingularJ) →
  p11ToNormal (Joint.p11GeometricFrobenius j)
  ≡ Orbit.orbitInvolution (p11ToNormal j)
p11IntertwinesFrobenius Geo.jZeroSS = refl
p11IntertwinesFrobenius Geo.j1728SS = refl

p11NormalFormRealization :
  Orbit.InvolutionNormalFormRealization
    Geo.P11SupersingularJ
    Joint.p11GeometricFrobenius
    (Spectrum.supersingularOrbitSpectrum Matrix.prime11)
p11NormalFormRealization = record
  { Orbit.toNormal = p11ToNormal
  ; Orbit.fromNormal = p11FromNormal
  ; Orbit.fromAfterTo = p11FromAfterTo
  ; Orbit.toAfterFrom = p11ToAfterFrom
  ; Orbit.intertwinesInvolution = p11IntertwinesFrobenius
  }

p11GeometricSpectrumRealization :
  Spectrum.SupersingularFrobeniusNormalFormRealization
    Matrix.prime11 p11FrobeniusCarrier
p11GeometricSpectrumRealization = record
  { Spectrum.realization = p11NormalFormRealization
  ; Spectrum.realizationReceipt =
      "Explicit j=0/1728 chart to the fixed=2 paired=0 Frobenius normal form"
  }

p11PairedOrbitDefectIsZero :
  Orbit.pairedOrbitCount (Spectrum.supersingularOrbitSpectrum Matrix.prime11) ≡ 0
p11PairedOrbitDefectIsZero = refl

record P11GeometricFrobeniusBoundary : Set where
  field
    actualSourceCertifiedCarrierConsumed : Bool
    actualSourceCertifiedCarrierConsumedIsTrue :
      actualSourceCertifiedCarrierConsumed ≡ true

    actualFrobeniusActionConstructed : Bool
    actualFrobeniusActionConstructedIsTrue :
      actualFrobeniusActionConstructed ≡ true

    normalFormRealizationConstructed : Bool
    normalFormRealizationConstructedIsTrue :
      normalFormRealizationConstructed ≡ true

    pairedOrbitDefectZeroConstructed : Bool
    pairedOrbitDefectZeroConstructedIsTrue :
      pairedOrbitDefectZeroConstructed ≡ true

canonicalP11GeometricFrobeniusBoundary : P11GeometricFrobeniusBoundary
canonicalP11GeometricFrobeniusBoundary = record
  { actualSourceCertifiedCarrierConsumed = true
  ; actualSourceCertifiedCarrierConsumedIsTrue = refl
  ; actualFrobeniusActionConstructed = true
  ; actualFrobeniusActionConstructedIsTrue = refl
  ; normalFormRealizationConstructed = true
  ; normalFormRealizationConstructedIsTrue = refl
  ; pairedOrbitDefectZeroConstructed = true
  ; pairedOrbitDefectZeroConstructedIsTrue = refl
  }
