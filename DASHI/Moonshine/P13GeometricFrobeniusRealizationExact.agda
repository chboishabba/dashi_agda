module DASHI.Moonshine.P13GeometricFrobeniusRealizationExact where

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
-- DASHI CONTRIBUTION
--
-- Consume the new independent p=13 Deuring/Legendre-j carrier and realize the
-- repository's generic supersingular Frobenius normal form from it.  The coarse
-- carrier is literally one rational class j=5, so the geometric spectrum is
-- fixed=1, paired=0 without using the finite Ogg/Fricke table as its producer.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin; zero)
open import Data.Sum using (inj₁; inj₂)

import DASHI.Foundations.FiniteInvolutionOrbitNormalFormExact as Orbit
import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix
import DASHI.Moonshine.SupersingularFrobeniusOrbitSpectrumExact as Spectrum
import DASHI.Moonshine.P13OggFullLevel2DeuringControlExact as P13

emptyFinElim : ∀ {A : Set} → Fin 0 → A
emptyFinElim ()

p13FrobeniusCarrier : Spectrum.SupersingularFrobeniusCarrier Matrix.prime13
p13FrobeniusCarrier = record
  { Spectrum.Carrier = P13.P13GeometricJ
  ; Spectrum.frobenius = P13.p13CoarseFrobenius
  ; Spectrum.frobeniusInvolutive = P13.p13CoarseFrobeniusInvolution
  ; Spectrum.carrierReceipt =
      "Exact H13/Legendre-j chart: three quadratic lambda pairs all map to j=5"
  }

P13Normal : Set
P13Normal = Orbit.OrbitNormalFormCarrier 1 0

p13ToNormal : P13.P13GeometricJ → P13Normal
p13ToNormal P13.j5 = inj₁ zero

p13FromNormal : P13Normal → P13.P13GeometricJ
p13FromNormal (inj₁ zero) = P13.j5
p13FromNormal (inj₂ (empty , bit)) = emptyFinElim empty

p13FromAfterTo :
  (j : P13.P13GeometricJ) → p13FromNormal (p13ToNormal j) ≡ j
p13FromAfterTo P13.j5 = refl

p13ToAfterFrom :
  (j : P13Normal) → p13ToNormal (p13FromNormal j) ≡ j
p13ToAfterFrom (inj₁ zero) = refl
p13ToAfterFrom (inj₂ (empty , bit)) = emptyFinElim empty

p13IntertwinesFrobenius :
  (j : P13.P13GeometricJ) →
  p13ToNormal (P13.p13CoarseFrobenius j)
  ≡ Orbit.orbitInvolution (p13ToNormal j)
p13IntertwinesFrobenius P13.j5 = refl

p13NormalFormRealization :
  Orbit.InvolutionNormalFormRealization
    P13.P13GeometricJ
    P13.p13CoarseFrobenius
    (Spectrum.supersingularOrbitSpectrum Matrix.prime13)
p13NormalFormRealization = record
  { Orbit.toNormal = p13ToNormal
  ; Orbit.fromNormal = p13FromNormal
  ; Orbit.fromAfterTo = p13FromAfterTo
  ; Orbit.toAfterFrom = p13ToAfterFrom
  ; Orbit.intertwinesInvolution = p13IntertwinesFrobenius
  }

p13GeometricSpectrumRealization :
  Spectrum.SupersingularFrobeniusNormalFormRealization
    Matrix.prime13 p13FrobeniusCarrier
p13GeometricSpectrumRealization = record
  { Spectrum.realization = p13NormalFormRealization
  ; Spectrum.realizationReceipt =
      "Independent p13 Deuring/Legendre j=5 carrier to fixed=1 paired=0 normal form"
  }

p13PairedOrbitDefectIsZero :
  Orbit.pairedOrbitCount (Spectrum.supersingularOrbitSpectrum Matrix.prime13) ≡ 0
p13PairedOrbitDefectIsZero = refl

record P13GeometricFrobeniusBoundary : Set where
  field
    independentDeuringCarrierConsumed : Bool
    actualFrobeniusActionConstructed : Bool
    normalFormRealizationConstructed : Bool
    pairedOrbitDefectZeroConstructed : Bool
    finiteOggTableUsedAsGeometricProducer : Bool

canonicalP13GeometricFrobeniusBoundary : P13GeometricFrobeniusBoundary
canonicalP13GeometricFrobeniusBoundary = record
  { independentDeuringCarrierConsumed = true
  ; actualFrobeniusActionConstructed = true
  ; normalFormRealizationConstructed = true
  ; pairedOrbitDefectZeroConstructed = true
  ; finiteOggTableUsedAsGeometricProducer = false
  }
