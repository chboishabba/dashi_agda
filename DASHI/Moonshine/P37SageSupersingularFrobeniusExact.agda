module DASHI.Moonshine.P37SageSupersingularFrobeniusExact where

------------------------------------------------------------------------
-- EXECUTABLE SOURCE / CONTEXT
--
-- SageMath, "Module of supersingular points" reference manual, maintained by
-- William Stein, David Kohel, and Iftikhar Burhanuddin.  No DOI asserted for
-- the software documentation.
--
-- The documented characteristic-37 computation is
--
--   SupersingularModule(37).supersingular_points()[0]
--     = [8, 27*a + 23, 10*a + 20]
--
-- in GF(37^2), and the same documentation gives
--
--   B_37(2) = [[1,1,1],[1,0,2],[1,2,0]].
--
-- It also exhibits the two extension-valued points as the two roots, besides
-- the rational root 8, in the p=37 Phi_2 computation.
--
-- MATHEMATICAL CONTEXT
-- John Voight, "Quaternion Algebras", GTM 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
--
-- Joseph H. Silverman, "The Arithmetic of Elliptic Curves", 2nd ed.,
-- Springer, 2009. DOI: 10.1007/978-0-387-09494-6.
--
-- DASHI CONTRIBUTION
--
-- Replace the anonymous p=37 three-slot control by a source-labelled geometric
-- carrier.  The visible F_37 point 8 is Frobenius-fixed; the two remaining
-- points form the unique quadratic Frobenius pair.  We chart this carrier to
-- the existing Sage-basis p37 Brandt classes and prove the documented T2
-- neighbour system commutes with Frobenius edge-by-edge.
--
-- This encodes the cited/executable finite-field result; it does not implement
-- GF(37^2) polynomial arithmetic from first principles inside Agda.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin; zero; suc)
open import Data.Sum using (inj₁; inj₂)

import DASHI.Foundations.FiniteInvolutionOrbitNormalFormExact as Orbit
import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix
import DASHI.Moonshine.SupersingularFrobeniusOrbitSpectrumExact as Spectrum
import DASHI.Moonshine.BrandtStackUnweightingControlsExact as Controls
import DASHI.Moonshine.P37NonOggPositiveHeckeControlExact as P37

------------------------------------------------------------------------
-- Source-labelled supersingular j-classes.
------------------------------------------------------------------------

data P37SupersingularJ : Set where
  j8
  j27aPlus23
  j10aPlus20 : P37SupersingularJ

sageDisplayLabel : P37SupersingularJ → String
sageDisplayLabel j8 = "8"
sageDisplayLabel j27aPlus23 = "27*a + 23"
sageDisplayLabel j10aPlus20 = "10*a + 20"

p37Frobenius : P37SupersingularJ → P37SupersingularJ
p37Frobenius j8 = j8
p37Frobenius j27aPlus23 = j10aPlus20
p37Frobenius j10aPlus20 = j27aPlus23

p37FrobeniusInvolutive :
  (j : P37SupersingularJ) → p37Frobenius (p37Frobenius j) ≡ j
p37FrobeniusInvolutive j8 = refl
p37FrobeniusInvolutive j27aPlus23 = refl
p37FrobeniusInvolutive j10aPlus20 = refl

------------------------------------------------------------------------
-- Exact chart to the existing Sage Brandt-basis carrier.
------------------------------------------------------------------------

toBrandtClass : P37SupersingularJ → Controls.P37BrandtClass
toBrandtClass j8 = Controls.p37c0
toBrandtClass j27aPlus23 = Controls.p37c1
toBrandtClass j10aPlus20 = Controls.p37c2

fromBrandtClass : Controls.P37BrandtClass → P37SupersingularJ
fromBrandtClass Controls.p37c0 = j8
fromBrandtClass Controls.p37c1 = j27aPlus23
fromBrandtClass Controls.p37c2 = j10aPlus20

brandtAfterJ : (j : P37SupersingularJ) → fromBrandtClass (toBrandtClass j) ≡ j
brandtAfterJ j8 = refl
brandtAfterJ j27aPlus23 = refl
brandtAfterJ j10aPlus20 = refl

jAfterBrandt :
  (c : Controls.P37BrandtClass) → toBrandtClass (fromBrandtClass c) ≡ c
jAfterBrandt Controls.p37c0 = refl
jAfterBrandt Controls.p37c1 = refl
jAfterBrandt Controls.p37c2 = refl

brandtFrobenius : Controls.P37BrandtClass → Controls.P37BrandtClass
brandtFrobenius c = toBrandtClass (p37Frobenius (fromBrandtClass c))

brandtFrobeniusTable0 : brandtFrobenius Controls.p37c0 ≡ Controls.p37c0
brandtFrobeniusTable0 = refl

brandtFrobeniusTable1 : brandtFrobenius Controls.p37c1 ≡ Controls.p37c2
brandtFrobeniusTable1 = refl

brandtFrobeniusTable2 : brandtFrobenius Controls.p37c2 ≡ Controls.p37c1
brandtFrobeniusTable2 = refl

------------------------------------------------------------------------
-- Exact p37 T2/Frobenius equivariance on the source Brandt neighbour list.
------------------------------------------------------------------------

p37T2CommutesWithFrobenius :
  (source : Controls.P37BrandtClass) →
  (edge : Fin 3) →
  brandtFrobenius (P37.p37T2Neighbour source edge)
  ≡ P37.p37T2Neighbour (brandtFrobenius source) edge
p37T2CommutesWithFrobenius Controls.p37c0 zero = refl
p37T2CommutesWithFrobenius Controls.p37c0 (suc zero) = refl
p37T2CommutesWithFrobenius Controls.p37c0 (suc (suc zero)) = refl
p37T2CommutesWithFrobenius Controls.p37c1 zero = refl
p37T2CommutesWithFrobenius Controls.p37c1 (suc zero) = refl
p37T2CommutesWithFrobenius Controls.p37c1 (suc (suc zero)) = refl
p37T2CommutesWithFrobenius Controls.p37c2 zero = refl
p37T2CommutesWithFrobenius Controls.p37c2 (suc zero) = refl
p37T2CommutesWithFrobenius Controls.p37c2 (suc (suc zero)) = refl

------------------------------------------------------------------------
-- Explicit normal-form realization: one fixed point and one paired orbit.
------------------------------------------------------------------------

P37Normal : Set
P37Normal = Orbit.OrbitNormalFormCarrier 1 1

p37ToNormal : P37SupersingularJ → P37Normal
p37ToNormal j8 = inj₁ zero
p37ToNormal j27aPlus23 = inj₂ (zero , Orbit.bit0)
p37ToNormal j10aPlus20 = inj₂ (zero , Orbit.bit1)

p37FromNormal : P37Normal → P37SupersingularJ
p37FromNormal (inj₁ zero) = j8
p37FromNormal (inj₂ (zero , Orbit.bit0)) = j27aPlus23
p37FromNormal (inj₂ (zero , Orbit.bit1)) = j10aPlus20

p37FromAfterTo : (j : P37SupersingularJ) → p37FromNormal (p37ToNormal j) ≡ j
p37FromAfterTo j8 = refl
p37FromAfterTo j27aPlus23 = refl
p37FromAfterTo j10aPlus20 = refl

p37ToAfterFrom : (j : P37Normal) → p37ToNormal (p37FromNormal j) ≡ j
p37ToAfterFrom (inj₁ zero) = refl
p37ToAfterFrom (inj₂ (zero , Orbit.bit0)) = refl
p37ToAfterFrom (inj₂ (zero , Orbit.bit1)) = refl

p37IntertwinesFrobenius :
  (j : P37SupersingularJ) →
  p37ToNormal (p37Frobenius j) ≡ Orbit.orbitInvolution (p37ToNormal j)
p37IntertwinesFrobenius j8 = refl
p37IntertwinesFrobenius j27aPlus23 = refl
p37IntertwinesFrobenius j10aPlus20 = refl

p37NormalFormRealization :
  Orbit.InvolutionNormalFormRealization
    P37SupersingularJ p37Frobenius
    (Spectrum.supersingularOrbitSpectrum Matrix.prime37)
p37NormalFormRealization = record
  { Orbit.toNormal = p37ToNormal
  ; Orbit.fromNormal = p37FromNormal
  ; Orbit.fromAfterTo = p37FromAfterTo
  ; Orbit.toAfterFrom = p37ToAfterFrom
  ; Orbit.intertwinesInvolution = p37IntertwinesFrobenius
  }

p37FrobeniusCarrier : Spectrum.SupersingularFrobeniusCarrier Matrix.prime37
p37FrobeniusCarrier = record
  { Spectrum.Carrier = P37SupersingularJ
  ; Spectrum.frobenius = p37Frobenius
  ; Spectrum.frobeniusInvolutive = p37FrobeniusInvolutive
  ; Spectrum.carrierReceipt =
      "Sage SupersingularModule(37): [8,27*a+23,10*a+20] in GF(37^2)"
  }

p37GeometricSpectrumRealization :
  Spectrum.SupersingularFrobeniusNormalFormRealization
    Matrix.prime37 p37FrobeniusCarrier
p37GeometricSpectrumRealization = record
  { Spectrum.realization = p37NormalFormRealization
  ; Spectrum.realizationReceipt =
      "8 fixed; the two GF(37^2) extension classes form the quadratic Frobenius pair"
  }

record P37SageFrobeniusBoundary : Set where
  field
    sourceSupersingularLabelsEncoded : Bool
    sourceSupersingularLabelsEncodedIsTrue : sourceSupersingularLabelsEncoded ≡ true

    geometricFrobeniusActionConstructed : Bool
    geometricFrobeniusActionConstructedIsTrue :
      geometricFrobeniusActionConstructed ≡ true

    t2FrobeniusEquivarianceConstructed : Bool
    t2FrobeniusEquivarianceConstructedIsTrue :
      t2FrobeniusEquivarianceConstructed ≡ true

    oneFixedOnePairNormalFormRealized : Bool
    oneFixedOnePairNormalFormRealizedIsTrue :
      oneFixedOnePairNormalFormRealized ≡ true

    gf37SquaredArithmeticReimplementedInternally : Bool
    gf37SquaredArithmeticReimplementedInternallyIsFalse :
      gf37SquaredArithmeticReimplementedInternally ≡ false

canonicalP37SageFrobeniusBoundary : P37SageFrobeniusBoundary
canonicalP37SageFrobeniusBoundary = record
  { sourceSupersingularLabelsEncoded = true
  ; sourceSupersingularLabelsEncodedIsTrue = refl
  ; geometricFrobeniusActionConstructed = true
  ; geometricFrobeniusActionConstructedIsTrue = refl
  ; t2FrobeniusEquivarianceConstructed = true
  ; t2FrobeniusEquivarianceConstructedIsTrue = refl
  ; oneFixedOnePairNormalFormRealized = true
  ; oneFixedOnePairNormalFormRealizedIsTrue = refl
  ; gf37SquaredArithmeticReimplementedInternally = false
  ; gf37SquaredArithmeticReimplementedInternallyIsFalse = refl
  }
