module DASHI.Moonshine.OggSmallCharacteristicAutomorphismOrderAttributionExact where

------------------------------------------------------------------------
-- SMALL-CHARACTERISTIC SUPERSINGULAR AUTOMORPHISM ORDERS
--
-- EXTERNAL SOURCE
--
-- Andrew P. Ogg, "Hyperelliptic modular curves",
-- Bulletin de la Societe Mathematique de France 102 (1974), 449--462.
--
-- Ogg states in the characteristic-2 argument that the unique supersingular
-- elliptic curve has automorphism group of order 24, and then states that the
-- corresponding characteristic-3 supersingular j=0 curve has 12
-- automorphisms.
--
-- This module records those two EXTERNAL arithmetic values only.
--
-- DASHI does not derive the automorphism groups here, does not identify them
-- with the exponent-residual groupoids, and does not identify the factor
-- 24/12 = 2 with the retained p=2 orientation sheet.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Source

oggHyperellipticModularCurves :
  Attribution.AttributedSource
oggHyperellipticModularCurves =
  Attribution.mkNoDOISource
    "Andrew P. Ogg"
    "Hyperelliptic modular curves"
    "Bulletin de la Societe Mathematique de France 102, 449--462"
    "1974"
    "https://www.numdam.org/item/BSMF_1974__102__449_0/"
    Attribution.academicArticleSource
    "external authority for the small-characteristic supersingular automorphism-order statements used here"
    Attribution.publicAttribution

data SmallCharacteristicPrime : Set where
  p2 p3 : SmallCharacteristicPrime

externalSupersingularAutomorphismOrder :
  SmallCharacteristicPrime -> Nat
externalSupersingularAutomorphismOrder p2 = 24
externalSupersingularAutomorphismOrder p3 = 12

p2ExternalAutomorphismOrderIs24 :
  externalSupersingularAutomorphismOrder p2 ≡ 24
p2ExternalAutomorphismOrderIs24 = refl

p3ExternalAutomorphismOrderIs12 :
  externalSupersingularAutomorphismOrder p3 ≡ 12
p3ExternalAutomorphismOrderIs12 = refl

p2OrderIsTwiceP3Order :
  externalSupersingularAutomorphismOrder p2
  ≡ 2 * externalSupersingularAutomorphismOrder p3
p2OrderIsTwiceP3Order = refl

claimOrigin : Source.ClaimOrigin
claimOrigin = Source.externalOggSourceClaim

data AutomorphismOrderRatioIsResidualOrientationFibre : Set where
data AutomorphismOrderDeterminesExponentResidualGroupoid : Set where

automorphismOrderRatioDoesNotIdentifyResidualOrientationFibre :
  AutomorphismOrderRatioIsResidualOrientationFibre -> ⊥
automorphismOrderRatioDoesNotIdentifyResidualOrientationFibre ()

automorphismOrderDoesNotDetermineExponentResidualGroupoid :
  AutomorphismOrderDeterminesExponentResidualGroupoid -> ⊥
automorphismOrderDoesNotDetermineExponentResidualGroupoid ()

record SmallCharacteristicAutomorphismOrderBoundary : Set where
  constructor small-characteristic-automorphism-order-boundary
  field
    oggSourceAttributed : Bool
    p2Order24RecordedAsExternal : Bool
    p3Order12RecordedAsExternal : Bool
    factorTwoComparisonProved : Bool
    factorTwoIdentifiedWithResidualOrientation : Bool
    automorphismOrderPromotedToResidualGroupoid : Bool

canonicalSmallCharacteristicAutomorphismOrderBoundary :
  SmallCharacteristicAutomorphismOrderBoundary
canonicalSmallCharacteristicAutomorphismOrderBoundary =
  small-characteristic-automorphism-order-boundary
    true true true true false false
