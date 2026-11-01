{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Etch.AspectRatioTransportExact where

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)

-- Source:
-- Richard A. Gottscho; C. W. Jurgensen; D. J. Vitkavage,
-- "Microscopic uniformity in plasma etching",
-- Journal of Vacuum Science & Technology B 10 (1992) 2133–2147,
-- DOI: 10.1116/1.586180.
--
-- The paper documents dependence of etch behavior on aspect ratio and pattern
-- density.  This module owns finite geometry/transport coordinates and exact
-- non-descent examples; it does not encode a specific reactor or recipe.

record FeatureGeometry : Set where
  constructor featureGeometry
  field
    depthCode : Nat
    widthCode : Nat
    localPatternDensityCode : Nat

open FeatureGeometry public

-- Division-free aspect-ratio comparison.  For positive widths,
--   depth₁ / width₁ = depth₂ / width₂
-- iff the cross products agree.
SameAspectRatio : FeatureGeometry → FeatureGeometry → Set
SameAspectRatio a b = depthCode a * widthCode b ≡ depthCode b * widthCode a

record FeatureTransport : Set where
  constructor featureTransport
  field
    geometry              : FeatureGeometry
    entranceNeutralFlux   : Nat
    bottomNeutralFlux     : Nat
    entranceIonFlux       : Nat
    bottomIonFlux         : Nat
    removalCode           : Nat

open FeatureTransport public

shallowFeature : FeatureTransport
shallowFeature =
  featureTransport (featureGeometry 20 20 10) 100 80 100 90 70

deepFeature : FeatureTransport
deepFeature =
  featureTransport (featureGeometry 80 20 10) 100 35 100 75 40

sameWidth : widthCode (geometry shallowFeature) ≡ widthCode (geometry deepFeature)
sameWidth = refl

sameEntranceNeutralFlux : entranceNeutralFlux shallowFeature ≡ entranceNeutralFlux deepFeature
sameEntranceNeutralFlux = refl

sameEntranceIonFlux : entranceIonFlux shallowFeature ≡ entranceIonFlux deepFeature
sameEntranceIonFlux = refl

data ⊥ : Set where

-- Equal reactor-side entrance fluxes do not force equal bottom fluxes once
-- feature geometry differs.
bottomNeutralTransportNonDescent :
  bottomNeutralFlux shallowFeature ≡ bottomNeutralFlux deepFeature → ⊥
bottomNeutralTransportNonDescent ()

removalNonDescentFromEntranceFlux :
  removalCode shallowFeature ≡ removalCode deepFeature → ⊥
removalNonDescentFromEntranceFlux ()

-- Pattern-density / microloading seam: two geometrically identical features can
-- receive different local effective flux when their neighborhood differs.
lowDensityFeature : FeatureTransport
lowDensityFeature =
  featureTransport (featureGeometry 40 20 5) 100 75 100 85 65

highDensityFeature : FeatureTransport
highDensityFeature =
  featureTransport (featureGeometry 40 20 50) 100 55 100 80 50

sameFeatureAspectRatio :
  SameAspectRatio (geometry lowDensityFeature) (geometry highDensityFeature)
sameFeatureAspectRatio = refl

microloadingNonDescent :
  bottomNeutralFlux lowDensityFeature ≡ bottomNeutralFlux highDensityFeature → ⊥
microloadingNonDescent ()

data TransportResidual : Set where
  NeutralKnudsenTransport      : TransportResidual
  IonAngularShadowing          : TransportResidual
  SurfaceStickingCoefficient   : TransportResidual
  RecombinationProbability     : TransportResidual
  PatternDensityDepletion      : TransportResidual
  FeatureChargingField         : TransportResidual
  AspectRatioDependentEtchRate : TransportResidual
  ExactMicroloadingLaw         : TransportResidual
