{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Deposition.FeatureConformalityExact where

open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)

-- Sources:
-- Steven M. George, "Atomic Layer Deposition: An Overview",
-- Chemical Reviews 110 (2010) 111–131, DOI: 10.1021/cr900056b.
--
-- Luzhao Sun et al., "Chemical vapour deposition",
-- Nature Reviews Methods Primers 1, 5 (2021), stable identifier:
-- https://www.nature.com/articles/s43586-020-00005-y
--
-- Conformality is represented as a feature-resolved deposition outcome rather
-- than being inferred from process name alone.

record FeatureFilm : Set where
  constructor featureFilm
  field
    topThicknessCode    : Nat
    sidewallThicknessCode : Nat
    bottomThicknessCode : Nat
    depthCode           : Nat
    widthCode           : Nat

open FeatureFilm public

-- Division-free step-coverage witness:
-- bottom / top = numerator / denominator.
record BottomStepCoverage (x : FeatureFilm) : Set where
  constructor bottomStepCoverage
  field
    numerator   : Nat
    denominator : Nat
    ratioLaw    : bottomThicknessCode x * denominator ≡ topThicknessCode x * numerator

open BottomStepCoverage public

conformalLike : FeatureFilm
conformalLike = featureFilm 100 98 97 80 20

transportLimitedLike : FeatureFilm
transportLimitedLike = featureFilm 100 70 40 80 20

conformalBottomCoverage : BottomStepCoverage conformalLike
conformalBottomCoverage = bottomStepCoverage 97 100 refl

transportLimitedBottomCoverage : BottomStepCoverage transportLimitedLike
transportLimitedBottomCoverage = bottomStepCoverage 2 5 refl

sameTopThickness : topThicknessCode conformalLike ≡ topThicknessCode transportLimitedLike
sameTopThickness = refl

sameGeometryDepth : depthCode conformalLike ≡ depthCode transportLimitedLike
sameGeometryDepth = refl

sameGeometryWidth : widthCode conformalLike ≡ widthCode transportLimitedLike
sameGeometryWidth = refl

data ⊥ : Set where

-- Equal top thickness and equal feature geometry do not determine bottom film.
-- Transport/reaction regime remains an independent producer.
conformalityNonDescent :
  bottomThicknessCode conformalLike ≡ bottomThicknessCode transportLimitedLike → ⊥
conformalityNonDescent ()

-- Firewall:
-- ALD != perfect conformality and CVD != poor conformality as type-level rules.
-- Actual step coverage depends on precursor transport, sticking/reactivity,
-- cycle dose/purge, pressure, temperature and feature geometry.
data ConformalityResidual : Set where
  PrecursorPenetration       : ConformalityResidual
  StickingProbability        : ConformalityResidual
  SurfaceSaturationTimescale : ConformalityResidual
  DiffusionReactionRatio     : ConformalityResidual
  DoseAndPurgeSchedule       : ConformalityResidual
  FeatureGeometry            : ConformalityResidual
  ExactStepCoverageLaw       : ConformalityResidual
