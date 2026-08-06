module DASHI.Biology.LogPolarRetinotopyBridge where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Finite log-polar retinotopy bridge.
--
-- The retina and cortex are not asserted to form an exact mathematical
-- log-polar grid.  This module proves finite analogues of two useful
-- consequences of the complex-log approximation: multiplicative scale and
-- rotation become additive translations in cortical coordinates.
--
-- Source-facing references:
-- Eric L. Schwartz,
-- "Computational anatomy and functional architecture of striate cortex:
-- a spatial mapping approach to perceptual coding",
-- DOI 10.1016/0042-6989(80)90090-5.
-- Duyan Ta, Yanshuai Tu, Zhong-Lin Lu, and Yalin Wang,
-- "Quantitative Characterization of the Human Retinotopic Map Based on
-- Quasiconformal Mapping", DOI 10.1016/j.media.2021.102230.

data RadiusScale : Set where
  radiusOne : RadiusScale
  radiusTwo : RadiusScale
  radiusFour : RadiusScale

logRadiusCode : RadiusScale → Nat
logRadiusCode radiusOne = 0
logRadiusCode radiusTwo = 1
logRadiusCode radiusFour = 2

doubleRadius : RadiusScale → RadiusScale
doubleRadius radiusOne = radiusTwo
doubleRadius radiusTwo = radiusFour
doubleRadius radiusFour = radiusFour

doublingAtRadiusOneIsUnitTranslation :
  logRadiusCode (doubleRadius radiusOne)
  ≡
  suc (logRadiusCode radiusOne)
doublingAtRadiusOneIsUnitTranslation = refl

doublingAtRadiusTwoIsUnitTranslation :
  logRadiusCode (doubleRadius radiusTwo)
  ≡
  suc (logRadiusCode radiusTwo)
doublingAtRadiusTwoIsUnitTranslation = refl

data AngleSector : Set where
  sector0 : AngleSector
  sector1 : AngleSector
  sector2 : AngleSector
  sector3 : AngleSector

rotateQuarter : AngleSector → AngleSector
rotateQuarter sector0 = sector1
rotateQuarter sector1 = sector2
rotateQuarter sector2 = sector3
rotateQuarter sector3 = sector0

angleCode : AngleSector → Nat
angleCode sector0 = 0
angleCode sector1 = 1
angleCode sector2 = 2
angleCode sector3 = 3

quarterRotationAtZeroIsUnitTranslation :
  angleCode (rotateQuarter sector0)
  ≡
  suc (angleCode sector0)
quarterRotationAtZeroIsUnitTranslation = refl

quarterRotationAtOneIsUnitTranslation :
  angleCode (rotateQuarter sector1)
  ≡
  suc (angleCode sector1)
quarterRotationAtOneIsUnitTranslation = refl

record PolarSample : Set where
  constructor polarSample
  field
    radius : RadiusScale
    angle : AngleSector

open PolarSample public

record CorticalSample : Set where
  constructor corticalSample
  field
    radialCoordinate : Nat
    angularCoordinate : Nat

open CorticalSample public

retinocorticalMap : PolarSample → CorticalSample
retinocorticalMap (polarSample r θ) =
  corticalSample (logRadiusCode r) (angleCode θ)

spiralStep : PolarSample → PolarSample
spiralStep (polarSample r θ) =
  polarSample (doubleRadius r) (rotateQuarter θ)

spiralStart : PolarSample
spiralStart = polarSample radiusOne sector0

spiralSecond : PolarSample
spiralSecond = spiralStep spiralStart

spiralThird : PolarSample
spiralThird = spiralStep spiralSecond

spiralSecondMapsToDiagonalOne :
  retinocorticalMap spiralSecond ≡ corticalSample 1 1
spiralSecondMapsToDiagonalOne = refl

spiralThirdMapsToDiagonalTwo :
  retinocorticalMap spiralThird ≡ corticalSample 2 2
spiralThirdMapsToDiagonalTwo = refl

------------------------------------------------------------------------
-- A finite phyllotactic phase carrier.  This is not the real golden angle;
-- it records the structurally relevant fact that sequential radial growth and
-- angular phase advance can jointly become a simple trajectory in cortical
-- coordinates.

data PrimordiumIndex : Set where
  primordium0 : PrimordiumIndex
  primordium1 : PrimordiumIndex
  primordium2 : PrimordiumIndex

phyllotacticSample : PrimordiumIndex → PolarSample
phyllotacticSample primordium0 =
  polarSample radiusOne sector0
phyllotacticSample primordium1 =
  polarSample radiusTwo sector1
phyllotacticSample primordium2 =
  polarSample radiusFour sector2

phyllotacticCorticalProgression :
  retinocorticalMap (phyllotacticSample primordium2)
  ≡
  corticalSample 2 2
phyllotacticCorticalProgression = refl

------------------------------------------------------------------------
-- Distinct world generators may share one cortical projection.

data WorldGenerator : Set where
  squareWorldGenerator : WorldGenerator
  apollonianWorldGenerator : WorldGenerator
  phyllotacticWorldGenerator : WorldGenerator

data CorticalPattern : Set where
  radialTunnelPattern : CorticalPattern
  branchingPattern : CorticalPattern

corticalProjection : WorldGenerator → CorticalPattern
corticalProjection squareWorldGenerator = radialTunnelPattern
corticalProjection apollonianWorldGenerator = radialTunnelPattern
corticalProjection phyllotacticWorldGenerator = branchingPattern

squareAndApollonianCanShareCorticalProjection :
  corticalProjection squareWorldGenerator
  ≡
  corticalProjection apollonianWorldGenerator
squareAndApollonianCanShareCorticalProjection = refl

squareAndApollonianRemainDifferentGenerators :
  squareWorldGenerator ≡ apollonianWorldGenerator → ⊥
squareAndApollonianRemainDifferentGenerators ()

record LogPolarBoundary : Set where
  constructor logPolarBoundary
  field
    retinaIsExactLogPolarGrid : Bool
    retinaIsExactLogPolarGridIsFalse :
      retinaIsExactLogPolarGrid ≡ false

    corticalProjectionIdentifiesWorldGenerator : Bool
    corticalProjectionIdentifiesWorldGeneratorIsFalse :
      corticalProjectionIdentifiesWorldGenerator ≡ false

    finitePhaseIsGoldenAngleMeasurement : Bool
    finitePhaseIsGoldenAngleMeasurementIsFalse :
      finitePhaseIsGoldenAngleMeasurement ≡ false

open LogPolarBoundary public

canonicalLogPolarBoundary : LogPolarBoundary
canonicalLogPolarBoundary =
  logPolarBoundary false refl false refl false refl
