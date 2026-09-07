module DASHI.Culture.HoeMathLevelsSourceBoundaryExact where

------------------------------------------------------------------------
-- HOE_MATH LEVELS SOURCE / LINEAGE BOUNDARY
--
-- hoe_math owns the assembled pedagogical presentation/chart used here.
-- Underlying Spiral Dynamics, developmental-stage and AQAL materials retain
-- their own source histories.  The web presentation does not import empirical
-- validation of every developmental claim.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

hoeMathIntroductionSource : Source.AttributedSource
hoeMathIntroductionSource =
  Source.mkNoDOISource
    "hoe_math"
    "LEVELS [1: INTRODUCTION]"
    "itishoemath.com"
    "2025-2026 web publication"
    "https://itishoemath.com/levels-1-introduction/"
    Source.practitionerSource
    "presenter-owned nine-level pedagogical model and explanation; page states that the chart is simplified and draws on multiple researchers"
    Source.publicAttribution

hoeMathChartSource : Source.AttributedSource
hoeMathChartSource =
  Source.mkNoDOISource
    "hoe_math"
    "FREE Levels Chart"
    "itishoemath.com"
    "2025-2026"
    "https://itishoemath.com/free-levels-chart/"
    Source.practitionerSource
    "assembled chart separately presenting Spiral Dynamics, developmental levels and AQAL-derived coordinates; underlying named models retain their own authorship"
    Source.publicAttribution

data LevelsComponent : Set where
  simplifiedNineLevelPresentation
  spiralDynamicsComponent
  developmentalLevelsComponent
  aqalQuadrants
  aqalLevels
  aqalLines
  aqalStates
  aqalTypes
  : LevelsComponent

data ComponentOwnership : Set where
  hoeMathPresentationOwnership
  underlyingNamedTradition
  mixedAssembly
  : ComponentOwnership

ownership : LevelsComponent → ComponentOwnership
ownership simplifiedNineLevelPresentation = hoeMathPresentationOwnership
ownership spiralDynamicsComponent = underlyingNamedTradition
ownership developmentalLevelsComponent = underlyingNamedTradition
ownership aqalQuadrants = underlyingNamedTradition
ownership aqalLevels = underlyingNamedTradition
ownership aqalLines = underlyingNamedTradition
ownership aqalStates = underlyingNamedTradition
ownership aqalTypes = underlyingNamedTradition

------------------------------------------------------------------------
-- Structural content actually exposed by the chart.
------------------------------------------------------------------------

data LevelsCoordinate : Set where
  individualMind
  culture
  objectivePhysicalForm
  socialSystem
  developmentalLine
  stateMode
  typeVariation
  viewpointQuadrant
  : LevelsCoordinate

data DevelopmentRelation : Set where
  sequentialStageRelation
  independentlyDevelopingLine
  fluctuatingStateRelation
  orthogonalTypeRelation
  perspectiveRelation
  : DevelopmentRelation

coordinateRelation : LevelsCoordinate → DevelopmentRelation
coordinateRelation individualMind = sequentialStageRelation
coordinateRelation culture = sequentialStageRelation
coordinateRelation objectivePhysicalForm = sequentialStageRelation
coordinateRelation socialSystem = sequentialStageRelation
coordinateRelation developmentalLine = independentlyDevelopingLine
coordinateRelation stateMode = fluctuatingStateRelation
coordinateRelation typeVariation = orthogonalTypeRelation
coordinateRelation viewpointQuadrant = perspectiveRelation

------------------------------------------------------------------------
-- Therefore "levels" cannot safely be flattened to one scalar rank without an
-- additional consumer-specific projection.
------------------------------------------------------------------------

data LevelsIsOnlyOneScalarLadder : Set where
data HigherLevelMeansAuthorityOnEveryCoordinate : Set where
data HoeMathOwnsSpiralDynamics : Set where
data HoeMathOwnsAQAL : Set where
data UnderlyingResearchersOwnHoeMathPresentation : Set where
data ChartPresentationProvesEmpiricalUniversality : Set where
data NineLevelLabelsAreIdenticalToEveryUnderlyingScale : Set where

levelsNotOnlyOneScalarLadder : LevelsIsOnlyOneScalarLadder → ⊥
levelsNotOnlyOneScalarLadder ()

higherDoesNotMeanUniversalAuthority :
  HigherLevelMeansAuthorityOnEveryCoordinate → ⊥
higherDoesNotMeanUniversalAuthority ()

hoeMathDoesNotBecomeSpiralDynamicsAuthor : HoeMathOwnsSpiralDynamics → ⊥
hoeMathDoesNotBecomeSpiralDynamicsAuthor ()

hoeMathDoesNotBecomeAQALAuthor : HoeMathOwnsAQAL → ⊥
hoeMathDoesNotBecomeAQALAuthor ()

underlyingResearchersDoNotOwnHoeMathPresentation :
  UnderlyingResearchersOwnHoeMathPresentation → ⊥
underlyingResearchersDoNotOwnHoeMathPresentation ()

chartDoesNotProveEmpiricalUniversality :
  ChartPresentationProvesEmpiricalUniversality → ⊥
chartDoesNotProveEmpiricalUniversality ()

nineLabelsDoNotBecomeIdenticalToEveryScale :
  NineLevelLabelsAreIdenticalToEveryUnderlyingScale → ⊥
nineLabelsDoNotBecomeIdenticalToEveryUnderlyingScale ()

record HoeMathLevelsSourceBoundary : Set where
  constructor hoe-math-levels-source-boundary
  field
    hoeMathAssemblyAttributed : Bool
    spiralDynamicsLineageSeparated : Bool
    developmentalScaleLineageSeparated : Bool
    aqalLineageSeparated : Bool
    multipleCoordinatesRecovered : Bool
    independentlyDevelopingLinesRecovered : Bool
    fluctuatingStatesRecovered : Bool
    singleScalarExhaustionClaim : Bool
    universalEmpiricalValidityClaim : Bool
    strongerScientificClaimsRequireUnderlyingSources : Bool

canonicalHoeMathLevelsSourceBoundary : HoeMathLevelsSourceBoundary
canonicalHoeMathLevelsSourceBoundary =
  hoe-math-levels-source-boundary
    true true true true true true true false false true
