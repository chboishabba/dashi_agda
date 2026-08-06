module DASHI.Physics.Foundations.ParameterScaleTaxonomyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Constants.Registry as Registry
import DASHI.Core.CandidateFunctionalCore as Candidate

------------------------------------------------------------------------
-- Replacement constants taxonomy.
--
-- This module implements the replacement A--P supplied after the earlier
-- Sections 46--76.  It keeps five explanatory levels distinct, proves a
-- finite scale-orbit obstruction, records law/vacuum/boundary decomposition,
-- and separates invariant ratios from numerical representatives in units.

data ExplanatoryLevel : Set where
  structuralInvariantLevel : ExplanatoryLevel
  dynamicalParameterLevel : ExplanatoryLevel
  dimensionfulScaleLevel : ExplanatoryLevel
  conversionConstantLevel : ExplanatoryLevel
  unitRepresentationLevel : ExplanatoryLevel

data ParameterOrigin : Set where
  lawOrigin : ParameterOrigin
  vacuumOrigin : ParameterOrigin
  boundaryOrigin : ParameterOrigin
  calibrationOrigin : ParameterOrigin

data ConstantRole : Set where
  structuralIntegerRole : ConstantRole
  dimensionlessDynamicalRole : ConstantRole
  dimensionfulScaleRole : ConstantRole
  conversionRole : ConstantRole
  humanUnitNumberRole : ConstantRole

record ClassifiedQuantity : Set where
  constructor classifiedQuantity
  field
    label : String
    role : ConstantRole
    level : ExplanatoryLevel
    origin : ParameterOrigin

open ClassifiedQuantity public

fineStructureQuantity : ClassifiedQuantity
fineStructureQuantity =
  classifiedQuantity
    "fine-structure coupling"
    dimensionlessDynamicalRole
    dynamicalParameterLevel
    calibrationOrigin

speedOfLightConversionQuantity : ClassifiedQuantity
speedOfLightConversionQuantity =
  classifiedQuantity
    "speed-of-light conversion relation"
    conversionRole
    conversionConstantLevel
    calibrationOrigin

siSpeedNumberQuantity : ClassifiedQuantity
siSpeedNumberQuantity =
  classifiedQuantity
    "299792458 metres per second"
    humanUnitNumberRole
    unitRepresentationLevel
    calibrationOrigin

existingRegistryCarrier : Set₁
existingRegistryCarrier = Registry.ConstantsRegistryLink

existingCandidateFunctionalCarrier : Set
existingCandidateFunctionalCarrier = Candidate.CandidateFunctionalSurface

------------------------------------------------------------------------
-- Law, vacuum, and boundary data are separate sources of realised values.

record ParameterDecomposition : Set where
  constructor parameterDecomposition
  field
    lawCoordinate : Nat
    vacuumCoordinate : Nat
    boundaryCoordinate : Nat

open ParameterDecomposition public

realisedCoordinate : ParameterDecomposition → Nat
realisedCoordinate p =
  lawCoordinate p + vacuumCoordinate p + boundaryCoordinate p

canonicalParameterDecomposition : ParameterDecomposition
canonicalParameterDecomposition = parameterDecomposition 2 3 4

canonicalRealisedCoordinateIsNine :
  realisedCoordinate canonicalParameterDecomposition ≡ 9
canonicalRealisedCoordinateIsNine = refl

------------------------------------------------------------------------
-- Exact finite scale-orbit obstruction.
--
-- A nonzero observable with nonzero scaling weight has at least two distinct
-- representatives on a nontrivial scale orbit.  A scale-equivariant rule
-- therefore cannot select both representatives as one unique numerical value.

data ScaleRepresentative : Set where
  unitScale : ScaleRepresentative
  doubledScale : ScaleRepresentative

scaledObservable : ScaleRepresentative → Nat
scaledObservable unitScale = 1
scaledObservable doubledScale = 2

unitAndDoubledScaleAreDistinct :
  scaledObservable unitScale ≡ scaledObservable doubledScale → ⊥
unitAndDoubledScaleAreDistinct ()

data ScaleBreakingMechanism : Set where
  explicitScaleBreaking : ScaleBreakingMechanism
  spontaneousScaleBreaking : ScaleBreakingMechanism
  anomalousScaleBreaking : ScaleBreakingMechanism
  boundaryScaleBreaking : ScaleBreakingMechanism
  finiteSizeScaleBreaking : ScaleBreakingMechanism
  calibrationScaleFixing : ScaleBreakingMechanism

record ScaleSelectionWitness : Set where
  constructor scaleSelectionWitness
  field
    mechanism : ScaleBreakingMechanism
    selectedRepresentative : ScaleRepresentative

canonicalScaleSelectionWitness : ScaleSelectionWitness
canonicalScaleSelectionWitness =
  scaleSelectionWitness boundaryScaleBreaking unitScale

------------------------------------------------------------------------
-- Finite dimensional-transmutation analogue.
--
-- The generated scale is derived from a dimensionless running datum and a
-- reference scale.  The construction deliberately records that changing the
-- reference datum changes the realised scale: it is not creation from no data.

record RunningDatum : Set where
  constructor runningDatum
  field
    referenceScale : Nat
    dimensionlessCoupling : Nat

open RunningDatum public

generatedScale : RunningDatum → Nat
generatedScale datum =
  referenceScale datum * dimensionlessCoupling datum

runningDatumA : RunningDatum
runningDatumA = runningDatum 3 2

runningDatumB : RunningDatum
runningDatumB = runningDatum 3 3

generatedScaleAIsSix : generatedScale runningDatumA ≡ 6
generatedScaleAIsSix = refl

generatedScaleBIsNine : generatedScale runningDatumB ≡ 9
generatedScaleBIsNine = refl

------------------------------------------------------------------------
-- Reparametrisation and identifiability.
--
-- Two coordinates can describe the same observable point.  A physical
-- objective must descend to the observable quotient instead of depending on
-- the spelling or Euclidean norm of one coordinate chart.

data TheoryCoordinate : Set where
  coordinateLambda : TheoryCoordinate
  coordinateEta : TheoryCoordinate
  coordinateOther : TheoryCoordinate

data ObservableClass : Set where
  observableClassA : ObservableClass
  observableClassB : ObservableClass

observableClass : TheoryCoordinate → ObservableClass
observableClass coordinateLambda = observableClassA
observableClass coordinateEta = observableClassA
observableClass coordinateOther = observableClassB

lambdaAndEtaAreObservationallyIdentified :
  observableClass coordinateLambda ≡ observableClass coordinateEta
lambdaAndEtaAreObservationallyIdentified = refl

invariantScore : ObservableClass → Nat
invariantScore observableClassA = 1
invariantScore observableClassB = 4

coordinateInvariantScore : TheoryCoordinate → Nat
coordinateInvariantScore coordinate = invariantScore (observableClass coordinate)

reparametrisedCoordinatesHaveSameScore :
  coordinateInvariantScore coordinateLambda
  ≡
  coordinateInvariantScore coordinateEta
reparametrisedCoordinatesHaveSameScore = refl

------------------------------------------------------------------------
-- Universal ratios and precision-dependent descriptive length.

record RatioRepresentative : Set where
  constructor ratioRepresentative
  field
    numerator : Nat
    denominator : Nat

open RatioRepresentative public

sameRatio : RatioRepresentative → RatioRepresentative → Set
sameRatio x y =
  numerator x * denominator y
  ≡
  numerator y * denominator x

ratioTwoFour : RatioRepresentative
ratioTwoFour = ratioRepresentative 2 4

ratioThreeSix : RatioRepresentative
ratioThreeSix = ratioRepresentative 3 6

universalRatioWitness : sameRatio ratioTwoFour ratioThreeSix
universalRatioWitness = refl

precisionCodeLength : Nat → Nat
precisionCodeLength precision = precision

threeDigitPrecisionCostsThree : precisionCodeLength 3 ≡ 3
threeDigitPrecisionCostsThree = refl

fiveDigitPrecisionCostsFive : precisionCodeLength 5 ≡ 5
fiveDigitPrecisionCostsFive = refl

------------------------------------------------------------------------
-- Authority boundary.

record ParameterScaleBoundary : Set where
  constructor parameterScaleBoundary
  field
    everyDimensionlessConstantIsAnRGFixedPoint : Bool
    everyDimensionlessConstantIsAnRGFixedPointIsFalse :
      everyDimensionlessConstantIsAnRGFixedPoint ≡ false

    exactScaleInvarianceSelectsUniqueNonzeroScale : Bool
    exactScaleInvarianceSelectsUniqueNonzeroScaleIsFalse :
      exactScaleInvarianceSelectsUniqueNonzeroScale ≡ false

    numericalValueInChosenUnitsIsInvariantContent : Bool
    numericalValueInChosenUnitsIsInvariantContentIsFalse :
      numericalValueInChosenUnitsIsInvariantContent ≡ false

    coordinateNormIsReparametrisationInvariant : Bool
    coordinateNormIsReparametrisationInvariantIsFalse :
      coordinateNormIsReparametrisationInvariant ≡ false

    dimensionalTransmutationNeedsNoIntegrationDatum : Bool
    dimensionalTransmutationNeedsNoIntegrationDatumIsFalse :
      dimensionalTransmutationNeedsNoIntegrationDatum ≡ false

    constantsRegistryIsReDerivedHere : Bool
    constantsRegistryIsReDerivedHereIsFalse :
      constantsRegistryIsReDerivedHere ≡ false

open ParameterScaleBoundary public

canonicalParameterScaleBoundary : ParameterScaleBoundary
canonicalParameterScaleBoundary =
  parameterScaleBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
