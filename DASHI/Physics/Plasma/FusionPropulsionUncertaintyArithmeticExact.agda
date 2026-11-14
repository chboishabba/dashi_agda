module DASHI.Physics.Plasma.FusionPropulsionUncertaintyArithmeticExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.FusionPropulsionLiteralMaxCutExact as MaxCut

------------------------------------------------------------------------
-- ROOT-POLE SQUARE-ROOT SCALING: FINITE ARITHMETIC WITNESS
--
-- This is an exact arithmetic normal form for validation fixtures.  It does
-- not prove the kinetic dispersion theorem; that remains carried by the
-- source-attributed RootPoleInstabilityReceipt.
------------------------------------------------------------------------

record SquareRootScalingWitness : Set where
  constructor square-root-scaling-witness
  field
    minorityDensityScale : Nat
    densitySquareRoot : Nat
    growthCoefficient : Nat
    growthRateScale : Nat
    densityIsSquare :
      minorityDensityScale ≡ densitySquareRoot * densitySquareRoot
    growthIsCoefficientTimesRoot :
      growthRateScale ≡ growthCoefficient * densitySquareRoot
    squaredGrowthIdentity :
      growthRateScale * growthRateScale ≡
      (growthCoefficient * growthCoefficient) * minorityDensityScale
    scalingSource : MaxCut.SourceAttribution

open SquareRootScalingWitness public

canonicalSquareRootScalingFixture : SquareRootScalingWitness
canonicalSquareRootScalingFixture =
  square-root-scaling-witness
    4 2 3 6 refl refl refl MaxCut.qinfischRootPoleSource

record RootPoleArithmeticBoundary : Set where
  constructor root-pole-arithmetic-boundary
  field
    finiteScalingFixtureProvesKineticDispersionRelation : Bool
    finiteScalingFixtureProvesKineticDispersionRelationIsFalse :
      finiteScalingFixtureProvesKineticDispersionRelation ≡ false

    kineticTheorySuppliesValidationShape : Bool
    kineticTheorySuppliesValidationShapeIsTrue :
      kineticTheorySuppliesValidationShape ≡ true

canonicalRootPoleArithmeticBoundary : RootPoleArithmeticBoundary
canonicalRootPoleArithmeticBoundary =
  root-pole-arithmetic-boundary false refl true refl

------------------------------------------------------------------------
-- SPECIES-RESOLVED ENERGY-TRANSFER BOOKKEEPING
--
-- The exchange-conservation theorem shape is reusable.  Ideal-MHD triad
-- dynamics are not imported into the kinetic IBW mechanism.
------------------------------------------------------------------------

record QuantisedSpeciesPowerTransfer : Set where
  constructor quantised-species-power-transfer
  field
    fusionProductPowerLoss : Nat
    coherentThermalIonPower : Nat
    otherPower : Nat
    conservation :
      fusionProductPowerLoss ≡ coherentThermalIonPower + otherPower
    source : MaxCut.SourceAttribution
    sourceIsTheory :
      MaxCut.evidenceClass source ≡ MaxCut.analyticOrKineticTheory

open QuantisedSpeciesPowerTransfer public

qinfischReportedPowerPartition : QuantisedSpeciesPowerTransfer
qinfischReportedPowerPartition =
  quantised-species-power-transfer
    10000
    9996
    4
    refl
    MaxCut.qinfischRootPoleSource
    refl

record KineticExchangeCrossPollinationBoundary : Set where
  constructor kinetic-exchange-cross-pollination-boundary
  field
    conservationBookkeepingShapeReusable : Bool
    conservationBookkeepingShapeReusableIsTrue :
      conservationBookkeepingShapeReusable ≡ true
    idealMHDTriadCoefficientTransferred : Bool
    idealMHDTriadCoefficientTransferredIsFalse :
      idealMHDTriadCoefficientTransferred ≡ false
    reportedPartitionIsExperimentalMeasurement : Bool
    reportedPartitionIsExperimentalMeasurementIsFalse :
      reportedPartitionIsExperimentalMeasurement ≡ false

canonicalKineticExchangeCrossPollinationBoundary :
  KineticExchangeCrossPollinationBoundary
canonicalKineticExchangeCrossPollinationBoundary =
  kinetic-exchange-cross-pollination-boundary
    true refl false refl false refl

------------------------------------------------------------------------
-- P-B11 COMPETING-MODEL FAMILY
------------------------------------------------------------------------

data PB11CrossSectionModel : Set where
  lowerResonanceEvaluation : PB11CrossSectionModel
  upperResonanceEvaluation : PB11CrossSectionModel

lowerUpperModelsDistinct :
  lowerResonanceEvaluation ≡ upperResonanceEvaluation → ⊥
lowerUpperModelsDistinct ()

record PB11ReactivityFamily : Set₁ where
  constructor pb11-reactivity-family
  field
    RelativeEnergy CrossSection Reactivity : Set
    sigma :
      PB11CrossSectionModel → RelativeEnergy → CrossSection
    distributionIntegratedReactivity :
      PB11CrossSectionModel → Reactivity
    nuisance : MaxCut.CrossSectionNuisanceParameters
    propagationReceipt : Set
    reactivitySource : MaxCut.SourceAttribution
    sourceIsPlannedMeasurement :
      MaxCut.evidenceClass reactivitySource ≡ MaxCut.plannedMeasurement

open PB11ReactivityFamily public

record PB11UncertaintyBoundary : Set where
  constructor pb11-uncertainty-boundary
  field
    twoAdmissibleModelsAreDefinitionallyEqual : Bool
    twoAdmissibleModelsAreDefinitionallyEqualIsFalse :
      twoAdmissibleModelsAreDefinitionallyEqual ≡ false

    plannedMeasurementSelectsModelNow : Bool
    plannedMeasurementSelectsModelNowIsFalse :
      plannedMeasurementSelectsModelNow ≡ false

    modelIndexMustReachReactivity : Bool
    modelIndexMustReachReactivityIsTrue :
      modelIndexMustReachReactivity ≡ true

canonicalPB11UncertaintyBoundary : PB11UncertaintyBoundary
canonicalPB11UncertaintyBoundary =
  pb11-uncertainty-boundary false refl false refl true refl

------------------------------------------------------------------------
-- SAME-STATE POWER BALANCE
--
-- Natural-number quanta make the accounting identity executable while leaving
-- SI conversion, uncertainty and physical values to the literal evidence
-- package.
------------------------------------------------------------------------

record QuantisedPowerBalance : Set where
  constructor quantised-power-balance
  field
    fusionPower : Nat
    radiationLoss : Nat
    transportLoss : Nat
    sustainPower : Nat
    conversionLoss : Nat
    usefulPower : Nat
    usefulPowerPredecessor : Nat
    usefulPowerPositive : usefulPower ≡ suc usefulPowerPredecessor
    conservation :
      fusionPower ≡
      usefulPower +
      (radiationLoss +
      (transportLoss +
      (sustainPower + conversionLoss)))

open QuantisedPowerBalance public

canonicalPositivePowerBalanceFixture : QuantisedPowerBalance
canonicalPositivePowerBalanceFixture =
  quantised-power-balance
    15
    2
    3
    4
    5
    1
    0
    refl
    refl

record QuantisedNozzleClosure : Set where
  constructor quantised-nozzle-closure
  field
    massFlow : Nat
    exhaustVelocity : Nat
    thrust : Nat
    doubledJetPower : Nat
    standardGravityCode : Nat
    specificImpulseCode : Nat
    thrustIdentity : thrust ≡ massFlow * exhaustVelocity
    doubledJetPowerIdentity :
      doubledJetPower ≡ massFlow * (exhaustVelocity * exhaustVelocity)
    specificImpulseIdentity :
      exhaustVelocity ≡ standardGravityCode * specificImpulseCode

open QuantisedNozzleClosure public

canonicalNozzleIdentityFixture : QuantisedNozzleClosure
canonicalNozzleIdentityFixture =
  quantised-nozzle-closure
    2 6 12 72 2 3 refl refl refl

record QuantisedSystemSpecificPower : Set where
  constructor quantised-system-specific-power
  field
    systemPower : Nat
    systemMass : Nat
    specificPower : Nat
    specificPowerIdentity :
      systemPower ≡ systemMass * specificPower

open QuantisedSystemSpecificPower public

canonicalSpecificPowerFixture : QuantisedSystemSpecificPower
canonicalSpecificPowerFixture =
  quantised-system-specific-power 20 4 5 refl

------------------------------------------------------------------------
-- NUMERICAL FIXTURES ARE REGRESSION TESTS, NOT EMPIRICAL PERFORMANCE.
------------------------------------------------------------------------

record QuantisedFixtureBoundary : Set where
  constructor quantised-fixture-boundary
  field
    arithmeticIdentityImpliesMeasuredEngine : Bool
    arithmeticIdentityImpliesMeasuredEngineIsFalse :
      arithmeticIdentityImpliesMeasuredEngine ≡ false

    positiveToyBalanceImpliesNetPositiveAneutronicFusion : Bool
    positiveToyBalanceImpliesNetPositiveAneutronicFusionIsFalse :
      positiveToyBalanceImpliesNetPositiveAneutronicFusion ≡ false

    physicalValuesRequireSourceIndexedSIClaims : Bool
    physicalValuesRequireSourceIndexedSIClaimsIsTrue :
      physicalValuesRequireSourceIndexedSIClaims ≡ true

canonicalQuantisedFixtureBoundary : QuantisedFixtureBoundary
canonicalQuantisedFixtureBoundary =
  quantised-fixture-boundary false refl false refl true refl
