module DASHI.Environment.PhotosyntheticAssimilationValidationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Environment.PlantHydraulicAtmosphereCarbonCouplingExact as Plant
import DASHI.Environment.PhotosyntheticLightOptimizationExact as LightOpt

------------------------------------------------------------------------
-- PREDICTED / MEASURED ASSIMILATION VALIDATION
--
-- This closes the experiment-facing carrier only.  It does not supply a
-- concrete dataset, chamber protocol, gas-exchange instrument, or statistical
-- criterion. Those remain producer/source coordinates.
------------------------------------------------------------------------

record AssimilationValidationAlgebra (Scalar : Set) : Set₁ where
  constructor assimilation-validation-algebra
  field
    _≤_ : Scalar → Scalar → Set

open AssimilationValidationAlgebra public

record PhotosyntheticAssimilationFixture
    {Scalar : Set}
    (leaf : Plant.LeafGasExchangeReceipt) : Set₁ where
  constructor photosynthetic-assimilation-fixture
  field
    FixtureState : Set
    leafState : FixtureState → Plant.LeafState leaf
    atmosphereState : FixtureState → Plant.AtmosphereState leaf
    predictedAssimilation : FixtureState → Scalar
    measuredAssimilation : FixtureState → Scalar
    comparison : Scalar → Scalar → Scalar
    residual : FixtureState → Scalar
    residualLaw :
      (state : FixtureState) →
      residual state ≡ comparison (predictedAssimilation state) (measuredAssimilation state)
    sourceSpectrumReference : String
    canopyGeometryReference : String
    gasExchangeInstrumentReference : String
    temperatureHumidityCO2Reference : String
    biologicalSpecimenReference : String
    datasetDigest : String

open PhotosyntheticAssimilationFixture public

record CertifiedAssimilationValidation
    {Scalar : Set}
    {leaf : Plant.LeafGasExchangeReceipt}
    (algebra : AssimilationValidationAlgebra Scalar)
    (fixture : PhotosyntheticAssimilationFixture {Scalar = Scalar} leaf) : Set₁ where
  constructor certified-assimilation-validation
  field
    allowedResidual : Scalar
    everyFixtureResidualAdmissible :
      (state : FixtureState fixture) →
      _≤_ algebra (residual fixture state) allowedResidual
    heldOutSplitReference : String
    uncertaintyReference : String
    modelDiscrepancyReference : String
    validationProgrammeReference : String

open CertifiedAssimilationValidation public

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data CalibrationFitIsHeldOutAssimilationValidation : Set where
calibrationFitIsNotHeldOutAssimilationValidation :
  CalibrationFitIsHeldOutAssimilationValidation → ⊥
calibrationFitIsNotHeldOutAssimilationValidation ()

data GoodAssimilationResidualProvesOptimalDeployment : Set where
goodAssimilationResidualDoesNotProveOptimalDeployment :
  GoodAssimilationResidualProvesOptimalDeployment → ⊥
goodAssimilationResidualDoesNotProveOptimalDeployment ()

data OneSpeciesFixtureValidatesAllPlants : Set where
oneSpeciesFixtureDoesNotValidateAllPlants : OneSpeciesFixtureValidatesAllPlants → ⊥
oneSpeciesFixtureDoesNotValidateAllPlants ()
