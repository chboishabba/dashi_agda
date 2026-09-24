{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.EinsteinEquationBidiResidualExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Geometry.NonconstantWarpedLorentzianModel as Geometry
import DASHI.Physics.Closure.DiscreteWarpedEinsteinMatterModel as Model

------------------------------------------------------------------------
-- EXECUTABLE EINSTEIN-EQUATION BIDI TEST
--
-- The finite warped model already computes both sides independently:
--
--   G_mu_nu                from the warped curvature contraction
--   T_mu_nu                from a matter-action variation.
--
-- Here we stop treating the physical coupling as a reason not to run the
-- comparison.  Instead we expose the normalized residual
--
--   R_mu_nu(kappa) = G_mu_nu - kappa T_mu_nu.
--
-- positiveUnit is the dimensionless normalized kappa = 1 fixture.  It stands
-- for a unit-normalized 8*pi*G only inside this finite fixture; it is NOT an SI
-- calibration or a continuum claim.
------------------------------------------------------------------------

data EinsteinEquationAttemptOutcome : Set where
  exactResidualZero : EinsteinEquationAttemptOutcome
  nonzeroResidualCounterexample : EinsteinEquationAttemptOutcome

sourceIsZero : Model.SourceCoefficient → Bool
sourceIsZero Model.negativeSource = false
sourceIsZero Model.zeroSource = true
sourceIsZero Model.positiveSource = false

andBool : Bool → Bool → Bool
andBool true b = b
andBool false b = false

scaleStress :
  Geometry.UnitCoefficient →
  Model.EinsteinTensor4 →
  Model.EinsteinTensor4
scaleStress coupling stress a b =
  Model.multiplyUnitSource coupling (stress a b)

einsteinEquationResidual :
  Geometry.UnitCoefficient →
  Model.EinsteinTensor4
einsteinEquationResidual coupling a b =
  Model.addSource
    (Model.computedEinsteinTensor a b)
    (Model.negateSource
      (scaleStress coupling Model.computedMatterStress a b))

allComponentsZero :
  Model.EinsteinTensor4 →
  Bool
allComponentsZero tensor =
  andBool (sourceIsZero (tensor Flat.timeAxis Flat.timeAxis))
  (andBool (sourceIsZero (tensor Flat.timeAxis Flat.xAxis))
  (andBool (sourceIsZero (tensor Flat.timeAxis Flat.yAxis))
  (andBool (sourceIsZero (tensor Flat.timeAxis Flat.zAxis))
  (andBool (sourceIsZero (tensor Flat.xAxis Flat.timeAxis))
  (andBool (sourceIsZero (tensor Flat.xAxis Flat.xAxis))
  (andBool (sourceIsZero (tensor Flat.xAxis Flat.yAxis))
  (andBool (sourceIsZero (tensor Flat.xAxis Flat.zAxis))
  (andBool (sourceIsZero (tensor Flat.yAxis Flat.timeAxis))
  (andBool (sourceIsZero (tensor Flat.yAxis Flat.xAxis))
  (andBool (sourceIsZero (tensor Flat.yAxis Flat.yAxis))
  (andBool (sourceIsZero (tensor Flat.yAxis Flat.zAxis))
  (andBool (sourceIsZero (tensor Flat.zAxis Flat.timeAxis))
  (andBool (sourceIsZero (tensor Flat.zAxis Flat.xAxis))
  (andBool (sourceIsZero (tensor Flat.zAxis Flat.yAxis))
           (sourceIsZero (tensor Flat.zAxis Flat.zAxis))))))))))))))))

classifyResidualBool : Bool → EinsteinEquationAttemptOutcome
classifyResidualBool true = exactResidualZero
classifyResidualBool false = nonzeroResidualCounterexample

runEinsteinEquationAttempt :
  Geometry.UnitCoefficient →
  EinsteinEquationAttemptOutcome
runEinsteinEquationAttempt coupling =
  classifyResidualBool (allComponentsZero (einsteinEquationResidual coupling))

normalizedEightPiGCoupling : Geometry.UnitCoefficient
normalizedEightPiGCoupling = Geometry.positiveUnit

normalizedEquationResidualPointwise :
  (a b : Flat.Axis4) →
  einsteinEquationResidual normalizedEightPiGCoupling a b
  ≡ Model.zeroSource
normalizedEquationResidualPointwise Flat.timeAxis Flat.timeAxis = refl
normalizedEquationResidualPointwise Flat.timeAxis Flat.xAxis = refl
normalizedEquationResidualPointwise Flat.timeAxis Flat.yAxis = refl
normalizedEquationResidualPointwise Flat.timeAxis Flat.zAxis = refl
normalizedEquationResidualPointwise Flat.xAxis Flat.timeAxis = refl
normalizedEquationResidualPointwise Flat.xAxis Flat.xAxis = refl
normalizedEquationResidualPointwise Flat.xAxis Flat.yAxis = refl
normalizedEquationResidualPointwise Flat.xAxis Flat.zAxis = refl
normalizedEquationResidualPointwise Flat.yAxis Flat.timeAxis = refl
normalizedEquationResidualPointwise Flat.yAxis Flat.xAxis = refl
normalizedEquationResidualPointwise Flat.yAxis Flat.yAxis = refl
normalizedEquationResidualPointwise Flat.yAxis Flat.zAxis = refl
normalizedEquationResidualPointwise Flat.zAxis Flat.timeAxis = refl
normalizedEquationResidualPointwise Flat.zAxis Flat.xAxis = refl
normalizedEquationResidualPointwise Flat.zAxis Flat.yAxis = refl
normalizedEquationResidualPointwise Flat.zAxis Flat.zAxis = refl

normalizedEquationAllComponentsZero :
  allComponentsZero
    (einsteinEquationResidual normalizedEightPiGCoupling)
  ≡ true
normalizedEquationAllComponentsZero = refl

normalizedEquationAttemptPasses :
  runEinsteinEquationAttempt normalizedEightPiGCoupling
  ≡ exactResidualZero
normalizedEquationAttemptPasses = refl

zeroCouplingTimeTimeCounterexample :
  einsteinEquationResidual Geometry.zeroUnit
    Flat.timeAxis Flat.timeAxis
  ≡ Model.positiveSource
zeroCouplingTimeTimeCounterexample = refl

zeroCouplingAttemptFails :
  runEinsteinEquationAttempt Geometry.zeroUnit
  ≡ nonzeroResidualCounterexample
zeroCouplingAttemptFails = refl

negativeCouplingTimeTimeCounterexample :
  einsteinEquationResidual Geometry.negativeUnit
    Flat.timeAxis Flat.timeAxis
  ≡ Model.positiveSource
negativeCouplingTimeTimeCounterexample = refl

negativeCouplingAttemptFails :
  runEinsteinEquationAttempt Geometry.negativeUnit
  ≡ nonzeroResidualCounterexample
negativeCouplingAttemptFails = refl

record EinsteinEquationBidiReceipt : Set where
  constructor einsteinEquationBidiReceipt
  field
    normalizedAttempt :
      runEinsteinEquationAttempt normalizedEightPiGCoupling
      ≡ exactResidualZero
    zeroCouplingRejected :
      runEinsteinEquationAttempt Geometry.zeroUnit
      ≡ nonzeroResidualCounterexample
    negativeCouplingRejected :
      runEinsteinEquationAttempt Geometry.negativeUnit
      ≡ nonzeroResidualCounterexample
    matterSourceNonzero :
      Model.computedMatterStress Flat.timeAxis Flat.timeAxis
      ≡ Model.positiveSource
    finiteBianchiResidualZero :
      Model.continuityBianchiResidual ≡ Model.zeroSource
    scope : String

open EinsteinEquationBidiReceipt public

canonicalEinsteinEquationBidiReceipt :
  EinsteinEquationBidiReceipt
canonicalEinsteinEquationBidiReceipt =
  einsteinEquationBidiReceipt
    normalizedEquationAttemptPasses
    zeroCouplingAttemptFails
    negativeCouplingAttemptFails
    Model.computedMatterSourceNonzero
    Model.computedContractedBianchi
    "Executed finite nonconstant Einstein/source residual test: normalized kappa=1 passes exactly; kappa=0 and kappa=-1 are rejected by explicit residuals. No SI calibration, continuum Einstein theorem, empirical GR validation, or GRQFT promotion follows."

physicalCalibrationStillOpen : Bool
physicalCalibrationStillOpen = true

physicalCalibrationStillOpenIsTrue :
  physicalCalibrationStillOpen ≡ true
physicalCalibrationStillOpenIsTrue = refl
