{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.Rocketdyne1974DimensionedPhysicsKernelExact where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Tiny, explicit dimensional AST. This enforces well-formed equations,
-- rather than allowing arbitrary unit-tag strings to cancel by assertion.
-- A dimensionally sound formula does NOT establish a calibrated engine model.
------------------------------------------------------------------------

data D : Set where
  force massRate speed time acceleration area pressure
    dimensionless temperatureDelta stress length
    elasticModulus expansionCoefficient : D

data E : D → Set where
  input : {d : D} → String → E d
  momentumFlux : E massRate → E speed → E force
  pressureDifference : E pressure → E pressure → E pressure
  pressureArea : E pressure → E area → E force
  forceSum : E force → E force → E force
  massFlowGravity : E massRate → E acceleration → E force
  forceOverMassFlowGravity : E force → E force → E time
  pressureThroatOverMassFlow : E pressure → E area → E massRate → E speed
  thrustOverChamberForce : E force → E force → E dimensionless
  accelerationTimesTime : E acceleration → E time → E speed
  radialPressureStress : E pressure → E length → E length → E stress
  thermalExpansionStress : E elasticModulus → E expansionCoefficient
                        → E temperatureDelta → E stress
  stressSum : E stress → E stress → E stress

-- Canonical RCS formula:
-- F = mdot v_exit + (p_exit - p_ambient) A_exit.
-- Same-point calibration and nozzle-pressure measurements still owed.
mdot : E massRate
mdot = input "measured total mass flow in kg/s"

vExit : E speed
vExit = input "measured or modelled nozzle exit velocity in m/s"

pExit : E pressure
pExit = input "exit pressure in Pa absolute"

pAmbient : E pressure
pAmbient = input "ambient pressure in Pa absolute"

aExit : E area
aExit = input "exit area in m^2"

pChamber : E pressure
pChamber = input "chamber pressure in Pa absolute"

aThroat : E area
aThroat = input "throat area in m^2"

gStandard : E acceleration
gStandard = input "standard gravity 9.80665 m/s^2"

thrustSI : E force
thrustSI = forceSum (momentumFlux mdot vExit)
                    (pressureArea (pressureDifference pExit pAmbient) aExit)

specificImpulseSI : E time
specificImpulseSI =
  forceOverMassFlowGravity thrustSI (massFlowGravity mdot gStandard)

characteristicVelocitySI : E speed
characteristicVelocitySI =
  pressureThroatOverMassFlow pChamber aThroat mdot

thrustCoefficientSI : E dimensionless
thrustCoefficientSI =
  thrustOverChamberForce thrustSI (pressureArea pChamber aThroat)

effectiveExhaustVelocitySI : E speed
effectiveExhaustVelocitySI = accelerationTimesTime gStandard specificImpulseSI

-- A source-backed, exact conversion using nominal printed Isp numbers:
-- c_eff = standard gravity * Isp. c_eff includes pressure thrust, and is
-- NOT necessarily the physical exhaust velocity at the nozzle plane.
-- 9.80665 m/s^2 * 294.4 s = 2887.07776 m/s.
-- 9.80665 m/s^2 * 290.0 s = 2843.9285 m/s.
-- The arithmetical results cannot establish mass flow or internal geometry.
g0FiveDecimalNumerator : Nat
g0FiveDecimalNumerator = 980665

ispUnsaturatedTenths : Nat
ispUnsaturatedTenths = 2944

ispSaturatedTenths : Nat
ispSaturatedTenths = 2900

unsaturatedEffectiveSpeedSI1e6 : Nat
unsaturatedEffectiveSpeedSI1e6 = 2887077760

saturatedEffectiveSpeedSI1e6 : Nat
saturatedEffectiveSpeedSI1e6 = 2843928500

unsaturatedSpeedCalculation :
  g0FiveDecimalNumerator * ispUnsaturatedTenths ≡
  unsaturatedEffectiveSpeedSI1e6
unsaturatedSpeedCalculation = refl

saturatedSpeedCalculation :
  g0FiveDecimalNumerator * ispSaturatedTenths ≡
  saturatedEffectiveSpeedSI1e6
saturatedSpeedCalculation = refl

-- If the nozzle is treated as a locally thin-walled cylindrical shell,
-- hoop-stress scales as pressure * local radius / thickness. This is a
-- conditional IDEALISATION only; real diverging nozzles need axial/hoop,
-- thermal, bending, discontinuity and buckling analysis.
chamberPressureGauge : E pressure
chamberPressureGauge = input "differential shell pressure in Pa"

localNozzleRadius : E length
localNozzleRadius = input "local shell radius in m"

localNozzleThickness : E length
localNozzleThickness = input "local shell thickness in m"

hoopStressIdealisation : E stress
hoopStressIdealisation =
  radialPressureStress chamberPressureGauge
                       localNozzleRadius localNozzleThickness

youngsModulusAtTemperature : E elasticModulus
youngsModulusAtTemperature = input "E(T) in Pa, Haynes-25 specific"

thermalExpansionAtTemperature : E expansionCoefficient
thermalExpansionAtTemperature = input "alpha(T) in 1/K"

constrainedTemperatureDifference : E temperatureDelta
constrainedTemperatureDifference = input "actual through-wall/axial delta T in K"

thermalStressIdealisation : E stress
thermalStressIdealisation =
  thermalExpansionStress youngsModulusAtTemperature
                         thermalExpansionAtTemperature
                         constrainedTemperatureDifference

combinedIdealisedStress : E stress
combinedIdealisedStress = stressSum hoopStressIdealisation
                                    thermalStressIdealisation

-- Physical inference cannot be constructed by assigning arbitrary pressure
-- or temperature terms to different dimensions. Stress exceedance needs a
-- measured/calibrated stress and temperature-dependent allowable law.
record StressFailurePayment : Set where
  constructor stress-failure-payment
  field
    experiment : String
    geometryRevision : String
    measuredWallTemperatureHistory : String
    mechanicalLoads : String
    validatedMaterialLaw : String
    sourceForAppliedStress : String
    sourceForAllowableStress : String
    quantifiedUncertainty : String
    observedFractureMode : String
    independentValidation : String

-- The paper's failure observation cannot populate these fields as numeric
-- calibrated stress inputs; no canonical StressFailurePayment is exported.
