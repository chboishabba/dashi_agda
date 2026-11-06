{-# OPTIONS --safe #-}
module DASHI.Geometry.GielisSIPerronOwnerWeldExact where

------------------------------------------------------------------------
-- REUSE, NOT REINVENTION:
--
-- * BIPM SI 2019, ninth edition, brochure revision 4.01, June 2026.
-- * Existing SI seven-exponent quantity carrier and
--   SIMetrologyBridge (authority/uncertainty distinct from dimensions).
-- * Exact SI speed-of-light integer from the EXISTING registered
--   numeric carrier, not an independently hard-coded physical input.
-- * Existing mechanical M/L/T dimensions and YangMillsSI conversion.
-- * Existing nonnegative finite influence powers and row-mass theorem,
--   not a second Perron-Frobenius library.
--
-- Torque has the same SI dimension as energy, but not the same
-- physical observable. Preserve its role and unit symbol (N m, not J).
--
-- NOT CLAIMED: exact spectral-radius Collatz-Wielandt proof in Agda,
-- native continuum spectral convergence, source radiometry, measurement
-- authority token, or a calibrated torque experiment.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer using (+_; -[1+_])
open import Agda.Builtin.Int using (pos)
open import Agda.Builtin.String using (String)
open import Data.Rational.Base using (ℚ; _≤_; _*_)

import DASHI.Physics.Units.SI as SI
import DASHI.Physics.Units.SIMetrologyBridge as SIMetrology
import DASHI.Physics.Units.MechanicalDimensionExact as Mechanical
import DASHI.Physics.YangMills.YangMillsSIScalingEndpointExact as MechanicalSI
import DASHI.Promotion.SIExactConstantParsedCarrierRequest as Constants
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as PerronRows
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.Foundations.R3HodgeCrossExact as Hodge
import DASHI.Physics.Foundations.ContinuousSO3Torque369BridgeExact as SO3

------------------------------------------------------------------------
-- Exact dimension and nominal-role certificates.
------------------------------------------------------------------------

data OpticalSIObservable : Set where
  sourcePower : OpticalSIObservable
  photonMomentumFlux : OpticalSIObservable
  wallTorque : OpticalSIObservable
  opticalEnergy : OpticalSIObservable
  angularImpulse : OpticalSIObservable

angularImpulseDimension : SI.Dimension
angularImpulseDimension =
  SI.dim (pos 2) SI.one SI.minusOne
    SI.zeroI SI.zeroI SI.zeroI SI.zeroI

wallTorqueDimension : SI.Dimension
wallTorqueDimension =
  MechanicalSI.mechanicalToSI Mechanical.energyDimension

angularMomentumDimension : SI.Dimension
angularMomentumDimension = angularImpulseDimension

roleDimension : OpticalSIObservable → SI.Dimension
roleDimension sourcePower = SI.Power
roleDimension photonMomentumFlux = SI.Force
roleDimension wallTorque = wallTorqueDimension
roleDimension opticalEnergy = SI.Energy
roleDimension angularImpulse = angularMomentumDimension

record RoleIndexedSIQuantity
    (role : OpticalSIObservable)
    (scale : SI.DecimalScale) : Set where
  constructor roleIndexedSI
  field
    value : SI.Quantity (roleDimension role) scale

wallTorqueHasSIDimensionEnergy :
  roleDimension wallTorque ≡ SI.Energy
wallTorqueHasSIDimensionEnergy =
  MechanicalSI.mechanicalEnergyToSI

newtonMetre : SI.Unit (roleDimension wallTorque)
newtonMetre = SI.mkUnit "N m" "newton metre (torque)"

jouleEnergy : SI.Unit (roleDimension opticalEnergy)
jouleEnergy = SI.joule

wattPower : SI.Unit (roleDimension sourcePower)
wattPower = SI.watt

newtonForce : SI.Unit (roleDimension photonMomentumFlux)
newtonForce = SI.newton

-- A measured physical value is indexed by the SI dimension and its decimal
-- scale; source, version and uncertainty remain inside the original type.
record OpticalMeasurement (role : OpticalSIObservable)
    (scale : SI.DecimalScale) : Set where
  constructor opticalMeasurement
  field
    measured : SI.Measurement (roleDimension role) scale

-- No coercion from a joule-valued energy role to wall torque is defined,
-- even though the exponent vectors agree.
zeroWallTorque : RoleIndexedSIQuantity wallTorque SI.unitScale
zeroWallTorque = roleIndexedSI SI.zeroQ

zeroOpticalEnergy : RoleIndexedSIQuantity opticalEnergy SI.unitScale
zeroOpticalEnergy = roleIndexedSI SI.zeroQ

------------------------------------------------------------------------
-- Dimensional product on the PREEXISTING Buckingham mechanical algebra.
-- Power / speed = force, and force x lever arm = torque.
-- This proves units, not a constitutive law relating the magnitudes.
------------------------------------------------------------------------

inverseSpeedDimension : Mechanical.MechanicalDimension
inverseSpeedDimension =
  Mechanical.dimension
    (+ zero) -[1+ zero ] (+ (suc zero))

forceFromPowerOverSpeed :
  Mechanical._⊗ᴰ_
    Mechanical.powerDimension
    inverseSpeedDimension
  ≡
  Mechanical.dimension
    (+ (suc zero)) (+ (suc zero))
    -[1+ suc zero ]
forceFromPowerOverSpeed = refl

torqueFromPowerOverSpeedAndRadius :
  Mechanical._⊗ᴰ_
    (Mechanical._⊗ᴰ_
      Mechanical.powerDimension
      inverseSpeedDimension)
    Mechanical.lengthDimension
  ≡ Mechanical.energyDimension
torqueFromPowerOverSpeedAndRadius = refl

mechanicalOpticalTorqueIsSI :
  MechanicalSI.mechanicalToSI
    (Mechanical._⊗ᴰ_
      (Mechanical._⊗ᴰ_
        Mechanical.powerDimension
        inverseSpeedDimension)
      Mechanical.lengthDimension)
  ≡ SI.Energy
mechanicalOpticalTorqueIsSI = refl

angularImpulseIsDistinctFromPower :
  roleDimension angularImpulse ≡
  SI.dim (pos 2) SI.one SI.minusOne
    SI.zeroI SI.zeroI SI.zeroI SI.zeroI
angularImpulseIsDistinctFromPower = refl


------------------------------------------------------------------------
-- PAY THE MAGNITUDE TRANSPORT, not only the dimension-labelled target.
-- The payload uses the existing dimension-indexed Mechanical.Quantity
-- and its multiplyQuantity owner; the SI conversion comes from the
-- existing YangMillsSIScalingEndpointExact bridge. No unitless
-- scalar is silently called a measured optical watt.
------------------------------------------------------------------------

inverseSpeedQuantity : Set
inverseSpeedQuantity =
  Mechanical.Quantity ℚ inverseSpeedDimension

powerQuantity : Set
powerQuantity =
  Mechanical.Quantity ℚ Mechanical.powerDimension

radiusQuantity : Set
radiusQuantity =
  Mechanical.Quantity ℚ Mechanical.lengthDimension

modelOpticalForce :
  powerQuantity →
  inverseSpeedQuantity →
  Mechanical.Quantity ℚ
    (Mechanical._⊗ᴰ_ Mechanical.powerDimension
      inverseSpeedDimension)
modelOpticalForce power inverseSpeed =
  Mechanical.multiplyQuantity _*_ power inverseSpeed

modelOpticalTorqueRaw :
  powerQuantity →
  inverseSpeedQuantity →
  radiusQuantity →
  Mechanical.Quantity ℚ
    (Mechanical._⊗ᴰ_
      (Mechanical._⊗ᴰ_ Mechanical.powerDimension
        inverseSpeedDimension)
      Mechanical.lengthDimension)
modelOpticalTorqueRaw power inverseSpeed radius =
  Mechanical.multiplyQuantity _*_
    (modelOpticalForce power inverseSpeed) radius

modelOpticalTorque :
  powerQuantity →
  inverseSpeedQuantity →
  radiusQuantity →
  Mechanical.Quantity ℚ Mechanical.energyDimension
modelOpticalTorque power inverseSpeed radius =
  subst (Mechanical.Quantity ℚ)
    torqueFromPowerOverSpeedAndRadius
    (modelOpticalTorqueRaw power inverseSpeed radius)

modelOpticalTorqueHasActualMagnitude :
  ∀ (power : ℚ) (inverseSpeed : ℚ) (radius : ℚ) →
  Mechanical.magnitude
    (modelOpticalTorque
      (Mechanical.quantity power)
      (Mechanical.quantity inverseSpeed)
      (Mechanical.quantity radius))
  ≡ (power * inverseSpeed) * radius
modelOpticalTorqueHasActualMagnitude power inverseSpeed radius = refl

modelOpticalTorqueInExistingSI :
  powerQuantity →
  inverseSpeedQuantity →
  radiusQuantity →
  MechanicalSI.SIIndexedQuantity ℚ SI.Energy
modelOpticalTorqueInExistingSI power inverseSpeed radius =
  MechanicalSI.mechanicalQuantityToSI
    (modelOpticalTorque power inverseSpeed radius)

modelOpticalTorqueSIMagnitude :
  ∀ (power : ℚ) (inverseSpeed : ℚ) (radius : ℚ) →
  MechanicalSI.magnitude
    (modelOpticalTorqueInExistingSI
      (Mechanical.quantity power)
      (Mechanical.quantity inverseSpeed)
      (Mechanical.quantity radius))
  ≡ (power * inverseSpeed) * radius
modelOpticalTorqueSIMagnitude power inverseSpeed radius = refl

-- SI and MLT dimension equality is a genuine type-indexed transport.
-- A physical sample requires (among other things) a calibrated P,
-- source direction distribution, actual wall reflectivity, normal and
-- hit position; none is introduced as an equality by this construction.

------------------------------------------------------------------------
-- Canonical exact speed-of-light carrier, with no fabricated authority.
------------------------------------------------------------------------

speedOfLightFromExistingSIRegistry : Nat
speedOfLightFromExistingSIRegistry =
  Constants.ExactIntegerTextCarrier.absoluteValue
    Constants.canonicalCMetrePerSecondIntegerCarrier

speedOfLightIsExactSIInteger :
  speedOfLightFromExistingSIRegistry ≡ 299792458
speedOfLightIsExactSIInteger = refl

canonicalMetrologyAuthority : SIMetrology.SIMetrologyAuthority
canonicalMetrologyAuthority = SIMetrology.siMetrologyAuthority

-- Dimensions/formal definitions are NOT experimental calibration.
data EmpiricalOpticalCalibration : Set where

cannotSupplyCalibrationFromSIType :
  EmpiricalOpticalCalibration → OpticalMeasurement wallTorque SI.unitScale
cannotSupplyCalibrationFromSIType ()

------------------------------------------------------------------------
-- Existing nonnegative finite influence matrix algebra and spectral boundary.
--
-- The relevant positive matrix owner already proves power-row bounds.
-- Do not mistake 'Collatz' odd/even integer dynamics for
-- Collatz-Wielandt's variational spectral-radius theorem.
------------------------------------------------------------------------

finiteMatrixPowersReuse :
  ∀ {Site : Set}
    (dataSet : PerronRows.NonnegativeFiniteInfluenceMajorant Site) →
  Nat → PerronRows.Matrix Site
finiteMatrixPowersReuse =
  PerronRows.majorantPowerPositive

finiteInfluenceRowPowerBoundReuse :
  ∀ {Site}
    {dataSet : PerronRows.NonnegativeFiniteInfluenceMajorant Site} →
  PerronRows.NonnegativeInfluencePowers dataSet →
  ∀ n x →
  Sums.sumRational
    (PerronRows.sites dataSet)
    (PerronRows.majorantPowerPositive dataSet n x)
  ≤ PerronRows.rationalPower
      (PerronRows.rowMass dataSet)
      (suc n)
finiteInfluenceRowPowerBoundReuse =
  PerronRows.positivePowerRowMassBound

-- The actual finite-raster proof uses A=(4I-B)/h^2 and a strictly
-- positive rational test vector q:
-- min_i [(4q_i-(Bq)_i)/(h^2q_i)]
--   <= lambda_min(A) <=
-- max_i [(4q_i-(Bq)_i)/(h^2q_i)].
--
-- This is checked by exact integer rational arithmetic in
-- scripts/gielis_raster_fd_positivity_certificate.py.
-- A general Agda proof needs the missing positive spectral-radius owner;
-- no statement-only record is labeled an accepted theorem here.

existingR3CrossOwner : Bool
existingR3CrossOwner = Hodge.r3HodgeWedgeCrossClosed

existingContinuousSO3Convention : Bool
existingContinuousSO3Convention =
  SO3.existingSO3ContinuousConventionReused

physicalTorqueMeasuredHere : Bool
physicalTorqueMeasuredHere = false
