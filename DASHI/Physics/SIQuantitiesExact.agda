module DASHI.Physics.SIQuantitiesExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Bureau International des Poids et Mesures (BIPM),
-- The International System of Units (SI), 9th edition (2019),
-- current official brochure revision 4.01 (June 2026).
-- DOI: 10.59161/AUEZ1291.
--
-- Source boundary:
-- The BIPM supplies the SI base quantities/units and derived-unit relations.
-- The indexed Agda carrier below is a DASHI formal reconstruction used to make
-- dimensional compatibility explicit across physics, chemistry and LES.
------------------------------------------------------------------------

-- Signed exponent: nonnegative n means +n; negative n means -(n+1).
data Exponent : Set where
  nonnegative : Nat → Exponent
  negative : Nat → Exponent

zeroE : Exponent
zeroE = nonnegative 0

oneE : Exponent
oneE = nonnegative 1

twoE : Exponent
twoE = nonnegative 2

threeE : Exponent
threeE = nonnegative 3

fourE : Exponent
fourE = nonnegative 4

minusOneE : Exponent
minusOneE = negative 0

minusTwoE : Exponent
minusTwoE = negative 1

minusThreeE : Exponent
minusThreeE = negative 2

-- Canonical seven-base-dimension vector, ordered
-- length, mass, time, electric current, thermodynamic temperature,
-- amount of substance, luminous intensity.
record Dimension : Set where
  constructor dimension
  field
    lengthExponent : Exponent
    massExponent : Exponent
    timeExponent : Exponent
    currentExponent : Exponent
    temperatureExponent : Exponent
    amountExponent : Exponent
    luminousExponent : Exponent

open Dimension public

dimensionless : Dimension
dimensionless = dimension zeroE zeroE zeroE zeroE zeroE zeroE zeroE

lengthDimension : Dimension
lengthDimension = dimension oneE zeroE zeroE zeroE zeroE zeroE zeroE

massDimension : Dimension
massDimension = dimension zeroE oneE zeroE zeroE zeroE zeroE zeroE

timeDimension : Dimension
timeDimension = dimension zeroE zeroE oneE zeroE zeroE zeroE zeroE

electricCurrentDimension : Dimension
electricCurrentDimension = dimension zeroE zeroE zeroE oneE zeroE zeroE zeroE

temperatureDimension : Dimension
temperatureDimension = dimension zeroE zeroE zeroE zeroE oneE zeroE zeroE

amountDimension : Dimension
amountDimension = dimension zeroE zeroE zeroE zeroE zeroE oneE zeroE

luminousIntensityDimension : Dimension
luminousIntensityDimension = dimension zeroE zeroE zeroE zeroE zeroE zeroE oneE

------------------------------------------------------------------------
-- Derived dimensions needed by the present LES physics/chemistry cutset.
------------------------------------------------------------------------

areaDimension : Dimension
areaDimension = dimension twoE zeroE zeroE zeroE zeroE zeroE zeroE

volumeDimension : Dimension
volumeDimension = dimension threeE zeroE zeroE zeroE zeroE zeroE zeroE

velocityDimension : Dimension
velocityDimension = dimension oneE zeroE minusOneE zeroE zeroE zeroE zeroE

accelerationDimension : Dimension
accelerationDimension = dimension oneE zeroE minusTwoE zeroE zeroE zeroE zeroE

densityDimension : Dimension
densityDimension = dimension minusThreeE oneE zeroE zeroE zeroE zeroE zeroE

pressureDimension : Dimension
pressureDimension = dimension minusOneE oneE minusTwoE zeroE zeroE zeroE zeroE

dynamicViscosityDimension : Dimension
dynamicViscosityDimension = dimension minusOneE oneE minusOneE zeroE zeroE zeroE zeroE

volumetricFlowRateDimension : Dimension
volumetricFlowRateDimension = dimension threeE zeroE minusOneE zeroE zeroE zeroE zeroE

diffusionCoefficientDimension : Dimension
diffusionCoefficientDimension = dimension twoE zeroE minusOneE zeroE zeroE zeroE zeroE

amountConcentrationDimension : Dimension
amountConcentrationDimension = dimension minusThreeE zeroE zeroE zeroE zeroE oneE zeroE

energyDimension : Dimension
energyDimension = dimension twoE oneE minusTwoE zeroE zeroE zeroE zeroE

powerDimension : Dimension
powerDimension = dimension twoE oneE minusThreeE zeroE zeroE zeroE zeroE

electricChargeDimension : Dimension
electricChargeDimension = dimension zeroE zeroE oneE oneE zeroE zeroE zeroE

voltageDimension : Dimension
voltageDimension = dimension twoE oneE minusThreeE minusOneE zeroE zeroE zeroE

electricResistanceDimension : Dimension
electricResistanceDimension = dimension twoE oneE minusThreeE minusTwoE zeroE zeroE zeroE

electricConductanceDimension : Dimension
electricConductanceDimension = dimension minusTwoE minusOneE threeE twoE zeroE zeroE zeroE

capacitanceDimension : Dimension
capacitanceDimension = dimension minusTwoE minusOneE fourE twoE zeroE zeroE zeroE

electricFieldDimension : Dimension
electricFieldDimension = dimension oneE oneE minusThreeE minusOneE zeroE zeroE zeroE

------------------------------------------------------------------------
-- Quantity values are indexed by dimension.  The scalar representation is an
-- application parameter: exact rationals, intervals, floating values, measured
-- values with uncertainty, etc. can reuse the same dimensional type.
------------------------------------------------------------------------

record Quantity (Scalar : Set) (dimension : Dimension) : Set where
  constructor quantity
  field
    magnitude : Scalar

open Quantity public

Current : Set → Set
Current Scalar = Quantity Scalar electricCurrentDimension

Charge : Set → Set
Charge Scalar = Quantity Scalar electricChargeDimension

Voltage : Set → Set
Voltage Scalar = Quantity Scalar voltageDimension

Resistance : Set → Set
Resistance Scalar = Quantity Scalar electricResistanceDimension

Conductance : Set → Set
Conductance Scalar = Quantity Scalar electricConductanceDimension

Capacitance : Set → Set
Capacitance Scalar = Quantity Scalar capacitanceDimension

ElectricField : Set → Set
ElectricField Scalar = Quantity Scalar electricFieldDimension

Concentration : Set → Set
Concentration Scalar = Quantity Scalar amountConcentrationDimension

DiffusionCoefficient : Set → Set
DiffusionCoefficient Scalar = Quantity Scalar diffusionCoefficientDimension

Velocity : Set → Set
Velocity Scalar = Quantity Scalar velocityDimension

Pressure : Set → Set
Pressure Scalar = Quantity Scalar pressureDimension

Density : Set → Set
Density Scalar = Quantity Scalar densityDimension

DynamicViscosity : Set → Set
DynamicViscosity Scalar = Quantity Scalar dynamicViscosityDimension

VolumetricFlowRate : Set → Set
VolumetricFlowRate Scalar = Quantity Scalar volumetricFlowRateDimension

------------------------------------------------------------------------
-- Stable source and architecture boundary.
------------------------------------------------------------------------

siSourceDOI : String
siSourceDOI = "10.59161/AUEZ1291"

record SIQuantityBoundary : Set where
  constructor siQuantityBoundary
  field
    sameScalarImpliesSameDimension : Bool
    sameScalarImpliesSameDimensionIsFalse : sameScalarImpliesSameDimension ≡ false

    unitLabelAloneProvesPhysicalLaw : Bool
    unitLabelAloneProvesPhysicalLawIsFalse : unitLabelAloneProvesPhysicalLaw ≡ false

    dimensionallyTypedQuantityIsMeasuredQuantity : Bool
    dimensionallyTypedQuantityIsMeasuredQuantityIsFalse :
      dimensionallyTypedQuantityIsMeasuredQuantity ≡ false

    siTypingCanBeSharedAcrossDomains : Bool
    siTypingCanBeSharedAcrossDomainsIsTrue : siTypingCanBeSharedAcrossDomains ≡ true

canonicalSIQuantityBoundary : SIQuantityBoundary
canonicalSIQuantityBoundary =
  siQuantityBoundary
    false refl
    false refl
    false refl
    true refl
