module DASHI.Physics.Units.SI where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Bureau International des Poids et Mesures (BIPM),
-- The International System of Units (SI), 9th edition (2019),
-- official brochure revision 4.01 (June 2026).
-- DOI: 10.59161/AUEZ1291.
--
-- Source boundary:
-- BIPM supplies the SI base quantities/units and derived-unit relations.
-- The type-indexed Agda representation is a DASHI formal reconstruction.
------------------------------------------------------------------------

record Dimension : Set where
  constructor dim
  field
    L M T I Θ N J : Int

one : Int
one = pos (suc zero)

zeroI : Int
zeroI = pos zero

minusOne : Int
minusOne = negsuc zero

minusTwo : Int
minusTwo = negsuc (suc zero)

minusThree : Int
minusThree = negsuc (suc (suc zero))

Dimensionless Length Mass Time Current Temperature Amount LuminousIntensity : Dimension
Dimensionless     = dim zeroI zeroI zeroI zeroI zeroI zeroI zeroI
Length            = dim one   zeroI zeroI zeroI zeroI zeroI zeroI
Mass              = dim zeroI one   zeroI zeroI zeroI zeroI zeroI
Time              = dim zeroI zeroI one   zeroI zeroI zeroI zeroI
Current           = dim zeroI zeroI zeroI one   zeroI zeroI zeroI
Temperature       = dim zeroI zeroI zeroI zeroI one   zeroI zeroI
Amount            = dim zeroI zeroI zeroI zeroI zeroI one   zeroI
LuminousIntensity = dim zeroI zeroI zeroI zeroI zeroI zeroI one

Area Volume Frequency Velocity Acceleration Force Pressure Energy Power Charge Voltage Capacitance Resistance Conductance MagneticFlux MagneticFluxDensity Inductance LuminousFlux Illuminance Activity AbsorbedDose CatalyticActivity : Dimension
Area                = dim (pos 2) zeroI zeroI zeroI zeroI zeroI zeroI
Volume              = dim (pos 3) zeroI zeroI zeroI zeroI zeroI zeroI
Frequency           = dim zeroI zeroI minusOne zeroI zeroI zeroI zeroI
Velocity            = dim one zeroI minusOne zeroI zeroI zeroI zeroI
Acceleration        = dim one zeroI minusTwo zeroI zeroI zeroI zeroI
Force               = dim one one minusTwo zeroI zeroI zeroI zeroI
Pressure            = dim minusOne one minusTwo zeroI zeroI zeroI zeroI
Energy              = dim (pos 2) one minusTwo zeroI zeroI zeroI zeroI
Power               = dim (pos 2) one minusThree zeroI zeroI zeroI zeroI
Charge              = dim zeroI zeroI one one zeroI zeroI zeroI
Voltage             = dim (pos 2) one minusThree minusOne zeroI zeroI zeroI
Capacitance         = dim minusTwo minusOne (pos 4) (pos 2) zeroI zeroI zeroI
Resistance          = dim (pos 2) one minusThree minusTwo zeroI zeroI zeroI
Conductance         = dim minusTwo minusOne (pos 3) (pos 2) zeroI zeroI zeroI
MagneticFlux        = dim (pos 2) one minusTwo minusOne zeroI zeroI zeroI
MagneticFluxDensity = dim zeroI one minusTwo minusOne zeroI zeroI zeroI
Inductance          = dim (pos 2) one minusTwo minusTwo zeroI zeroI zeroI
LuminousFlux        = LuminousIntensity
Illuminance         = dim minusTwo zeroI zeroI zeroI zeroI zeroI one
Activity            = Frequency
AbsorbedDose        = dim (pos 2) zeroI minusTwo zeroI zeroI zeroI zeroI
CatalyticActivity   = dim zeroI zeroI minusOne zeroI zeroI one zeroI

MolarEnergy MolarEntropy MolarConcentration : Dimension
MolarEnergy        = dim (pos 2) one minusTwo zeroI zeroI minusOne zeroI
MolarEntropy       = dim (pos 2) one minusTwo zeroI minusOne minusOne zeroI
MolarConcentration = dim minusThree zeroI zeroI zeroI zeroI one zeroI

------------------------------------------------------------------------
-- Additional coherent dimensions needed by fluid / transport / bioelectric
-- applications.  These are dimension expressions, not claims of constitutive
-- law or measured value.
------------------------------------------------------------------------

Density DynamicViscosity VolumetricFlowRate DiffusionCoefficient ElectricField : Dimension
Density              = dim minusThree one zeroI zeroI zeroI zeroI zeroI
DynamicViscosity     = dim minusOne one minusOne zeroI zeroI zeroI zeroI
VolumetricFlowRate   = dim (pos 3) zeroI minusOne zeroI zeroI zeroI zeroI
DiffusionCoefficient = dim (pos 2) zeroI minusOne zeroI zeroI zeroI zeroI
ElectricField        = dim one one minusThree minusOne zeroI zeroI zeroI

------------------------------------------------------------------------
-- Decimal scale and exact signed fixed-point quantity.
------------------------------------------------------------------------

record DecimalScale : Set where
  constructor tenTo
  field exponent : Int

unitScale deciScale centiScale milliScale microScale nanoScale : DecimalScale
unitScale  = tenTo zeroI
deciScale  = tenTo minusOne
centiScale = tenTo minusTwo
milliScale = tenTo minusThree
microScale = tenTo (negsuc 5)
nanoScale  = tenTo (negsuc 8)

record Quantity (d : Dimension) (s : DecimalScale) : Set where
  constructor quantity
  field
    negative : Bool
    magnitude : Nat

zeroQ : ∀ {d s} → Quantity d s
zeroQ = quantity false zero

negQ : ∀ {d s} → Nat → Quantity d s
negQ n = quantity true n

posQ : ∀ {d s} → Nat → Quantity d s
posQ n = quantity false n

------------------------------------------------------------------------
-- SI base and named derived units.
------------------------------------------------------------------------

record Unit (d : Dimension) : Set where
  constructor mkUnit
  field symbol name : String

metre : Unit Length
metre = mkUnit "m" "metre"

kilogram : Unit Mass
kilogram = mkUnit "kg" "kilogram"

second : Unit Time
second = mkUnit "s" "second"

ampere : Unit Current
ampere = mkUnit "A" "ampere"

kelvin : Unit Temperature
kelvin = mkUnit "K" "kelvin"

mole : Unit Amount
mole = mkUnit "mol" "mole"

candela : Unit LuminousIntensity
candela = mkUnit "cd" "candela"

hertz : Unit Frequency
hertz = mkUnit "Hz" "hertz"

newton : Unit Force
newton = mkUnit "N" "newton"

pascal : Unit Pressure
pascal = mkUnit "Pa" "pascal"

joule : Unit Energy
joule = mkUnit "J" "joule"

watt : Unit Power
watt = mkUnit "W" "watt"

coulomb : Unit Charge
coulomb = mkUnit "C" "coulomb"

volt : Unit Voltage
volt = mkUnit "V" "volt"

farad : Unit Capacitance
farad = mkUnit "F" "farad"

ohm : Unit Resistance
ohm = mkUnit "Ω" "ohm"

siemens : Unit Conductance
siemens = mkUnit "S" "siemens"

weber : Unit MagneticFlux
weber = mkUnit "Wb" "weber"

tesla : Unit MagneticFluxDensity
tesla = mkUnit "T" "tesla"

henry : Unit Inductance
henry = mkUnit "H" "henry"

lumen : Unit LuminousFlux
lumen = mkUnit "lm" "lumen"

lux : Unit Illuminance
lux = mkUnit "lx" "lux"

becquerel : Unit Activity
becquerel = mkUnit "Bq" "becquerel"

gray : Unit AbsorbedDose
gray = mkUnit "Gy" "gray"

sievert : Unit AbsorbedDose
sievert = mkUnit "Sv" "sievert"

katal : Unit CatalyticActivity
katal = mkUnit "kat" "katal"

joulePerMole : Unit MolarEnergy
joulePerMole = mkUnit "J mol⁻¹" "joule per mole"

joulePerMoleKelvin : Unit MolarEntropy
joulePerMoleKelvin = mkUnit "J mol⁻¹ K⁻¹" "joule per mole kelvin"

molePerCubicMetre : Unit MolarConcentration
molePerCubicMetre = mkUnit "mol m⁻³" "mole per cubic metre"

kilogramPerCubicMetre : Unit Density
kilogramPerCubicMetre = mkUnit "kg m⁻³" "kilogram per cubic metre"

pascalSecond : Unit DynamicViscosity
pascalSecond = mkUnit "Pa s" "pascal second"

cubicMetrePerSecond : Unit VolumetricFlowRate
cubicMetrePerSecond = mkUnit "m³ s⁻¹" "cubic metre per second"

squareMetrePerSecond : Unit DiffusionCoefficient
squareMetrePerSecond = mkUnit "m² s⁻¹" "square metre per second"

voltPerMetre : Unit ElectricField
voltPerMetre = mkUnit "V m⁻¹" "volt per metre"

------------------------------------------------------------------------
-- Typed measurement and authority metadata.
------------------------------------------------------------------------

record Measurement (d : Dimension) (s : DecimalScale) : Set where
  constructor measurement
  field
    value : Quantity d s
    uncertainty : Nat
    unit : Unit d
    source version : String

same-dimension-only : ∀ {d s} → Quantity d s → Quantity d s → Set
same-dimension-only x y = x ≡ y → x ≡ y

same-dimension-only-proof : ∀ {d s} (x y : Quantity d s) → same-dimension-only x y
same-dimension-only-proof x y eq = eq

siSourceDOI : String
siSourceDOI = "10.59161/AUEZ1291"
