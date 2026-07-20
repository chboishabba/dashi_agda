module DASHI.Physics.Units.SI where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Type-indexed SI dimensions.
--
-- Exponent order:
-- length, mass, time, electric current, thermodynamic temperature,
-- amount of substance, luminous intensity.

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
-- Decimal scale and exact signed fixed-point quantity.

record DecimalScale : Set where
  constructor tenTo
  field exponent : Int

unitScale deciScale centiScale milliScale microScale nanoScale : DecimalScale
unitScale  = tenTo zeroI
deciScale  = tenTo minusOne
centiScale = tenTo minusTwo
milliScale = tenTo minusThree
microScale = tenTo (negsuc (pos 3))
nanoScale  = tenTo (negsuc (pos 8))

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
-- SI base and named derived units. The dimension index prevents mixing units
-- of unlike physical kind even when their numeric carriers coincide.

record Unit (d : Dimension) : Set where
  constructor unit
  field symbol name : String

metre : Unit Length
metre = unit "m" "metre"

kilogram : Unit Mass
kilogram = unit "kg" "kilogram"

second : Unit Time
second = unit "s" "second"

ampere : Unit Current
ampere = unit "A" "ampere"

kelvin : Unit Temperature
kelvin = unit "K" "kelvin"

mole : Unit Amount
mole = unit "mol" "mole"

candela : Unit LuminousIntensity
candela = unit "cd" "candela"

hertz : Unit Frequency
hertz = unit "Hz" "hertz"

newton : Unit Force
newton = unit "N" "newton"

pascal : Unit Pressure
pascal = unit "Pa" "pascal"

joule : Unit Energy
joule = unit "J" "joule"

watt : Unit Power
watt = unit "W" "watt"

coulomb : Unit Charge
coulomb = unit "C" "coulomb"

volt : Unit Voltage
volt = unit "V" "volt"

farad : Unit Capacitance
farad = unit "F" "farad"

ohm : Unit Resistance
ohm = unit "Ω" "ohm"

siemens : Unit Conductance
siemens = unit "S" "siemens"

weber : Unit MagneticFlux
weber = unit "Wb" "weber"

tesla : Unit MagneticFluxDensity
tesla = unit "T" "tesla"

henry : Unit Inductance
henry = unit "H" "henry"

lumen : Unit LuminousFlux
lumen = unit "lm" "lumen"

lux : Unit Illuminance
lux = unit "lx" "lux"

becquerel : Unit Activity
becquerel = unit "Bq" "becquerel"

gray : Unit AbsorbedDose
gray = unit "Gy" "gray"

sievert : Unit AbsorbedDose
sievert = unit "Sv" "sievert"

katal : Unit CatalyticActivity
katal = unit "kat" "katal"

joulePerMole : Unit MolarEnergy
joulePerMole = unit "J mol⁻¹" "joule per mole"

joulePerMoleKelvin : Unit MolarEntropy
joulePerMoleKelvin = unit "J mol⁻¹ K⁻¹" "joule per mole kelvin"

molePerCubicMetre : Unit MolarConcentration
molePerCubicMetre = unit "mol m⁻³" "mole per cubic metre"

------------------------------------------------------------------------
-- Typed measurement and authority metadata.

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
