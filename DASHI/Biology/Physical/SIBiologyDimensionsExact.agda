module DASHI.Biology.Physical.SIBiologyDimensionsExact where

open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (zero; suc)

import DASHI.Physics.Units.SI as SI

------------------------------------------------------------------------
-- Derived SI dimensions needed by the physical-developmental operator lane.
--
-- Exponent order follows DASHI.Physics.Units.SI:
--   length, mass, time, current, temperature, amount, luminous intensity.
--
-- These are definitions, not empirical parameter values.
------------------------------------------------------------------------

z : Int
z = pos zero

p1 : Int
p1 = pos (suc zero)

p2 : Int
p2 = pos (suc (suc zero))

p4 : Int
p4 = pos (suc (suc (suc (suc zero))))

n1 : Int
n1 = negsuc zero

n2 : Int
n2 = negsuc (suc zero)

n3 : Int
n3 = negsuc (suc (suc zero))

n4 : Int
n4 = negsuc (suc (suc (suc zero)))

-- mol m^-2 s^-1
MolarFlux : SI.Dimension
MolarFlux = SI.dim n2 z n1 z z p1 z

-- m^2 s^-1
Diffusivity : SI.Dimension
Diffusivity = SI.dim p2 z n1 z z z z

-- mol m^-3 s^-1
MolarReactionRate : SI.Dimension
MolarReactionRate = SI.dim n3 z n1 z z p1 z

-- mol s^-1
MolarFlowRate : SI.Dimension
MolarFlowRate = SI.dim z z n1 z z p1 z

-- N m^-1 = kg s^-2
SurfaceTension : SI.Dimension
SurfaceTension = SI.dim z p1 n2 z z z z

-- N m^-3 = kg m^-2 s^-2
ForceDensity : SI.Dimension
ForceDensity = SI.dim n2 p1 n2 z z z z

-- A m^-2
CurrentDensity : SI.Dimension
CurrentDensity = SI.dim n2 z z p1 z z z

-- F m^-2 = kg^-1 m^-4 s^4 A^2
CapacitancePerArea : SI.Dimension
CapacitancePerArea = SI.dim n4 n1 p4 p2 z z z

-- J K^-1 s^-1 = kg m^2 s^-3 K^-1
EntropyFlowRate : SI.Dimension
EntropyFlowRate = SI.dim p2 p1 n3 z n1 z z

molePerSquareMetreSecond : SI.Unit MolarFlux
molePerSquareMetreSecond = SI.mkUnit "mol m⁻² s⁻¹" "mole per square metre second"

squareMetrePerSecond : SI.Unit Diffusivity
squareMetrePerSecond = SI.mkUnit "m² s⁻¹" "square metre per second"

molePerCubicMetreSecond : SI.Unit MolarReactionRate
molePerCubicMetreSecond = SI.mkUnit "mol m⁻³ s⁻¹" "mole per cubic metre second"

molePerSecond : SI.Unit MolarFlowRate
molePerSecond = SI.mkUnit "mol s⁻¹" "mole per second"

newtonPerMetre : SI.Unit SurfaceTension
newtonPerMetre = SI.mkUnit "N m⁻¹" "newton per metre"

newtonPerCubicMetre : SI.Unit ForceDensity
newtonPerCubicMetre = SI.mkUnit "N m⁻³" "newton per cubic metre"

amperePerSquareMetre : SI.Unit CurrentDensity
amperePerSquareMetre = SI.mkUnit "A m⁻²" "ampere per square metre"

joulePerKelvinSecond : SI.Unit EntropyFlowRate
joulePerKelvinSecond = SI.mkUnit "J K⁻¹ s⁻¹" "joule per kelvin second"
