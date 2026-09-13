module DASHI.Physics.Textile.TextileMechanicalDimensionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Integer using (+_; -[1+_])

import DASHI.Physics.Units.MechanicalDimensionExact as Dim

tensionDimension : Dim.MechanicalDimension
tensionDimension =
  Dim.dimension (+ (suc zero)) (+ (suc zero)) -[1+ suc zero ]

stressDimension : Dim.MechanicalDimension
stressDimension = Dim.pressureDimension

strainDimension : Dim.MechanicalDimension
strainDimension = Dim.dimensionless

youngModulusDimension : Dim.MechanicalDimension
youngModulusDimension = stressDimension

axialRigidityDimension : Dim.MechanicalDimension
axialRigidityDimension = tensionDimension

curvatureDimension : Dim.MechanicalDimension
curvatureDimension = Dim.inverseLengthDimension

linearDensityDimension : Dim.MechanicalDimension
linearDensityDimension =
  Dim.dimension (+ (suc zero)) -[1+ zero ] (+ zero)

arealDensityDimension : Dim.MechanicalDimension
arealDensityDimension =
  Dim.dimension (+ (suc zero)) -[1+ suc zero ] (+ zero)

bendingRigidityDimension : Dim.MechanicalDimension
bendingRigidityDimension =
  Dim.dimension
    (+ (suc zero))
    (+ (suc (suc (suc zero))))
    -[1+ suc zero ]

torsionalRigidityDimension : Dim.MechanicalDimension
torsionalRigidityDimension = bendingRigidityDimension

tensileStressMatchesPressure :
  stressDimension ≡ Dim.pressureDimension
tensileStressMatchesPressure = refl

youngModulusMatchesStress :
  youngModulusDimension ≡ stressDimension
youngModulusMatchesStress = refl

strainIsDimensionless :
  strainDimension ≡ Dim.dimensionless
strainIsDimensionless = refl

tensionTimesInverseAreaIsStress :
  tensionDimension Dim.⊗ᴰ Dim.inverseAreaDimension
  ≡ stressDimension
tensionTimesInverseAreaIsStress = refl

youngModulusTimesAreaIsAxialRigidity :
  youngModulusDimension Dim.⊗ᴰ Dim.areaDimension
  ≡ axialRigidityDimension
youngModulusTimesAreaIsAxialRigidity = refl

youngModulusTimesAreaSquaredIsBendingRigidity :
  youngModulusDimension Dim.⊗ᴰ
    (Dim.areaDimension Dim.⊗ᴰ Dim.areaDimension)
  ≡ bendingRigidityDimension
youngModulusTimesAreaSquaredIsBendingRigidity = refl

linearDensityTimesLengthIsMass :
  linearDensityDimension Dim.⊗ᴰ Dim.lengthDimension
  ≡ Dim.massDimension
linearDensityTimesLengthIsMass = refl

arealDensityTimesAreaIsMass :
  arealDensityDimension Dim.⊗ᴰ Dim.areaDimension
  ≡ Dim.massDimension
arealDensityTimesAreaIsMass = refl
