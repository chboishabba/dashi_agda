module DASHI.Physics.Units.MechanicalDimensionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Edgar Buckingham.
-- Title: "On Physically Similar Systems; Illustrations of the Use of
-- Dimensional Equations".
-- Physical Review 4 (1914), 345--376.
-- DOI: 10.1103/PhysRev.4.345.
--
-- PURPOSE
-- A small reusable M-L-T dimension algebra for the repository's physical
-- theories.  This is deliberately below the existing nominal finite quantity
-- wrappers: Energy and Work may remain semantically distinct even though they
-- carry the same mechanical dimension.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Integer using (ℤ; +_; -[1+_]; _+_)

record MechanicalDimension : Set where
  constructor dimension
  field
    massExponent : ℤ
    lengthExponent : ℤ
    timeExponent : ℤ

open MechanicalDimension public

infixl 7 _⊗ᴰ_

_⊗ᴰ_ : MechanicalDimension → MechanicalDimension → MechanicalDimension
dimension m₁ l₁ t₁ ⊗ᴰ dimension m₂ l₂ t₂ =
  dimension (m₁ + m₂) (l₁ + l₂) (t₁ + t₂)

dimensionless : MechanicalDimension
dimensionless = dimension (+ zero) (+ zero) (+ zero)

massDimension : MechanicalDimension
massDimension = dimension (+ (suc zero)) (+ zero) (+ zero)

lengthDimension : MechanicalDimension
lengthDimension = dimension (+ zero) (+ (suc zero)) (+ zero)

timeDimension : MechanicalDimension
timeDimension = dimension (+ zero) (+ zero) (+ (suc zero))

inverseLengthDimension : MechanicalDimension
inverseLengthDimension = dimension (+ zero) -[1+ zero ] (+ zero)

inverseAreaDimension : MechanicalDimension
inverseAreaDimension = dimension (+ zero) -[1+ suc zero ] (+ zero)

frequencyDimension : MechanicalDimension
frequencyDimension = dimension (+ zero) (+ zero) -[1+ zero ]

areaDimension : MechanicalDimension
areaDimension = dimension (+ zero) (+ (suc (suc zero))) (+ zero)

velocityDimension : MechanicalDimension
velocityDimension = dimension (+ zero) (+ (suc zero)) -[1+ zero ]

speedSquaredDimension : MechanicalDimension
speedSquaredDimension =
  dimension (+ zero) (+ (suc (suc zero))) -[1+ suc zero ]

accelerationDimension : MechanicalDimension
accelerationDimension =
  dimension (+ zero) (+ (suc zero)) -[1+ suc zero ]

kinematicViscosityDimension : MechanicalDimension
kinematicViscosityDimension =
  dimension (+ zero) (+ (suc (suc zero))) -[1+ zero ]

massDensityDimension : MechanicalDimension
massDensityDimension =
  dimension (+ (suc zero)) -[1+ suc (suc zero) ] (+ zero)

energyDimension : MechanicalDimension
energyDimension =
  dimension (+ (suc zero)) (+ (suc (suc zero))) -[1+ suc zero ]

workDimension : MechanicalDimension
workDimension = energyDimension

powerDimension : MechanicalDimension
powerDimension =
  dimension (+ (suc zero)) (+ (suc (suc zero))) -[1+ suc (suc zero) ]

pressureDimension : MechanicalDimension
pressureDimension =
  dimension (+ (suc zero)) -[1+ zero ] -[1+ suc zero ]

newtonianPotentialDimension : MechanicalDimension
newtonianPotentialDimension = speedSquaredDimension

velocityGradientDimension : MechanicalDimension
velocityGradientDimension = frequencyDimension

laplacianVelocityDimension : MechanicalDimension
laplacianVelocityDimension =
  dimension (+ zero) -[1+ zero ] -[1+ zero ]

specificDissipationRateDimension : MechanicalDimension
specificDissipationRateDimension =
  dimension (+ zero) (+ (suc (suc zero))) -[1+ suc (suc zero) ]

actionDimension : MechanicalDimension
actionDimension =
  dimension (+ (suc zero)) (+ (suc (suc zero))) -[1+ zero ]

------------------------------------------------------------------------
-- Exact cancellation and derived-dimension laws.
------------------------------------------------------------------------

inverseLengthTimesLength :
  inverseLengthDimension ⊗ᴰ lengthDimension ≡ dimensionless
inverseLengthTimesLength = refl

velocityTimesTime :
  velocityDimension ⊗ᴰ timeDimension ≡ lengthDimension
velocityTimesTime = refl

velocityGradientTimesTime :
  velocityGradientDimension ⊗ᴰ timeDimension ≡ dimensionless
velocityGradientTimesTime = refl

powerTimesTime :
  powerDimension ⊗ᴰ timeDimension ≡ energyDimension
powerTimesTime = refl

potentialMatchesSpeedSquared :
  newtonianPotentialDimension ≡ speedSquaredDimension
potentialMatchesSpeedSquared = refl

viscosityMatchesLengthVelocity :
  lengthDimension ⊗ᴰ velocityDimension ≡ kinematicViscosityDimension
viscosityMatchesLengthVelocity = refl

velocityTimeDerivativeIsAcceleration :
  velocityDimension ⊗ᴰ frequencyDimension ≡ accelerationDimension
velocityTimeDerivativeIsAcceleration = refl

advectionIsAcceleration :
  velocityDimension ⊗ᴰ velocityGradientDimension ≡ accelerationDimension
advectionIsAcceleration = refl

viscousLaplacianIsAcceleration :
  kinematicViscosityDimension ⊗ᴰ laplacianVelocityDimension
  ≡ accelerationDimension
viscousLaplacianIsAcceleration = refl

pressureGradientMatchesDensityAcceleration :
  pressureDimension ⊗ᴰ inverseLengthDimension
  ≡ massDensityDimension ⊗ᴰ accelerationDimension
pressureGradientMatchesDensityAcceleration = refl

specificDissipationIntegratedInTimeIsSpecificEnergy :
  specificDissipationRateDimension ⊗ᴰ timeDimension
  ≡ speedSquaredDimension
specificDissipationIntegratedInTimeIsSpecificEnergy = refl

------------------------------------------------------------------------
-- Dimension-indexed quantities.  The scalar carrier is intentionally
-- independent of the dimension algebra, allowing finite, rational, Bishop-real
-- and completed-real instances to share the same dimensional semantics.
------------------------------------------------------------------------

record Quantity (Scalar : Set) (dimensionOf : MechanicalDimension) : Set where
  constructor quantity
  field
    magnitude : Scalar

open Quantity public

mapMagnitude :
  ∀ {Scalar Target dimensionOf} →
  (Scalar → Target) → Quantity Scalar dimensionOf → Quantity Target dimensionOf
mapMagnitude f (quantity value) = quantity (f value)

multiplyQuantity :
  ∀ {Scalar leftDimension rightDimension} →
  (Scalar → Scalar → Scalar) →
  Quantity Scalar leftDimension →
  Quantity Scalar rightDimension →
  Quantity Scalar (leftDimension ⊗ᴰ rightDimension)
multiplyQuantity multiply (quantity left) (quantity right) =
  quantity (multiply left right)

sameDimensionRatio :
  ∀ {Scalar dimensionOf} →
  (Scalar → Scalar → Scalar) →
  Quantity Scalar dimensionOf →
  Quantity Scalar dimensionOf →
  Quantity Scalar dimensionless
sameDimensionRatio divide (quantity numerator) (quantity denominator) =
  quantity (divide numerator denominator)
