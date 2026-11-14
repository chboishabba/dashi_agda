module DASHI.Physics.QuantumSensors.NVCrystalOrientationExact where

-- Finite crystallographic NV-axis labels, not a full tetrahedral
-- crystal group or a calibrated defect-orientation tomography.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Agda.Builtin.List using ([]; _∷_)

record Vector3 : Set where
  constructor xyz
  field x y z : ℚ
open Vector3 public

-- Four unoriented <111> axes, represented by selected signed normals.
data NVAxis : Set where
  a111 a1m1m1 am11m1 am1m11 : NVAxis

axisVector : NVAxis → Vector3
axisVector a111 = xyz 1 1 1
axisVector a1m1m1 = xyz 1 (- 1) (- 1)
axisVector am11m1 = xyz (- 1) 1 (- 1)
axisVector am1m11 = xyz (- 1) (- 1) 1

dot : Vector3 → Vector3 → ℚ
dot u v = x u * x v + y u * y v + z u * z v

-- Projection is unnormalised by sqrt(3); units are explicit in consumers.
projectAxis : NVAxis → Vector3 → ℚ
projectAxis a b = dot (axisVector a) b

uniformField : ℚ → Vector3
uniformField b = xyz b b b

-- The selected [111] axis sees three components in the same direction.
project111 :
  (b : ℚ) → projectAxis a111 (uniformField b) ≡ b + b + b
project111 b = solve (b ∷ [])

-- Defect-orientation sign is not an independent new physical dimension.
record CrystalSensorSite : Set where
  constructor crystal-site
  field
    orientation : NVAxis
    strainSplitting : ℚ
    crystalReference : ℚ
open CrystalSensorSite public
