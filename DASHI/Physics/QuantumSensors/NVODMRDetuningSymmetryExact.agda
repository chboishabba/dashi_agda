module DASHI.Physics.QuantumSensors.NVODMRDetuningSymmetryExact where

-- Exact weak-drive, finite rational detuning algebra for phenomenological
-- NV ODMR. The Lorentzian denominator/physical positivity are separately
-- witnessed; no linewidth or fluorescence values are source-calibrated.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Tactic.RingSolver using (solve)

-- Denominator Δ²+Γ² without importing a physically assumed inverse.
lineShapeDenominator : ℚ → ℚ → ℚ
lineShapeDenominator detuning width =
  detuning * detuning + width * width

symmetricDenominator :
  (detuning width : ℚ) →
  lineShapeDenominator detuning width ≡
  lineShapeDenominator (0ℚ - detuning) width
symmetricDenominator detuning width =
  solve (detuning ∷ width ∷ [])


-- The driven resonance detuning is f_drive - (D + gamma B).
-- A field difference b changes detuning by minus gamma*b.
detuning : ℚ → ℚ → ℚ → ℚ → ℚ
detuning drive D gamma B = drive - (D + gamma * B)

detuningFieldShift :
  (drive D gamma B shift : ℚ) →
  detuning drive D gamma (B + shift) ≡
  detuning drive D gamma B - gamma * shift
detuningFieldShift drive D gamma B shift =
  solve (drive ∷ D ∷ gamma ∷ B ∷ shift ∷ [])
