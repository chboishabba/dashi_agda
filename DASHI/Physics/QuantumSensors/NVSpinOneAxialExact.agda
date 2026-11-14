module DASHI.Physics.QuantumSensors.NVSpinOneAxialExact where

-- A finite, exactly rational axial NV ground-state model.
-- This models labelled energy branches; it does not prove a calibrated ODMR
-- spectrum, strain/hyperfine corrections, or experimental resolution.
-- Physical background: NV-centre spin-one zero-field splitting and Zeeman coupling.
-- New formal derivations here are attributed to the DASHI formalisation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Algebra.Quantum.FiniteQutrit as Q

record AxialNV : Set where
  constructor axial-nv
  field
    zeroFieldSplitting : ℚ
    gyromagneticRatio : ℚ
    axialMagneticField : ℚ
open AxialNV public

-- The order ket0, ket1, ket2 represents m_s = +1,0,-1.
energy : AxialNV → Q.QutritBasis → ℚ
energy p Q.ket0 = zeroFieldSplitting p + gyromagneticRatio p * axialMagneticField p
energy p Q.ket1 = 0ℚ
energy p Q.ket2 = zeroFieldSplitting p - gyromagneticRatio p * axialMagneticField p

-- Finite real-valued matrix; symmetric is a necessary algebraic part of
-- Hermiticity after a real-to-complex embedding, not a completed operator theorem.
matrixEntry : AxialNV → Q.QutritBasis → Q.QutritBasis → ℚ
matrixEntry p Q.ket0 Q.ket0 = energy p Q.ket0
matrixEntry p Q.ket1 Q.ket1 = energy p Q.ket1
matrixEntry p Q.ket2 Q.ket2 = energy p Q.ket2
matrixEntry p _ _ = 0ℚ

matrixSymmetric :
  (p : AxialNV) (i j : Q.QutritBasis) →
  matrixEntry p i j ≡ matrixEntry p j i
matrixSymmetric p Q.ket0 Q.ket0 = refl
matrixSymmetric p Q.ket0 Q.ket1 = refl
matrixSymmetric p Q.ket0 Q.ket2 = refl
matrixSymmetric p Q.ket1 Q.ket0 = refl
matrixSymmetric p Q.ket1 Q.ket1 = refl
matrixSymmetric p Q.ket1 Q.ket2 = refl
matrixSymmetric p Q.ket2 Q.ket0 = refl
matrixSymmetric p Q.ket2 Q.ket1 = refl
matrixSymmetric p Q.ket2 Q.ket2 = refl

-- Signed branch separation, without assuming a positive branch ordering.
signedSplitting : AxialNV → ℚ
signedSplitting p = energy p Q.ket0 - energy p Q.ket2

axialSplittingIdentity :
  (p : AxialNV) →
  signedSplitting p ≡
  gyromagneticRatio p * axialMagneticField p +
  gyromagneticRatio p * axialMagneticField p
axialSplittingIdentity (axial-nv d gamma b) =
  solve (d ∷ gamma ∷ b ∷ [])
