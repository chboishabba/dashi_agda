module DASHI.Physics.Closure.NSPeriodicRealBiotSavartModeNorm where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanRealPolynomialRing using
  (_+R_; _*R_; oneR; oneˡ)
open import DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver using
  (module RealPolynomialSolver)
open import DASHI.Physics.YangMills.BalabanComputedPolynomialSolver using
  (solveComputed; computed)
open RealPolynomialSolver using (Polynomial; _:=_; _:+_; _:*_)

import DASHI.Physics.Closure.NSPeriodicRealVectorPolynomialIdentities as Vector
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Modewise Biot-Savart Pythagorean identity in the real carrier.
--
-- With r = |k|^{-2}, Lagrange's identity gives
--
--   r |k×ω|² + r (k·ω)² = |ω|².
--
-- The first term is the homogeneous H1 contribution of
-- u = r(k×ω), while the second is the longitudinal vorticity complement.
------------------------------------------------------------------------

scaledLagrangeP :
  ∀ {n} →
  Polynomial n →
  Polynomial n → Polynomial n → Polynomial n →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n
scaledLagrangeP inverse k₁ k₂ k₃ w₁ w₂ w₃ =
  (inverse :* Vector.crossNormSquaredP k₁ k₂ k₃ w₁ w₂ w₃)
  :+
  (inverse :* Vector.squareP (Vector.dotP k₁ k₂ k₃ w₁ w₂ w₃))

scaledLagrangePolynomial :
  ∀ inverse k₁ k₂ k₃ w₁ w₂ w₃ →
  (inverse *R Vector.crossNormSquaredR k₁ k₂ k₃ w₁ w₂ w₃)
  +R
  (inverse *R
    (Vector.dotR k₁ k₂ k₃ w₁ w₂ w₃
     *R Vector.dotR k₁ k₂ k₃ w₁ w₂ w₃))
  ≡
  (inverse *R Vector.normKSquaredR k₁ k₂ k₃ w₁ w₂ w₃)
  *R Vector.normWSquaredR k₁ k₂ k₃ w₁ w₂ w₃
scaledLagrangePolynomial =
  solveComputed 7
    (λ inverse k₁ k₂ k₃ w₁ w₂ w₃ →
      scaledLagrangeP inverse k₁ k₂ k₃ w₁ w₂ w₃
      :=
      ((inverse :* Vector.normKSquaredP k₁ k₂ k₃ w₁ w₂ w₃)
       :* Vector.normWSquaredP k₁ k₂ k₃ w₁ w₂ w₃))
    computed

record RealModeInverseNormInputs : Set₁ where
  field
    k₁ k₂ k₃ w₁ w₂ w₃ inverseNormSquared : ℝ

    inverseNormLaw :
      inverseNormSquared
      *R Vector.normKSquaredR k₁ k₂ k₃ w₁ w₂ w₃
      ≡ oneR

open RealModeInverseNormInputs public

modeBiotSavartH1Squared modeVorticityLongitudinalSquared
  modeVorticityNormSquared : RealModeInverseNormInputs → ℝ
modeBiotSavartH1Squared M =
  inverseNormSquared M
  *R Vector.crossNormSquaredR
    (k₁ M) (k₂ M) (k₃ M) (w₁ M) (w₂ M) (w₃ M)
modeVorticityLongitudinalSquared M =
  inverseNormSquared M
  *R
  (Vector.dotR
    (k₁ M) (k₂ M) (k₃ M) (w₁ M) (w₂ M) (w₃ M)
   *R
   Vector.dotR
    (k₁ M) (k₂ M) (k₃ M) (w₁ M) (w₂ M) (w₃ M))
modeVorticityNormSquared M =
  Vector.normWSquaredR
    (k₁ M) (k₂ M) (k₃ M) (w₁ M) (w₂ M) (w₃ M)

modeBiotSavartPythagoreanIdentity :
  ∀ M →
  modeVorticityNormSquared M
  ≡
  modeBiotSavartH1Squared M
  +R modeVorticityLongitudinalSquared M
modeBiotSavartPythagoreanIdentity M =
  sym
    (trans
      (scaledLagrangePolynomial
        (inverseNormSquared M)
        (k₁ M) (k₂ M) (k₃ M)
        (w₁ M) (w₂ M) (w₃ M))
      (trans
        (cong
          (λ coefficient → coefficient *R modeVorticityNormSquared M)
          (inverseNormLaw M))
        (oneˡ (modeVorticityNormSquared M))))

------------------------------------------------------------------------
-- Status: the modewise real Biot-Savart norm split is checked from the exact
-- inverse-norm law and computed Lagrange identity.  Summing this identity over
-- Galerkin modes is handled by NSPeriodicFinitePythagoreanSum.
------------------------------------------------------------------------

realBiotSavartModeNormLevel : ProofLevel
realBiotSavartModeNormLevel = machineChecked
