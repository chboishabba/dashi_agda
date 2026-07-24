module DASHI.Physics.Closure.NSPeriodicRealVectorPolynomialIdentities where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanRealPolynomialRing using
  (_+R_; _*R_; -R_; zeroR)
open import DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver using
  (module RealPolynomialSolver; zeroCoefficient)
open import DASHI.Physics.YangMills.BalabanComputedPolynomialSolver using
  (solveComputed; computed)
open RealPolynomialSolver using
  (Polynomial; con; _:=_; _:+_; _:*_; :-_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact polynomial identities behind Fourier Biot-Savart and Leray geometry.
--
-- These are proved in the repository's axiomatic real carrier by the computed
-- polynomial solver, not assumed as vector-analysis axioms.
------------------------------------------------------------------------

zeroP : ∀ {n : Nat} → Polynomial n
zeroP = con zeroCoefficient

infixl 6 _-P_
_-P_ : ∀ {n : Nat} → Polynomial n → Polynomial n → Polynomial n
a -P b = a :+ (:- b)

squareP : ∀ {n : Nat} → Polynomial n → Polynomial n
squareP a = a :* a

crossXP crossYP crossZP :
  ∀ {n : Nat} →
  Polynomial n → Polynomial n → Polynomial n →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n
crossXP kx ky kz wx wy wz = (ky :* wz) -P (kz :* wy)
crossYP kx ky kz wx wy wz = (kz :* wx) -P (kx :* wz)
crossZP kx ky kz wx wy wz = (kx :* wy) -P (ky :* wx)

dotP normKSquaredP normWSquaredP crossNormSquaredP :
  ∀ {n : Nat} →
  Polynomial n → Polynomial n → Polynomial n →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n
dotP kx ky kz wx wy wz =
  (kx :* wx) :+ ((ky :* wy) :+ (kz :* wz))
normKSquaredP kx ky kz wx wy wz =
  squareP kx :+ (squareP ky :+ squareP kz)
normWSquaredP kx ky kz wx wy wz =
  squareP wx :+ (squareP wy :+ squareP wz)
crossNormSquaredP kx ky kz wx wy wz =
  squareP (crossXP kx ky kz wx wy wz)
  :+ (squareP (crossYP kx ky kz wx wy wz)
  :+ squareP (crossZP kx ky kz wx wy wz))

subR : ℝ → ℝ → ℝ
subR a b = a +R (-R b)

crossXR crossYR crossZR : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
crossXR kx ky kz wx wy wz = subR (ky *R wz) (kz *R wy)
crossYR kx ky kz wx wy wz = subR (kz *R wx) (kx *R wz)
crossZR kx ky kz wx wy wz = subR (kx *R wy) (ky *R wx)

dotR normKSquaredR normWSquaredR crossNormSquaredR :
  ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
dotR kx ky kz wx wy wz =
  (kx *R wx) +R ((ky *R wy) +R (kz *R wz))
normKSquaredR kx ky kz wx wy wz =
  (kx *R kx) +R ((ky *R ky) +R (kz *R kz))
normWSquaredR kx ky kz wx wy wz =
  (wx *R wx) +R ((wy *R wy) +R (wz *R wz))
crossNormSquaredR kx ky kz wx wy wz =
  (crossXR kx ky kz wx wy wz *R crossXR kx ky kz wx wy wz)
  +R ((crossYR kx ky kz wx wy wz *R crossYR kx ky kz wx wy wz)
  +R (crossZR kx ky kz wx wy wz *R crossZR kx ky kz wx wy wz))

waveDotOwnCrossR : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
waveDotOwnCrossR kx ky kz wx wy wz =
  (kx *R crossXR kx ky kz wx wy wz)
  +R ((ky *R crossYR kx ky kz wx wy wz)
  +R (kz *R crossZR kx ky kz wx wy wz))

waveDotOwnCrossPolynomial : ∀ kx ky kz wx wy wz →
  waveDotOwnCrossR kx ky kz wx wy wz ≡ zeroR
waveDotOwnCrossPolynomial =
  solveComputed 6
    (λ kx ky kz wx wy wz →
      ((kx :* crossXP kx ky kz wx wy wz)
       :+ ((ky :* crossYP kx ky kz wx wy wz)
       :+ (kz :* crossZP kx ky kz wx wy wz)))
      := zeroP)
    computed

lagrangeCrossProductPolynomial : ∀ kx ky kz wx wy wz →
  crossNormSquaredR kx ky kz wx wy wz
    +R (dotR kx ky kz wx wy wz *R dotR kx ky kz wx wy wz)
  ≡
  normKSquaredR kx ky kz wx wy wz
    *R normWSquaredR kx ky kz wx wy wz
lagrangeCrossProductPolynomial =
  solveComputed 6
    (λ kx ky kz wx wy wz →
      (crossNormSquaredP kx ky kz wx wy wz
       :+ squareP (dotP kx ky kz wx wy wz))
      :=
      (normKSquaredP kx ky kz wx wy wz
       :* normWSquaredP kx ky kz wx wy wz))
    computed

------------------------------------------------------------------------
-- Status: the two Euclidean polynomial identities are checked over the same
-- axiomatic real carrier used by the analytic formalization.  Remaining norm
-- work is their modewise scaling, nonnegativity, and finite-sum transport.
------------------------------------------------------------------------

realVectorPolynomialIdentityLevel : ProofLevel
realVectorPolynomialIdentityLevel = machineChecked
