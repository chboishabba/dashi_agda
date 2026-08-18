module DASHI.Physics.Closure.NSTriadKNPressureHessianVelocityBilinearFrobeniusBoundRound85Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Roger A. Horn; Charles R. Johnson.
-- Title: "Matrix Analysis", Second Edition.
-- DOI: 10.1017/CBO9781139020411.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND85 / SUFFICIENT NORM-LEVEL REPAIR FOR THE C4 HESSIAN OBSERVER
--
-- The companion no-go proves that
--
--   trace/Q + omega^T H omega + one off-diagonal injection
--
-- cannot determine the selected velocity--Hessian bilinear.  The natural
-- sufficient replacement is the full Frobenius mass.  This file proves on the
-- repository's exact rational finite-L2 carrier
--
--   (u^T H v)^2 <= ||H||_F^2 |u|^2 |v|^2.
--
-- There is NO dimension factor: use Cauchy--Schwarz on the nine coordinates
-- H_ij and u_i v_j, then
--
--   sum_ij (u_i v_j)^2 = |u|^2 |v|^2
--
-- exactly.
--
-- The second half instantiates H with Round81's pressure-Hessian multiplier
--
--   H_ij(k) = k_i k_j |k|^{-2} h(k),
--
-- whose Frobenius square is already exactly |h(k)|^2.  Hence
--
--   (u^T H(k) v)^2 <= |h(k)|^2 |u|^2 |v|^2.
--
-- This is the correct norm-level bridge if C4 uses full pressure-source mass.
-- It does not yet perform the convolution/shell summation needed for the
-- selected packet.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product.Base using (_,_)
open import Data.Rational.Base using (ℚ; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; trans)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact as M
import DASHI.Physics.Closure.NSTriadKNCorrectedFourierAngularStrainExact as A
import DASHI.Physics.Closure.NSTriadKNFourierStrainFrobeniusBoundRound68Exact as Frob
import DASHI.Physics.Closure.NSTriadKNPressureHessianFourierIsometryRound81Exact as P81

------------------------------------------------------------------------
-- Nine-coordinate Cauchy representation of u^T H v.
------------------------------------------------------------------------

matrixVelocityPairs : M.Matrix3 → V.Vector3 → V.Vector3 → List L2.Pair
matrixVelocityPairs H u v =
    (M.m11 H , V.x u * V.x v)
  ∷ (M.m12 H , V.x u * V.y v)
  ∷ (M.m13 H , V.x u * V.z v)
  ∷ (M.m21 H , V.y u * V.x v)
  ∷ (M.m22 H , V.y u * V.y v)
  ∷ (M.m23 H , V.y u * V.z v)
  ∷ (M.m31 H , V.z u * V.x v)
  ∷ (M.m32 H , V.z u * V.y v)
  ∷ (M.m33 H , V.z u * V.z v)
  ∷ []

velocityHessianWork : M.Matrix3 → V.Vector3 → V.Vector3 → ℚ
velocityHessianWork H u v = V.dot u (A.apply H v)

matrixVelocityPairDotExact : ∀ H u v →
  L2.pairDot (matrixVelocityPairs H u v)
  ≡ velocityHessianWork H u v
matrixVelocityPairDotExact
    (M.matrix3 h11 h12 h13 h21 h22 h23 h31 h32 h33)
    (V.v3 ux uy uz) (V.v3 vx vy vz) =
  solve
    (h11 ∷ h12 ∷ h13 ∷ h21 ∷ h22 ∷ h23 ∷ h31 ∷ h32 ∷ h33
      ∷ ux ∷ uy ∷ uz ∷ vx ∷ vy ∷ vz ∷ [])

matrixVelocityLeftNormExact : ∀ H u v →
  L2.leftNormSquared (matrixVelocityPairs H u v)
  ≡ Frob.frobeniusSquared H
matrixVelocityLeftNormExact
    (M.matrix3 h11 h12 h13 h21 h22 h23 h31 h32 h33)
    (V.v3 ux uy uz) (V.v3 vx vy vz) =
  solve
    (h11 ∷ h12 ∷ h13 ∷ h21 ∷ h22 ∷ h23 ∷ h31 ∷ h32 ∷ h33 ∷ [])

matrixVelocityRightNormFactors : ∀ H u v →
  L2.rightNormSquared (matrixVelocityPairs H u v)
  ≡ V.normSquared u * V.normSquared v
matrixVelocityRightNormFactors H
    (V.v3 ux uy uz) (V.v3 vx vy vz) =
  solve (ux ∷ uy ∷ uz ∷ vx ∷ vy ∷ vz ∷ [])

velocityHessianWorkSquaredBound : ∀ H u v →
  L2.square (velocityHessianWork H u v)
  ≤ Frob.frobeniusSquared H *
      (V.normSquared u * V.normSquared v)
velocityHessianWorkSquaredBound H u v =
  let
    pairs = matrixVelocityPairs H u v
    finite = L2.finiteCauchySchwarzSquared pairs

    rightExact :
      L2.leftNormSquared pairs * L2.rightNormSquared pairs
      ≡ Frob.frobeniusSquared H *
          (V.normSquared u * V.normSquared v)
    rightExact = cong₂ _*_
      (matrixVelocityLeftNormExact H u v)
      (matrixVelocityRightNormFactors H u v)

    withRight :
      L2.square (L2.pairDot pairs)
      ≤ Frob.frobeniusSquared H *
          (V.normSquared u * V.normSquared v)
    withRight = subst
      (λ upper → L2.square (L2.pairDot pairs) ≤ upper)
      rightExact finite
  in
  subst
    (λ lower →
      lower ≤ Frob.frobeniusSquared H *
        (V.normSquared u * V.normSquared v))
    (cong L2.square (matrixVelocityPairDotExact H u v))
    withRight

------------------------------------------------------------------------
-- Round81 pressure multiplier as an actual Matrix3.
------------------------------------------------------------------------

pressureHessianMatrix : P81.NonzeroModePoissonMultiplier → M.Matrix3
pressureHessianMatrix datum =
  M.matrix3
    (P81.hessianCoefficient datum (P81.kx datum) (P81.kx datum))
    (P81.hessianCoefficient datum (P81.kx datum) (P81.ky datum))
    (P81.hessianCoefficient datum (P81.kx datum) (P81.kz datum))
    (P81.hessianCoefficient datum (P81.ky datum) (P81.kx datum))
    (P81.hessianCoefficient datum (P81.ky datum) (P81.ky datum))
    (P81.hessianCoefficient datum (P81.ky datum) (P81.kz datum))
    (P81.hessianCoefficient datum (P81.kz datum) (P81.kx datum))
    (P81.hessianCoefficient datum (P81.kz datum) (P81.ky datum))
    (P81.hessianCoefficient datum (P81.kz datum) (P81.kz datum))

pressureHessianMatrixFrobeniusMeaning : ∀ datum →
  Frob.frobeniusSquared (pressureHessianMatrix datum)
  ≡ P81.hessianFrobeniusSquareEnergy datum
pressureHessianMatrixFrobeniusMeaning datum = refl

pressureHessianMatrixFrobeniusIsSourceSquare : ∀ datum →
  Frob.frobeniusSquared (pressureHessianMatrix datum)
  ≡ P81.square (P81.sourceCoefficient datum)
pressureHessianMatrixFrobeniusIsSourceSquare datum =
  trans
    (pressureHessianMatrixFrobeniusMeaning datum)
    (P81.pressureHessianModeFrobeniusIsometry datum)

pressureVelocityHessianWorkSourceBound : ∀ datum u v →
  L2.square (velocityHessianWork (pressureHessianMatrix datum) u v)
  ≤ P81.square (P81.sourceCoefficient datum) *
      (V.normSquared u * V.normSquared v)
pressureVelocityHessianWorkSourceBound datum u v =
  subst
    (λ coefficient →
      L2.square (velocityHessianWork (pressureHessianMatrix datum) u v)
      ≤ coefficient * (V.normSquared u * V.normSquared v))
    (pressureHessianMatrixFrobeniusIsSourceSquare datum)
    (velocityHessianWorkSquaredBound (pressureHessianMatrix datum) u v)

round85VelocityHessianBilinearFrobeniusBoundConstructed : Bool
round85VelocityHessianBilinearFrobeniusBoundConstructed = true

round85PressureHessianBilinearControlledByPoissonSourceMass : Bool
round85PressureHessianBilinearControlledByPoissonSourceMass = true

round85SelectedPacketHessianConvolutionBoundConstructed : Bool
round85SelectedPacketHessianConvolutionBoundConstructed = false

round85PressureHessianBilinearControlledByPoissonSourceMassIsTrue :
  round85PressureHessianBilinearControlledByPoissonSourceMass ≡ true
round85PressureHessianBilinearControlledByPoissonSourceMassIsTrue = refl
