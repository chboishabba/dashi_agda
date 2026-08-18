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
--   (u^T H v)^2 <= |u|^2 ||H||_F^2 |v|^2.
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
--   (u^T H(k) v)^2 <= |u|^2 |h(k)|^2 |v|^2.
--
-- This is the correct norm-level bridge if C4 uses full pressure-source mass.
-- It does not yet perform the convolution/shell summation needed for the
-- selected packet.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Product.Base using (_,_)
open import Data.Rational.Base using (ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact as M
import DASHI.Physics.Closure.NSTriadKNCorrectedFourierAngularStrainExact as A
import DASHI.Physics.Closure.NSTriadKNFourierStrainFrobeniusBoundRound68Exact as Frob
import DASHI.Physics.Closure.NSTriadKNPressureHessianFourierIsometryRound81Exact as P81

------------------------------------------------------------------------
-- Nine-coordinate Cauchy representation of u^T H v.
------------------------------------------------------------------------

matrixVelocityPairs : M.Matrix3 → V.Vector3 → V.Vector3 → L2.Pair ∷? 
