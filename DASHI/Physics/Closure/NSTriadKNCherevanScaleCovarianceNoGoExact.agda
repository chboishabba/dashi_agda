module DASHI.Physics.Closure.NSTriadKNCherevanScaleCovarianceNoGoExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Pylyp Cherevan.
-- Title: "Log-free estimate for the resonant paraproduct in the 3D
-- Navier--Stokes equations".
-- arXiv:2510.06246v1.
-- arXiv DOI: 10.48550/arXiv.2510.06246.
--
-- Related scaling background:
-- Authors: Herbert Koch; Daniel Tataru.
-- Title: "Well-posedness for the Navier--Stokes Equations".
-- Advances in Mathematics 157 (2001), 22--35.
-- DOI: 10.1006/aima.2000.1937.
--
-- PURPOSE
-- Audit the claimed scale consistency of
--
--   ||R_N(u)||_{H^-1} <= N^-1 ||u||_{H^1/2} ||u||_{H^1}.
--
-- Under u_mu(t,x)=mu u(mu^2 t,mu x), the nonlinear H^-1 norm and
-- ||u||_{H^1} both acquire mu^(1/2), while H^1/2 is invariant.  If the
-- output dyad also moves N -> mu N, the additional N^-1 contributes
-- mu^-1.  Hence the proposed right side scales as mu^-1/2, whereas the
-- left side scales as mu^1/2.
--
-- Fractional powers are avoided by taking mu=4, with square root 2.  The
-- exact witness is 1/2 < 2.  Removing the N^-1 factor restores equality of
-- the two scale multipliers, but of course does not prove the estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _*_; _<_)
open import Data.Rational.Properties as ℚₚ using (_<?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary.Decidable.Core using (toWitness)

spatialDilation squareRootDilation inverseSquareRootDilation : ℚ
spatialDilation = Int.+ 4 / 1
squareRootDilation = Int.+ 2 / 1
inverseSquareRootDilation = Int.+ 1 / 2

nonlinearHMinusOneScale : ℚ
nonlinearHMinusOneScale = squareRootDilation

criticalNormProductScale : ℚ
criticalNormProductScale = squareRootDilation

paperInverseDyadScale : ℚ
paperInverseDyadScale = Int.+ 1 / 4

paperRightSideScale : ℚ
paperRightSideScale =
  paperInverseDyadScale * criticalNormProductScale

paperRightSideScaleIsInverseRoot :
  paperRightSideScale ≡ inverseSquareRootDilation
paperRightSideScaleIsInverseRoot = solve []

claimedScaleMultiplierIsTooSmall :
  paperRightSideScale < nonlinearHMinusOneScale
claimedScaleMultiplierIsTooSmall =
  toWitness {a? = paperRightSideScale ℚₚ.<? nonlinearHMinusOneScale} _

frequencyFreeRightSideScale : ℚ
frequencyFreeRightSideScale = criticalNormProductScale

frequencyFreeScalingMatches :
  frequencyFreeRightSideScale ≡ nonlinearHMinusOneScale
frequencyFreeScalingMatches = solve []

paperScaleDefectFactor : ℚ
paperScaleDefectFactor =
  nonlinearHMinusOneScale * nonlinearHMinusOneScale

paperScaleDefectFactorIsFour :
  paperScaleDefectFactor ≡ spatialDilation
paperScaleDefectFactorIsFour = solve []
