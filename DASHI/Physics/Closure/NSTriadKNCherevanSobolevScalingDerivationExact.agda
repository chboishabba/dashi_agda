module DASHI.Physics.Closure.NSTriadKNCherevanSobolevScalingDerivationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Source under audit:
-- Author: Pylyp Cherevan.
-- Title: "Log-free estimate for the resonant paraproduct in the 3D
-- Navier--Stokes equations".
-- arXiv:2510.06246v1.
-- arXiv DOI: 10.48550/arXiv.2510.06246.
--
-- Scaling background:
-- Authors: Herbert Koch; Daniel Tataru.
-- Title: "Well-posedness for the Navier--Stokes Equations".
-- DOI: 10.1006/aima.2000.1937.
--
-- PURPOSE
-- Expand the round-eleven scale obstruction into the literal Sobolev
-- homogeneity factors.  For
--
--   u_mu(x) = mu u(mu x)
--
-- in dimension three, ||u_mu||_{H^s} scales by mu^(s-1/2).  Thus H^(1/2)
-- is invariant and H^1 gains mu^(1/2).  The quadratic derivative
--
--   B(u,u) = P div(u tensor u)
--
-- has amplitude mu^3.  A pure spatial rescaling f(mu x) contributes
-- mu^(-5/2) in H^(-1), hence B(u_mu,u_mu) gains mu^(1/2), not a negative
-- power.  The proposed additional N^(-1) makes the right side scale by
-- mu^(-1/2).  At mu=4 the exact multipliers are 2 and 1/2.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _*_; _<_)
open import Data.Rational.Properties as ℚₚ using (_<?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary.Decidable.Core using (toWitness)

mu fourRoot inverseDyad : ℚ
mu = Int.+ 4 / 1
fourRoot = Int.+ 2 / 1
inverseDyad = Int.+ 1 / 4

velocityHOneHalfScale velocityHOneScale : ℚ
velocityHOneHalfScale = Int.+ 1 / 1
velocityHOneScale = fourRoot

-- B(u_mu,u_mu) has the literal amplitude multiplier mu^3 = 64.
nonlinearAmplitudeScale : ℚ
nonlinearAmplitudeScale = Int.+ 64 / 1

-- For a field f(mu x), the three-dimensional H^(-1) norm contributes
-- mu^(-5/2) = 1/32 at mu=4.
pureSpatialHMinusOneScale : ℚ
pureSpatialHMinusOneScale = Int.+ 1 / 32

nonlinearHMinusOneScale : ℚ
nonlinearHMinusOneScale =
  nonlinearAmplitudeScale * pureSpatialHMinusOneScale

nonlinearHMinusOneScaleIsRoot :
  nonlinearHMinusOneScale ≡ fourRoot
nonlinearHMinusOneScaleIsRoot = solve []

paperRightSideScale : ℚ
paperRightSideScale =
  inverseDyad * velocityHOneHalfScale * velocityHOneScale

paperRightSideScaleIsInverseRoot :
  paperRightSideScale ≡ Int.+ 1 / 2
paperRightSideScaleIsInverseRoot = solve []

paperRightSideScaleIsTooSmall :
  paperRightSideScale < nonlinearHMinusOneScale
paperRightSideScaleIsTooSmall =
  toWitness {a? = paperRightSideScale ℚₚ.<? nonlinearHMinusOneScale} _

scaleDefectFactor : ℚ
scaleDefectFactor =
  nonlinearHMinusOneScale * nonlinearHMinusOneScale

scaleDefectFactorIsMu :
  scaleDefectFactor ≡ mu
scaleDefectFactorIsMu = solve []

-- Removing N^(-1) restores scale covariance of the norm product, but does
-- not by itself prove any resonant estimate.
frequencyFreeRightSideScale : ℚ
frequencyFreeRightSideScale =
  velocityHOneHalfScale * velocityHOneScale

frequencyFreeScaleMatches :
  frequencyFreeRightSideScale ≡ nonlinearHMinusOneScale
frequencyFreeScaleMatches = solve []
