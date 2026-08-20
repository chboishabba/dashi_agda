module DASHI.Physics.Closure.NSTriadKNHHGoodScaleInvariantAnnulusNoGoRound67Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- ROUND 67 / E1 CORRECTION
--
-- Round40 correctly proves that the *strain multiplier* is homogeneous of
-- degree zero.  Round48 then put the same radial-scale-invariance requirement
-- on `LiteralAnnularStrainCutoff`.  A genuine compact annular cutoff cannot
-- satisfy that requirement unless it vanishes along every positive scale
-- orbit on which it ever vanishes.
--
-- This module records that obstruction exactly.  If a cutoff is nonzero at a
-- lattice projection mode but zero at one positive radial rescaling of that
-- same mode, Round48 radialScaleInvariant immediately gives a contradiction.
-- Therefore E1 must keep two roles separate:
--
--   homogeneous order-zero physical strain symbol
--       TIMES
--   non-homogeneous smooth compact annular cutoff.
--
-- This is a producer-level correction: the old scale-invariant cutoff type is
-- still useful for homogeneous symbols, but it cannot be the C_c^4 annulus
-- whose derivatives and inverse-Fourier decay B/E require.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (0ℚ)
open import Relation.Binary.PropositionalEquality using (_≢_; sym; trans)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNFourierStrainScaleInvariantRound40Exact as Scale
import DASHI.Physics.Closure.NSTriadKNHHGoodLiteralAnnularStrainSymbolRound48Exact as Literal

record ScaleOrbitAnnulusWitness
    (cutoff : Literal.LiteralAnnularStrainCutoff) : Set₁ where
  field
    insideMode : V.ProjectionMode
    outsideScale : Threshold.PositiveThreshold
    insideNonzero : Literal.cutoffWeight cutoff insideMode ≢ 0ℚ
    scaledOutsideZero :
      Literal.cutoffWeight cutoff
        (Scale.scaledProjectionMode outsideScale insideMode)
      ≡ 0ℚ

open ScaleOrbitAnnulusWitness public

scaleInvariantCutoffCannotHaveScaleOrbitAnnulus :
  ∀ {cutoff} → ScaleOrbitAnnulusWitness cutoff → ⊥
scaleInvariantCutoffCannotHaveScaleOrbitAnnulus {cutoff} witness =
  insideNonzero witness
    (trans
      (sym
        (Literal.radialScaleInvariant cutoff
          (outsideScale witness) (insideMode witness)))
      (scaledOutsideZero witness))

scaleInvariantCutoffNonzeroPropagatesAlongEveryScale :
  ∀ cutoff scale modeData →
  Literal.cutoffWeight cutoff modeData ≢ 0ℚ →
  Literal.cutoffWeight cutoff (Scale.scaledProjectionMode scale modeData)
    ≢ 0ℚ
scaleInvariantCutoffNonzeroPropagatesAlongEveryScale
    cutoff scale modeData nonzero scaledZero =
  nonzero
    (trans
      (sym (Literal.radialScaleInvariant cutoff scale modeData))
      scaledZero)

round67HomogeneityAnnulusRolesSeparated : Bool
round67HomogeneityAnnulusRolesSeparated = true

round67ScaleInvariantCompactAnnulusRouteRuledOut : Bool
round67ScaleInvariantCompactAnnulusRouteRuledOut = true

round67HomogeneityAnnulusRolesSeparatedIsTrue :
  round67HomogeneityAnnulusRolesSeparated ≡ true
round67HomogeneityAnnulusRolesSeparatedIsTrue = refl

round67ScaleInvariantCompactAnnulusRouteRuledOutIsTrue :
  round67ScaleInvariantCompactAnnulusRouteRuledOut ≡ true
round67ScaleInvariantCompactAnnulusRouteRuledOutIsTrue = refl
