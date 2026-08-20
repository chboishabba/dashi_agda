module DASHI.Physics.Closure.NSTriadKNHighestAlphaRound67Exact where

------------------------------------------------------------------------
-- ROUND 67 HIGHEST-ALPHA DELTA
--
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Peter Constantin; Charles Fefferman; Andrew J. Majda.
-- Title: "Geometric Constraints on Potentially Singular Solutions for the
-- 3-D Euler Equations".
-- DOI: 10.1080/03605309608821197.
--
-- ROUND 67 ADVANCES
--
-- E1 TYPE CORRECTION:
-- Round48 placed radial scale invariance on the object named an annular cutoff.
-- Round67 proves this cannot represent a nonzero compact annulus: nonzero
-- cutoff weight propagates along every positive scale orbit.  Homogeneity now
-- belongs to the order-zero strain multiplier; localization must be a separate
-- non-homogeneous smooth cutoff.
--
-- B/E HARD-CUTOFF FALSIFIER:
-- The exact integer prefix characteristic jumps from 1 to 0 under one lattice
-- step at every boundary, hence also at every dyadic radius 2^j.  The hard
-- projector remains valid bookkeeping, but cannot supply the Taylor smallness.
--
-- E1 CONCRETE SMOOTH CORE:
-- Construct the explicit degree-9 fourth-order smoothstep
--
--   S(t)=126t^5-420t^6+540t^7-315t^8+70t^9,
--
-- with S(0)=0, S(1)=1 and first through fourth derivatives zero at both
-- endpoints.  These are exact rational polynomial identities and provide the
-- gluing jets required for a C^4 annular transition.
--
-- CROSS-POLLINATION + TAYLOR FACTOR:
-- The same S is instantiated in the existing finite-dimensional Frechet
-- carrier from the Yang-Mills/Balaban lane.  Its derivative is literally
-- S'(x)h and its remainder is literally S(x+h)-S(x)-S'(x)h.  The remainder is
-- then factored exactly as
--
--   R(x,h) = h^2 Q(x,h)
--
-- for an explicit rational polynomial Q.  Thus the smooth cutoff now has a
-- genuine second-order Taylor small parameter, rather than an assumed one.
--
-- B3 LOW-OUTPUT PARITY:
-- The physical Fourier strain multiplier is proved even under k -> -k.  This
-- removes the sign seam in Round66's low-output branch, where the two dominant
-- Taylor endpoints are naturally p and -q and their separation is the low
-- output k.
--
-- REMAINING RISK-BEARING B/E PRODUCER:
-- Attach the explicit smooth radial transition to the actual continuum
-- projection-mode/matrix symbol, prove quantitative derivative bounds on the
-- Round66 branch geometry (including the angular strain contribution), and
-- feed those bounds into the normalized physical Gram overlap.  The hard
-- annulus is no longer an admissible Taylor object.  Fourfold continuum
-- integration by parts for this same matrix symbol remains the E2 analytic
-- endpoint; Round62 already closes the resulting dyadic L1 summation.
--
-- No Clay promotion is made here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound66Exact
import DASHI.Physics.Closure.NSTriadKNHHGoodScaleInvariantAnnulusNoGoRound67Exact
import DASHI.Physics.Closure.NSTriadKNComHardDyadicBoundaryTaylorNoGoRound67Exact
import DASHI.Physics.Closure.NSTriadKNHHGoodC4AnnularPolynomialCoreRound67Exact
import DASHI.Physics.Closure.NSTriadKNHHGoodC4AnnularFrechetBridgeRound67Exact
import DASHI.Physics.Closure.NSTriadKNHHGoodC4AnnularTaylorFactorRound67Exact
import DASHI.Physics.Closure.NSTriadKNFourierStrainModeParityRound67Exact

round67HomogeneousAndAnnularRolesSeparated : Bool
round67HomogeneousAndAnnularRolesSeparated = true

round67HardAnnulusTaylorRouteFalsified : Bool
round67HardAnnulusTaylorRouteFalsified = true

round67ExplicitC4RadialTransitionCoreConstructed : Bool
round67ExplicitC4RadialTransitionCoreConstructed = true

round67C4TransitionFrechetExpansionConstructed : Bool
round67C4TransitionFrechetExpansionConstructed = true

round67C4TransitionTaylorSquareFactorConstructed : Bool
round67C4TransitionTaylorSquareFactorConstructed = true

round67FourierStrainModeParityConstructed : Bool
round67FourierStrainModeParityConstructed = true

round67PhysicalSixThreeTaylorOverlapConstructed : Bool
round67PhysicalSixThreeTaylorOverlapConstructed = false

round67SameObjectContinuumFourfoldIBPConstructed : Bool
round67SameObjectContinuumFourfoldIBPConstructed = false

round67ClayPromotion : Bool
round67ClayPromotion = false

round67HomogeneousAndAnnularRolesSeparatedIsTrue :
  round67HomogeneousAndAnnularRolesSeparated ≡ true
round67HomogeneousAndAnnularRolesSeparatedIsTrue = refl

round67HardAnnulusTaylorRouteFalsifiedIsTrue :
  round67HardAnnulusTaylorRouteFalsified ≡ true
round67HardAnnulusTaylorRouteFalsifiedIsTrue = refl

round67ExplicitC4RadialTransitionCoreConstructedIsTrue :
  round67ExplicitC4RadialTransitionCoreConstructed ≡ true
round67ExplicitC4RadialTransitionCoreConstructedIsTrue = refl

round67C4TransitionFrechetExpansionConstructedIsTrue :
  round67C4TransitionFrechetExpansionConstructed ≡ true
round67C4TransitionFrechetExpansionConstructedIsTrue = refl

round67C4TransitionTaylorSquareFactorConstructedIsTrue :
  round67C4TransitionTaylorSquareFactorConstructed ≡ true
round67C4TransitionTaylorSquareFactorConstructedIsTrue = refl

round67FourierStrainModeParityConstructedIsTrue :
  round67FourierStrainModeParityConstructed ≡ true
round67FourierStrainModeParityConstructedIsTrue = refl

round67PhysicalSixThreeTaylorOverlapConstructedIsFalse :
  round67PhysicalSixThreeTaylorOverlapConstructed ≡ false
round67PhysicalSixThreeTaylorOverlapConstructedIsFalse = refl

round67SameObjectContinuumFourfoldIBPConstructedIsFalse :
  round67SameObjectContinuumFourfoldIBPConstructed ≡ false
round67SameObjectContinuumFourfoldIBPConstructedIsFalse = refl

round67ClayPromotionIsFalse : round67ClayPromotion ≡ false
round67ClayPromotionIsFalse = refl
