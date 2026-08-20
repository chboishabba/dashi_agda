module DASHI.Papers.NavierStokes.TheoremInterfaceRound67Exact where

------------------------------------------------------------------------
-- PAPER-FACING ROUND67 DELTA
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
-- Round67 replaces the ambiguous "smooth the hard annulus" instruction by a
-- concrete and falsifiable theorem chain.
--
-- 1. A radially scale-invariant nonzero cutoff cannot be compactly annular.
--    Homogeneity belongs to the order-zero strain symbol, not the annular
--    localization.
--
-- 2. A hard integer/dyadic cutoff has an order-one jump under one lattice step
--    at every scale, so no high-frequency Taylor smallness may be extracted
--    from the hard projector itself.
--
-- 3. The explicit degree-9 smoothstep has four vanishing endpoint derivative
--    jets and an exact Frechet expansion.  Its remainder factors literally as
--
--       R(x,h) = h^2 Q(x,h).
--
--    Thus a genuine second-order cutoff Taylor factor is now constructed.
--
-- 4. The literal Fourier strain multiplier is even under k -> -k.  Hence the
--    Round66 low-output branch may use the close dominant pair p,-q whose
--    displacement is the low output, without a parity mismatch.
--
-- The remaining paper-facing B/E theorem is quantitative rather than
-- structural: put this smooth radial transition on the actual continuum
-- matrix symbol, control the angular-strain derivatives on the Round66 branch
-- geometry, obtain the normalized physical six-three overlap, and perform the
-- same-object fourfold inverse-Fourier integration by parts.  Round65 and
-- Round62 already consume those two outputs respectively.  Clay promotion is
-- still false.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Papers.NavierStokes.TheoremInterfaceRound66Exact
import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound67Exact as R67

round67PaperHardAnnulusTaylorRouteFalsified : Bool
round67PaperHardAnnulusTaylorRouteFalsified =
  R67.round67HardAnnulusTaylorRouteFalsified

round67PaperExplicitC4TransitionConstructed : Bool
round67PaperExplicitC4TransitionConstructed =
  R67.round67ExplicitC4RadialTransitionCoreConstructed

round67PaperTaylorSquareFactorConstructed : Bool
round67PaperTaylorSquareFactorConstructed =
  R67.round67C4TransitionTaylorSquareFactorConstructed

round67PaperLowOutputParityConstructed : Bool
round67PaperLowOutputParityConstructed =
  R67.round67FourierStrainModeParityConstructed

round67PaperPhysicalSixThreeOverlapStillOpen : Bool
round67PaperPhysicalSixThreeOverlapStillOpen =
  R67.round67PhysicalSixThreeTaylorOverlapConstructed

round67PaperContinuumFourfoldIBPStillOpen : Bool
round67PaperContinuumFourfoldIBPStillOpen =
  R67.round67SameObjectContinuumFourfoldIBPConstructed

round67PaperClayPromotion : Bool
round67PaperClayPromotion = R67.round67ClayPromotion

round67PaperHardAnnulusTaylorRouteFalsifiedIsTrue :
  round67PaperHardAnnulusTaylorRouteFalsified ≡ true
round67PaperHardAnnulusTaylorRouteFalsifiedIsTrue = refl

round67PaperExplicitC4TransitionConstructedIsTrue :
  round67PaperExplicitC4TransitionConstructed ≡ true
round67PaperExplicitC4TransitionConstructedIsTrue = refl

round67PaperTaylorSquareFactorConstructedIsTrue :
  round67PaperTaylorSquareFactorConstructed ≡ true
round67PaperTaylorSquareFactorConstructedIsTrue = refl

round67PaperLowOutputParityConstructedIsTrue :
  round67PaperLowOutputParityConstructed ≡ true
round67PaperLowOutputParityConstructedIsTrue = refl

round67PaperPhysicalSixThreeOverlapStillOpenIsFalse :
  round67PaperPhysicalSixThreeOverlapStillOpen ≡ false
round67PaperPhysicalSixThreeOverlapStillOpenIsFalse = refl

round67PaperContinuumFourfoldIBPStillOpenIsFalse :
  round67PaperContinuumFourfoldIBPStillOpen ≡ false
round67PaperContinuumFourfoldIBPStillOpenIsFalse = refl

round67PaperClayPromotionIsFalse : round67PaperClayPromotion ≡ false
round67PaperClayPromotionIsFalse = R67.round67ClayPromotionIsFalse
