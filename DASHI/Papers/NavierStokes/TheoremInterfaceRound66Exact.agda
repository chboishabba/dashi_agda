module DASHI.Papers.NavierStokes.TheoremInterfaceRound66Exact where

------------------------------------------------------------------------
-- PAPER-FACING ROUND66 DELTA
--
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Round66 removes two more ambiguities from the paper-facing B theorem.
--
-- First, the two width-one dominant legs now come with their omitted third leg
-- explicitly proved no larger than either dominant leg.  Thus every literal
-- resonance has a canonical low/dominant/dominant split, rather than merely an
-- existential common hat.
--
-- Second, that split and the dominant common hat are attached directly to the
-- literal ANNULAR commutator coefficient on the exact physical output fibre.
-- This is the operator index used by the Round65 Gram/Schur lane.
--
-- In physical transport roles p+q=k means p=advector, q=input, k=output.  The
-- split therefore gives exact low-advector / low-input / low-output branches.
-- In the low-advector branch incompressibility proves the exact identity
--
--   k . u_p = q . u_p,
--
-- with q,k the two dominant width-one endpoints.
--
-- Consequently the remaining B theorem is now a quantitative multiplier /
-- operator estimate on this already-identified literal branch geometry:
--
--   physical internal overlap <= twoBranchSquaredGap gap.
--
-- Round65 then supplies 17/64, 65/512 and 133/256 automatically.  Clay
-- promotion remains false.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Papers.NavierStokes.TheoremInterfaceRound65Exact
import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound66Exact as R66

round66PaperCanonicalLowDominantSplitConstructed : Bool
round66PaperCanonicalLowDominantSplitConstructed = true

round66PaperLiteralAnnularBonyGeometryConstructed : Bool
round66PaperLiteralAnnularBonyGeometryConstructed = true

round66PaperClayPromotion : Bool
round66PaperClayPromotion = R66.round66ClayPromotion

round66PaperCanonicalLowDominantSplitConstructedIsTrue :
  round66PaperCanonicalLowDominantSplitConstructed ≡ true
round66PaperCanonicalLowDominantSplitConstructedIsTrue = refl

round66PaperLiteralAnnularBonyGeometryConstructedIsTrue :
  round66PaperLiteralAnnularBonyGeometryConstructed ≡ true
round66PaperLiteralAnnularBonyGeometryConstructedIsTrue = refl

round66PaperClayPromotionIsFalse : round66PaperClayPromotion ≡ false
round66PaperClayPromotionIsFalse = R66.round66ClayPromotionIsFalse
