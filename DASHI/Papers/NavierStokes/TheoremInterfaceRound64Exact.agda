module DASHI.Papers.NavierStokes.TheoremInterfaceRound64Exact where

------------------------------------------------------------------------
-- PAPER-FACING ROUND64 DELTA
--
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Round64 strengthens the B-side paper boundary: every coefficient in the
-- literal centered Com physical-output-fibre row now carries a constructed
-- dominant common dyadic hat on the exact same resonant incidence index.
-- Projection of the packaged row recovers both the original incidence list and
-- the original literal coefficient list definitionally/theoremically.
--
-- The remaining B producer is therefore normalization/Gram realization plus
-- the six-three overlap inequality, not support identification.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Papers.NavierStokes.TheoremInterfaceRound63Exact
import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound64Exact as R64

round64PaperConsumesLiteralDominantHatComRow : Bool
round64PaperConsumesLiteralDominantHatComRow =
  R64.round64LiteralComRowDominantHatLocalizationConstructed

round64PaperClayPromotion : Bool
round64PaperClayPromotion = R64.round64ClayPromotion

round64PaperConsumesLiteralDominantHatComRowIsTrue :
  round64PaperConsumesLiteralDominantHatComRow ≡ true
round64PaperConsumesLiteralDominantHatComRowIsTrue =
  R64.round64LiteralComRowDominantHatLocalizationConstructedIsTrue

round64PaperClayPromotionIsFalse : round64PaperClayPromotion ≡ false
round64PaperClayPromotionIsFalse = R64.round64ClayPromotionIsFalse
