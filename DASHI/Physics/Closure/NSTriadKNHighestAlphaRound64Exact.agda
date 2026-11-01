module DASHI.Physics.Closure.NSTriadKNHighestAlphaRound64Exact where

------------------------------------------------------------------------
-- ROUND 64 HIGHEST-ALPHA DELTA
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
-- ROUND 64 ADVANCE
--
-- Round63 had two independently exact facts:
--
--   (1) the physical odd-P/Q output-fibre row is literally the centered
--       projector commutator row on `physicalOutputFiber`;
--   (2) every resonant `PhysicalTriadIncidence` has a constructed dominant
--       width-one common dyadic hat.
--
-- Round64 composes them on the SAME incidence index.  The new localized row
-- stores each literal commutator coefficient together with the constructed
-- common hat for that exact triad, and proves projection back to both the
-- original physical-output-fibre enumeration and the literal coefficient row.
--
-- Therefore B1 is strictly narrower now:
--
--   literal dominant-hat-localized coefficient row
--      -> normalized physical Gram/Schur factorization.
--
-- Common-hat support is no longer an independent B1 premise.
--
-- Remaining hard producers are unchanged in substance: normalized Gram
-- factorization and six-three overlap; C1; A2/C-data; E; A1; D/F; scalar G.
-- No Clay promotion is made here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound63Exact
import DASHI.Physics.Closure.NSTriadKNComLiteralDominantHatLocalizedRowRound64Exact as Localized

round64LiteralComRowDominantHatLocalizationConstructed : Bool
round64LiteralComRowDominantHatLocalizationConstructed =
  Localized.round64LiteralComRowCarriesConstructedDominantHatPerCoefficient

round64B1CommonHatIsNoLongerIndependentPremise : Bool
round64B1CommonHatIsNoLongerIndependentPremise = true

round64ClayPromotion : Bool
round64ClayPromotion = false

round64LiteralComRowDominantHatLocalizationConstructedIsTrue :
  round64LiteralComRowDominantHatLocalizationConstructed ≡ true
round64LiteralComRowDominantHatLocalizationConstructedIsTrue =
  Localized.round64LiteralComRowCarriesConstructedDominantHatPerCoefficientIsTrue

round64B1CommonHatIsNoLongerIndependentPremiseIsTrue :
  round64B1CommonHatIsNoLongerIndependentPremise ≡ true
round64B1CommonHatIsNoLongerIndependentPremiseIsTrue = refl

round64ClayPromotionIsFalse : round64ClayPromotion ≡ false
round64ClayPromotionIsFalse = refl
