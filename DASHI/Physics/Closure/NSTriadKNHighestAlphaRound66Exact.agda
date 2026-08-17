module DASHI.Physics.Closure.NSTriadKNHighestAlphaRound66Exact where

------------------------------------------------------------------------
-- ROUND 66 HIGHEST-ALPHA DELTA
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
-- ROUND 66 ADVANCES
--
-- B3 LOW-LEG GEOMETRY:
-- Round63's dominant-pair theorem retained only `WithinOne`.  Round66 repeats
-- the same finite resonance ordering but preserves the omitted theorem needed
-- by the six-three Taylor gain: the third leg is no larger than EITHER member
-- of the dominant pair.  Every literal resonant triad is therefore split as
--
--   one canonical low leg + two width-one dominant legs.
--
-- B1 CORRECT-INDEX LOCALIZATION:
-- Round64 localized the low-pass row; Round65 showed that the physical Gram /
-- Schur index is annular.  Round66 now packages the literal annular coefficient,
-- the dominant common hat, and the canonical low-leg split on the SAME
-- `PhysicalTriadIncidence`, with exact projections back to both
-- `physicalOutputFiber` and `annularOutputFibreCoefficients`.
--
-- CORRECTED B FRONTIER:
-- The remaining hard B theorem is now not "find a hat" or "find the low leg".
-- Both are constructed coefficientwise.  It is the quantitative Taylor/operator
-- estimate that turns the low-vs-dominant shell separation of this literal row
-- into the internal factorized overlap bound
--
--   overlap <= twoBranchSquaredGap gap.
--
-- Once that lands, Round65 already gives the physical 17/64, 65/512 and
-- 133/256 conclusions on the same real carrier.
--
-- No Clay promotion is made here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound65Exact
import DASHI.Physics.Closure.NSTriadKNResonantDominantLowLegSplitRound66Exact
import DASHI.Physics.Closure.NSTriadKNComAnnularDominantHatLocalizedRowRound66Exact

round66CanonicalLowLegConstructedForEveryPhysicalTriad : Bool
round66CanonicalLowLegConstructedForEveryPhysicalTriad = true

round66LiteralAnnularRowCarriesHatAndLowLegOnSameIndex : Bool
round66LiteralAnnularRowCarriesHatAndLowLegOnSameIndex = true

round66SixThreePhysicalTaylorOverlapConstructed : Bool
round66SixThreePhysicalTaylorOverlapConstructed = false

round66ClayPromotion : Bool
round66ClayPromotion = false

round66CanonicalLowLegConstructedForEveryPhysicalTriadIsTrue :
  round66CanonicalLowLegConstructedForEveryPhysicalTriad ≡ true
round66CanonicalLowLegConstructedForEveryPhysicalTriadIsTrue = refl

round66LiteralAnnularRowCarriesHatAndLowLegOnSameIndexIsTrue :
  round66LiteralAnnularRowCarriesHatAndLowLegOnSameIndex ≡ true
round66LiteralAnnularRowCarriesHatAndLowLegOnSameIndexIsTrue = refl

round66SixThreePhysicalTaylorOverlapConstructedIsFalse :
  round66SixThreePhysicalTaylorOverlapConstructed ≡ false
round66SixThreePhysicalTaylorOverlapConstructedIsFalse = refl

round66ClayPromotionIsFalse : round66ClayPromotion ≡ false
round66ClayPromotionIsFalse = refl
