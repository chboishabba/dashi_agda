module DASHI.Papers.NavierStokes.TheoremInterfaceRound65Exact where

------------------------------------------------------------------------
-- PAPER-FACING ROUND65 DELTA
--
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
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
-- Round65 corrects the paper-facing B interpretation:
--
-- * the literal Com row now has exact same-carrier self/cross masses and the
--   correct finite Hermitian Cauchy--Schwarz statement;
-- * the sharp 17/64 same-shell constant cannot bound ordinary normalized row
--   self-correlation, because that equals one for a nonzero row;
-- * the sharp target therefore belongs to the factorized pair product/internal
--   branch-overlap lane;
-- * a same-carrier PhysicalFactorizedGramCell now carries precisely that lane;
-- * the canonical finite Galerkin RHS is pointwise tangent to its canonical
--   one-orbit coordinate list.
--
-- Remaining B is the literal-row -> physical factorized-cell construction and
-- the internal six-three overlap estimate.  Remaining A1 is ODE/Picard plus the
-- localized differentiated identity.  Clay promotion remains false.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Papers.NavierStokes.TheoremInterfaceRound63Exact
import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound65Exact as R65

round65PaperConsumesCurrentAggregate : Bool
round65PaperConsumesCurrentAggregate = true

round65PaperClayPromotion : Bool
round65PaperClayPromotion = R65.round65ClayPromotion

round65PaperConsumesCurrentAggregateIsTrue :
  round65PaperConsumesCurrentAggregate ≡ true
round65PaperConsumesCurrentAggregateIsTrue = refl

round65PaperClayPromotionIsFalse : round65PaperClayPromotion ≡ false
round65PaperClayPromotionIsFalse = R65.round65ClayPromotionIsFalse
