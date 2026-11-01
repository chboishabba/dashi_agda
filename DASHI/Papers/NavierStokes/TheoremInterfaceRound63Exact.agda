module DASHI.Papers.NavierStokes.TheoremInterfaceRound63Exact where

------------------------------------------------------------------------
-- PAPER-FACING ROUND63 DELTA
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
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- Keep the large historical paper interface stable while importing the
-- theorem-producing Round63 delta.  The corrected public frontier is:
--
-- * A0 fixed-cutoff reality-orbit enumeration and literal RHS count repair are
--   constructed; fixed-N trajectory/Picard and differentiated shell identity
--   remain physical producers.
-- * C1 is exactly `forall n, Xi_n <= K` for
--       Xi_n = X_n/(C r^n)
--   on the positive block branch.
-- * B0 simple projector-annulus support is formally rejected, but every
--   resonant triangle has a constructed width-one common hat on its two
--   dominant legs.  B1 must factor the dominant-hat localized row into an
--   actual normalized Gram/Schur cell; B3 must then prove six-three overlap.
-- * the historical Gram cell does not itself imply overlap<=1; normalized B1
--   must establish that contraction before the 17/64 and 65/512 sharpening.
-- * HH-bad hard cost is optimized through Lambda_bad=C_* K_bad.
-- * D/F official Pair proof uniqueness is insufficient for endpoint
--   functionality; a coefficient/owner-preserving functional enumeration is
--   still required.
--
-- This module deliberately leaves Clay and terminal promotion false.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Papers.NavierStokes.TheoremInterface
import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound63Exact as R63

round63PaperConsumesCurrentAggregate : Bool
round63PaperConsumesCurrentAggregate = true

round63PaperClayPromotion : Bool
round63PaperClayPromotion = R63.round63ClayPromotion

round63PaperConsumesCurrentAggregateIsTrue :
  round63PaperConsumesCurrentAggregate ≡ true
round63PaperConsumesCurrentAggregateIsTrue = refl

round63PaperClayPromotionIsFalse : round63PaperClayPromotion ≡ false
round63PaperClayPromotionIsFalse = R63.round63ClayPromotionIsFalse
