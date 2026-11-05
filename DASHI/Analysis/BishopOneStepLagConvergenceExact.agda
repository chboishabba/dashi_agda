{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopOneStepLagConvergenceExact where

------------------------------------------------------------------------
-- A convergent Bishop history remains convergent after one-step lag.
-- This is the literal Nat.pred reindex needed by the telescoping K05
-- grouped-factorial identity: the Nth finite Cauchy triangle differs
-- from the original phase prefix by O_(N-1), not O_N.
--
-- Zero-index behavior does not affect the constructive Bishop limit.
-- No limit assumption or noncofinal subsequence is introduced.
-- Bishop and Bridges; Murray/Csimma, original Sequence.con*.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
import Data.Nat.Base as N
open import Data.Product.Base using (proj₁; proj₂)

import Real as R
import Sequence as S

oneStepLagConverges :
  (history : Nat → R.ℝ) →
  (limit : R.ℝ) →
  S._ConvergesTo_ history limit →
  S._ConvergesTo_ (λ n → history (N.pred n)) limit
oneStepLagConverges history limit (S.con* h) =
  S.con* (λ
    { (suc k-1) →
      let
        receipt = h (suc k-1)
        cutoff = suc (proj₁ receipt)
      in
      cutoff ,
      (λ
        { (suc n-1) (N.s≤s predecessorPastCutoff) →
          proj₂ receipt n-1 predecessorPastCutoff
        })
    })
