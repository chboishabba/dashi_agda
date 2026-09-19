module DASHI.Foundations.BishopFiniteSeriesDifferenceExact where

------------------------------------------------------------------------
-- FINITE BISHOP SERIES LINEARITY FOR SUBTRACTION
--
-- DASHI CONTRIBUTION
--
--   S_n(f) - S_n(g)  ~=  S_n(f-g).
--
-- This finite identity is used by the Cauchy-product wing decomposition.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Unnormalised using (0ℚᵘ)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

finiteSeriesDifference :
  (left right : Nat → BishopReal.ℝ) →
  ∀ count →
  BishopReal._≃_
    (BishopReal._-_
      (BishopSequence.SeriesOf left count)
      (BishopSequence.SeriesOf right count))
    (BishopSequence.SeriesOf
      (λ index → BishopReal._-_ (left index) (right index))
      count)
finiteSeriesDifference left right zero =
  let open BishopP.ℝ-Solver
  in solve 0
    (Κ 0ℚᵘ ⊖ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ)
    BishopP.≃-refl
finiteSeriesDifference left right (suc count) =
  BishopP.≃-trans
    (let open BishopP.ℝ-Solver
     in solve 4
       (λ leftPrefix leftTerm rightPrefix rightTerm →
         ((leftPrefix ⊕ leftTerm) ⊖ (rightPrefix ⊕ rightTerm))
         ⊜ ((leftPrefix ⊖ rightPrefix) ⊕
             (leftTerm ⊖ rightTerm)))
       BishopP.≃-refl
       (BishopSequence.SeriesOf left count)
       (left count)
       (BishopSequence.SeriesOf right count)
       (right count))
    (BishopP.+-cong
      (finiteSeriesDifference left right count)
      BishopP.≃-refl)
