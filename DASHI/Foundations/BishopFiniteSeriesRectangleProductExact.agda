module DASHI.Foundations.BishopFiniteSeriesRectangleProductExact where

------------------------------------------------------------------------
-- FINITE RECTANGLE PRODUCT IDENTITY
--
-- For Bishop-real sequences a,b, the product of finite partial sums equals the
-- corresponding finite rectangular double sum.  This is the purely algebraic
-- half of the Cauchy-product argument; no convergence is used here.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

open import DASHI.Physics.YangMills.CompactLieProofLevel

rectangleRow :
  (left right : Nat → BishopReal.ℝ) →
  Nat → Nat → BishopReal.ℝ
rectangleRow left right i width =
  BishopReal._*_
    (left i)
    (BishopSequence.SeriesOf right width)

rectangleSum :
  (left right : Nat → BishopReal.ℝ) →
  Nat → Nat → BishopReal.ℝ
rectangleSum left right height width =
  BishopSequence.SeriesOf
    (λ i → rectangleRow left right i width)
    height

rectangleProduct :
  (left right : Nat → BishopReal.ℝ) →
  ∀ height width →
  BishopReal._≃_
    (rectangleSum left right height width)
    (BishopReal._*_
      (BishopSequence.SeriesOf left height)
      (BishopSequence.SeriesOf right width))
rectangleProduct left right zero width =
  let open BishopP.ℝ-Solver
  in solve 1
    (λ rightSum → Κ 0ℚᵘ ⊜ Κ 0ℚᵘ ⊗ rightSum)
    BishopP.≃-refl
    (BishopSequence.SeriesOf right width)
rectangleProduct left right (suc height) width =
  let
    oldLeft = BishopSequence.SeriesOf left height
    rightSum = BishopSequence.SeriesOf right width
    nextLeft = left height
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (BishopP.+-cong
      (rectangleProduct left right height width)
      BishopP.≃-refl)
    (solve 3
      (λ old next rightValue →
        (old ⊗ rightValue) ⊕ (next ⊗ rightValue)
        ⊜ (old ⊕ next) ⊗ rightValue)
      BishopP.≃-refl
      oldLeft nextLeft rightSum)

bishopFiniteRectangleProductLevel : ProofLevel
bishopFiniteRectangleProductLevel = machineChecked
