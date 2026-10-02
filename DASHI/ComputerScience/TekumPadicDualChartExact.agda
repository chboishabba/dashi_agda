module DASHI.ComputerScience.TekumPadicDualChartExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Vec using (Vec)
open import Data.Vec.Base using (reverse)
open import Data.Vec.Properties using (reverse-involutive)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Algebra.Trit as Trit
import DASHI.ComputerScience.TekumTruncationRoundingExact as Tekum

------------------------------------------------------------------------
-- Reversal is the exact chart needed to exchange the two finite orientations:
--
-- Tekum's LST-first precision reduction removes the head (low significance).
-- In the reversed chart that same operation removes the tail (high index),
-- matching the direction of a low-order-prefix cylinder refinement.

dualChart : ∀ {n} → Vec Trit.Trit n → Vec Trit.Trit n
dualChart = reverse

dualChartInvolutive :
  ∀ {n} (xs : Vec Trit.Trit n) →
  dualChart (dualChart xs) ≡ xs
dualChartInvolutive = reverse-involutive

dualPrecisionTwo :
  ∀ {n} →
  Vec Trit.Trit (suc (suc n)) →
  Vec Trit.Trit n
dualPrecisionTwo xs =
  dualChart (Tekum.truncateTwo (dualChart xs))

tekumPrecisionConjugatesToDual :
  ∀ {n} (xs : Vec Trit.Trit (suc (suc n))) →
  dualChart (Tekum.truncateTwo xs)
  ≡ dualPrecisionTwo (dualChart xs)
tekumPrecisionConjugatesToDual xs
  rewrite dualChartInvolutive xs = refl

dualPrecisionFour :
  ∀ {n} →
  Vec Trit.Trit (suc (suc (suc (suc n)))) →
  Vec Trit.Trit n
dualPrecisionFour xs =
  dualChart
    (Tekum.truncateFourDirect
      (dualChart xs))

dualTwoStepComposition :
  ∀ {n}
  (xs : Vec Trit.Trit (suc (suc (suc (suc n))))) →
  dualPrecisionTwo (dualPrecisionTwo xs)
  ≡ dualPrecisionFour xs
dualTwoStepComposition xs =
  cong dualChart
    (trans
      (cong Tekum.truncateTwo (dualChartInvolutive (Tekum.truncateTwo (dualChart xs))))
      (Tekum.truncateTwoTwiceEqualsFour (dualChart xs)))

record TekumPadicDualChartBoundary : Set where
  constructor tekumPadicDualChartBoundary
  field
    reversalIsInvolution : Bool
    tekumTruncationHasExactDualConjugate : Bool
    dualTwoStepCompositionPaid : Bool
    dualChartAloneProvesNearestRounding : Bool
    dualChartAlonePromotesRealToPadic : Bool

canonicalTekumPadicDualChartBoundary : TekumPadicDualChartBoundary
canonicalTekumPadicDualChartBoundary =
  tekumPadicDualChartBoundary true true true false false
