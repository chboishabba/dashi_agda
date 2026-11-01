module DASHI.Analysis.BishopMachinEventualHalfPlaneExact where

------------------------------------------------------------------------
-- K04d1: ACTUAL BISHOP MACHIN STAGES ARE EVENTUALLY IN A STRONG
-- POSITIVE REAL HALF-PLANE: q_n > 3, HENCE > 1.
--
-- No uniform geometric modulus is needed for this topological theorem.
-- The original Bishop Sequence library constructs epsilon indices
-- directly from convergence, and the original DASHI Machin window
-- gives 3 < bishopMachinPi.
--
-- Note: the analytic carrier's separate, opaque predicate
-- realPartGreaterThanOne is NOT identified with Bishop order here.
-- That concrete half-plane predicate identity must be supplied by
-- the actual analytic function implementation, not assumed to hold
-- for every arbitrary AnalyticSubstrate.
--
-- Source: Murray (2022), arXiv:2205.08354; original
-- BishopMachinPiRationalWindowExact and K04a/Bishop finite series.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Nat.Base using (_≤_)
open import Data.Product.Base using (proj₁; proj₂)
open import Agda.Builtin.Sigma using (Σ; _,_)
import Real as Bishop
import RealProperties as RP
import Sequence as Series

import DASHI.Analysis.BishopMachinRationalStageEmbeddingExact as Q
import DASHI.Foundations.BishopMachinArctanConstructionExact as M
import DASHI.Foundations.BishopMachinPiRationalWindowExact as Window

EventuallyStrictlyAbove :
  (Nat → Bishop.ℝ) → Bishop.ℝ → Set
EventuallyStrictlyAbove sequence lower =
  Σ Nat (λ start →
    ∀ n → start ≤ n → Bishop._<_ lower (sequence n))

-- Universal strict-order stability under convergence, proved over
-- the SAME imported Bishop real and its epsilon-extraction theorem.
bishopConvergenceEventuallyAbove :
  ∀ {sequence : Nat → Bishop.ℝ} {limit lower : Bishop.ℝ} →
  Series._ConvergesTo_ sequence limit →
  Bishop._<_ lower limit →
  EventuallyStrictlyAbove sequence lower
bishopConvergenceEventuallyAbove
  {sequence} {limit} {lower} converges lowerBelowLimit =
  suc (proj₁ epsilonReceipt) ,
  λ n nLarge →
    let
      point = sequence n
      errorBelowDifference :
        Bishop._<_
          (Bishop._-_ limit point)
          (Bishop._-_ limit lower)
      errorBelowDifference =
        RP.≤-<-trans
          (RP.≤-respʳ-≃
            (RP.∣x-y∣≃∣y-x∣ limit point)
            (RP.x≤∣x∣ {x = Bishop._-_ limit point}))
          (proj₂ epsilonReceipt n nLarge)

      raw :
        Bishop._<_
          (Bishop._+_ limit
            (Bishop.-_ (Bishop._-_ limit lower)))
          (Bishop._+_ limit
            (Bishop.-_ (Bishop._-_ limit point)))
      raw =
        RP.+-monoˡ-< limit
          (RP.neg-mono-< errorBelowDifference)

      leftEq :
        Bishop._≃_
          (Bishop._+_ limit
            (Bishop.-_ (Bishop._-_ limit lower)))
          lower
      leftEq =
        let open RP.ℝ-Solver
        in solve 2
          (λ l a → l ⊕ (⊝ (l ⊖ a)) ⊜ a)
          RP.≃-refl limit lower

      rightEq :
        Bishop._≃_
          (Bishop._+_ limit
            (Bishop.-_ (Bishop._-_ limit point)))
          point
      rightEq =
        let open RP.ℝ-Solver
        in solve 2
          (λ l a → l ⊕ (⊝ (l ⊖ a)) ⊜ a)
          RP.≃-refl limit point
    in
    RP.<-respʳ-≃ rightEq
      (RP.<-respˡ-≃ leftEq raw)
  where
  epsilon = Bishop._-_ limit lower

  epsilonReceipt =
    Series.fast-ε-from-convergence
      (limit , converges)
      epsilon
      (RP.0<x⇒posx
        (RP.x<y⇒0<y-x lower limit lowerBelowLimit))

-- Stronger than merely σ>1: eventually the actual q_n lies strictly
-- above 3, using existing original source-proved 3<pi_M.
machinRationalStagesEventuallyAboveThree :
  EventuallyStrictlyAbove
    (λ n → Bishop._⋆ (Q.qMachinStage n))
    (Window.embed Window.three)
machinRationalStagesEventuallyAboveThree =
  bishopConvergenceEventuallyAbove
    Q.rationalMachinStagesConvergeToOriginalMachinPi
    Window.threeBelowMachinPi
