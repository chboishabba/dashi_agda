module DASHI.Foundations.BishopRound11TrigAtZeroExact where

------------------------------------------------------------------------
-- K05 / K04d: NATIVE ROUND11 BISHOP SINE AND COSINE AT THE ORIGIN.
--
-- Reuse the original signed-factorial term families, their concrete
-- Round11 convergence, and pinned Bishop Sequence.uniqueness-of-limits.
-- The zero-angle identities are proved from literal finite sums.
-- No external classical trigonometric object or new power series.
--
-- Original analysis: Bishop and Bridges, Constructive Analysis (1985);
-- Zachary Murray (2022, arXiv:2205.08354); viktorcsimma/bishop.
-- DASHI owns this specialization. Kernel check pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
open import Relation.Binary.PropositionalEquality using (cong)

import Real as R
import RealProperties as RP
import Sequence as Seq

import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as E
import DASHI.Foundations.BishopConcreteTrigSeriesConvergenceExact as Trig
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as Terms
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as Estimates
import DASHI.Analysis.BishopConcreteSineCosineFiniteTermDerivativeExact as Finite
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11

zeroPowSuccessor : (n : Nat) →
  R._≃_ (R.pow R.0ℝ (suc n)) R.0ℝ
zeroPowSuccessor n =
  let open RP.ℝ-Solver
  in solve 1
    (λ previous → previous ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ)
    RP.≃-refl (R.pow R.0ℝ n)

sineSignedTermAtZero : (index : Nat) →
  R._≃_ (Terms.sineSignedTerm R.0ℝ index) R.0ℝ
sineSignedTermAtZero index =
  RP.≃-trans
    (RP.*-congˡ
      (RP.*-congˡ
        (RP.≃-refl₂
          (cong (R.pow R.0ℝ)
            (Finite.oddIsSuccessorEven index)))))
    (RP.≃-trans
      (RP.*-congˡ
        (RP.*-congˡ
          (zeroPowSuccessor (Estimates.evenExponent index))))
      (let open RP.ℝ-Solver
       in solve 2
         (λ sign coefficient →
           sign ⊗ (coefficient ⊗ Κ 0ℚᵘ) ⊜ Κ 0ℚᵘ)
         RP.≃-refl
         (Terms.alternatingSign index)
         (R._⋆ (Estimates.inverseFactorialRational
           (Estimates.oddExponent index)))))

cosineSignedTermAtZeroHead :
  R._≃_ (Terms.cosineSignedTerm R.0ℝ zero) R.1ℝ
cosineSignedTermAtZeroHead =
  let open RP.ℝ-Solver
  in solve 0
    (Κ 1ℚᵘ ⊗ (Κ 1ℚᵘ ⊗ Κ 1ℚᵘ) ⊜ Κ 1ℚᵘ)
    RP.≃-refl

cosineSignedTermAtZeroTail : (index : Nat) →
  R._≃_ (Terms.cosineSignedTerm R.0ℝ (suc index)) R.0ℝ
cosineSignedTermAtZeroTail index =
  RP.≃-trans
    (RP.*-congˡ
      (RP.*-congˡ
        (zeroPowSuccessor (suc (Estimates.evenExponent index)))))
    (let open RP.ℝ-Solver
     in solve 2
       (λ sign coefficient →
         sign ⊗ (coefficient ⊗ Κ 0ℚᵘ) ⊜ Κ 0ℚᵘ)
       RP.≃-refl
       (Terms.alternatingSign (suc index))
       (R._⋆ (Estimates.inverseFactorialRational
         (Estimates.evenExponent (suc index)))))

sinePartialAtZero : (count : Nat) →
  R._≃_
    (Seq.SeriesOf (Terms.sineSignedTerm R.0ℝ) count)
    R.0ℝ
sinePartialAtZero zero = RP.≃-refl
sinePartialAtZero (suc count) =
  RP.≃-trans
    (RP.+-cong
      (sinePartialAtZero count)
      (sineSignedTermAtZero count))
    (RP.+-identityʳ R.0ℝ)

cosinePartialAtZero : (count : Nat) →
  R._≃_
    (Seq.SeriesOf (Terms.cosineSignedTerm R.0ℝ) (suc count))
    R.1ℝ
cosinePartialAtZero zero =
  RP.≃-trans
    (RP.+-cong RP.≃-refl cosineSignedTermAtZeroHead)
    (RP.+-identityˡ R.1ℝ)
cosinePartialAtZero (suc count) =
  RP.≃-trans
    (RP.+-cong
      (cosinePartialAtZero count)
      (cosineSignedTermAtZeroTail count))
    (RP.+-identityʳ R.1ℝ)

round11SineAtZero :
  (inputs : Round11.Round11BishopCutset) →
  R._≃_ (E.bishopSin (Round11.elementarySeries inputs) R.0ℝ) R.0ℝ
round11SineAtZero inputs =
  Seq.uniqueness-of-limits
    (Trig.concreteSineSeriesConverges inputs R.0ℝ)
    (Seq.xₙ≃c⇒xₙ→c
      (λ {(suc n) → sinePartialAtZero (suc n)}))

round11CosineAtZero :
  (inputs : Round11.Round11BishopCutset) →
  R._≃_ (E.bishopCos (Round11.elementarySeries inputs) R.0ℝ) R.1ℝ
round11CosineAtZero inputs =
  Seq.uniqueness-of-limits
    (Trig.concreteCosineSeriesConverges inputs R.0ℝ)
    (Seq.xₙ≃c⇒xₙ→c
      (λ {(suc n) → cosinePartialAtZero n}))
