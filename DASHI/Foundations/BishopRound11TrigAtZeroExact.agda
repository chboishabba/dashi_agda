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
import DASHI.Foundations.BishopSineCosineSetoidCongruenceExact as TrigCong
import DASHI.Physics.YangMills.BalabanBishopSeriesParityAndLimitExact as Parity
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


------------------------------------------------------------------------
-- K05: ALL FOUR *ACTUAL ROUND11* ADDITION ORIGIN-SPECIALIZATIONS.
-- These consume the native signed-factorial zero/one proof and the
-- existing Round11 termwise setoid congruence. They pay the origin
-- boundaries of the eventual full two-variable addition laws.
-- No hidden general sinAdd/cosAdd hypothesis is used.
------------------------------------------------------------------------

private
  sinB : Round11.Round11BishopCutset → R.ℝ → R.ℝ
  sinB inputs = E.bishopSin (Round11.elementarySeries inputs)

  cosB : Round11.Round11BishopCutset → R.ℝ → R.ℝ
  cosB inputs = E.bishopCos (Round11.elementarySeries inputs)

round11SineAdditionRightZero :
  (inputs : Round11.Round11BishopCutset) (x : R.ℝ) →
  R._≃_
    (sinB inputs (R._+_ x R.0ℝ))
    (R._+_
      (R._*_ (sinB inputs x) (cosB inputs R.0ℝ))
      (R._*_ (cosB inputs x) (sinB inputs R.0ℝ)))
round11SineAdditionRightZero inputs x =
  RP.≃-trans
    (TrigCong.bishopSinCongruent
      (Round11.round11ConcreteTermIdentification inputs)
      (RP.+-identityʳ x))
    (RP.≃-symm
      (RP.≃-trans
        (RP.+-cong
          (RP.*-cong RP.≃-refl (round11CosineAtZero inputs))
          (RP.*-cong RP.≃-refl (round11SineAtZero inputs)))
        (let open RP.ℝ-Solver
         in solve 2
           (λ s c →
             (s ⊗ Κ 1ℚᵘ) ⊕ (c ⊗ Κ 0ℚᵘ) ⊜ s)
           RP.≃-refl (sinB inputs x) (cosB inputs x))))

round11CosineAdditionRightZero :
  (inputs : Round11.Round11BishopCutset) (x : R.ℝ) →
  R._≃_
    (cosB inputs (R._+_ x R.0ℝ))
    (R._-_
      (R._*_ (cosB inputs x) (cosB inputs R.0ℝ))
      (R._*_ (sinB inputs x) (sinB inputs R.0ℝ)))
round11CosineAdditionRightZero inputs x =
  RP.≃-trans
    (TrigCong.bishopCosCongruent
      (Round11.round11ConcreteTermIdentification inputs)
      (RP.+-identityʳ x))
    (RP.≃-symm
      (RP.≃-trans
        (RP.+-cong
          (RP.*-cong RP.≃-refl (round11CosineAtZero inputs))
          (RP.-‿cong
            (RP.*-cong RP.≃-refl (round11SineAtZero inputs))))
        (let open RP.ℝ-Solver
         in solve 2
           (λ s c →
             (c ⊗ Κ 1ℚᵘ) ⊖ (s ⊗ Κ 0ℚᵘ) ⊜ c)
           RP.≃-refl (sinB inputs x) (cosB inputs x))))

round11SineAdditionLeftZero :
  (inputs : Round11.Round11BishopCutset) (x : R.ℝ) →
  R._≃_
    (sinB inputs (R._+_ R.0ℝ x))
    (R._+_
      (R._*_ (sinB inputs R.0ℝ) (cosB inputs x))
      (R._*_ (cosB inputs R.0ℝ) (sinB inputs x)))
round11SineAdditionLeftZero inputs x =
  RP.≃-trans
    (TrigCong.bishopSinCongruent
      (Round11.round11ConcreteTermIdentification inputs)
      (RP.+-identityˡ x))
    (RP.≃-symm
      (RP.≃-trans
        (RP.+-cong
          (RP.*-cong (round11SineAtZero inputs) RP.≃-refl)
          (RP.*-cong (round11CosineAtZero inputs) RP.≃-refl))
        (let open RP.ℝ-Solver
         in solve 2
           (λ s c →
             (Κ 0ℚᵘ ⊗ c) ⊕ (Κ 1ℚᵘ ⊗ s) ⊜ s)
           RP.≃-refl (sinB inputs x) (cosB inputs x))))

round11CosineAdditionLeftZero :
  (inputs : Round11.Round11BishopCutset) (x : R.ℝ) →
  R._≃_
    (cosB inputs (R._+_ R.0ℝ x))
    (R._-_
      (R._*_ (cosB inputs R.0ℝ) (cosB inputs x))
      (R._*_ (sinB inputs R.0ℝ) (sinB inputs x)))
round11CosineAdditionLeftZero inputs x =
  RP.≃-trans
    (TrigCong.bishopCosCongruent
      (Round11.round11ConcreteTermIdentification inputs)
      (RP.+-identityˡ x))
    (RP.≃-symm
      (RP.≃-trans
        (RP.+-cong
          (RP.*-cong (round11CosineAtZero inputs) RP.≃-refl)
          (RP.-‿cong
            (RP.*-cong (round11SineAtZero inputs) RP.≃-refl)))
        (let open RP.ℝ-Solver
         in solve 2
           (λ s c →
             (Κ 1ℚᵘ ⊗ c) ⊖ (Κ 0ℚᵘ ⊗ s) ⊜ c)
           RP.≃-refl (sinB inputs x) (cosB inputs x))))


------------------------------------------------------------------------
-- K05 ANTI-DIAGONAL SINE ADDITION: x + (-x).
-- This uses the same concrete Round11 sine/cosine and the existing
-- *proven* Bishop series parity, not a hypothetical trig authority.
-- Cosine on the anti-diagonal is equivalent to Pythagorean and must
-- remain a separate genuine outstanding lemma.
------------------------------------------------------------------------

round11SineAdditionOpposite :
  (inputs : Round11.Round11BishopCutset) (x : R.ℝ) →
  R._≃_
    (sinB inputs (R._+_ x (R.- x)))
    (R._+_
      (R._*_ (sinB inputs x) (cosB inputs (R.- x)))
      (R._*_ (cosB inputs x) (sinB inputs (R.- x))))
round11SineAdditionOpposite inputs x =
  RP.≃-trans
    (RP.≃-trans
      (TrigCong.bishopSinCongruent
        (Round11.round11ConcreteTermIdentification inputs)
        (RP.+-inverseʳ x))
      (round11SineAtZero inputs))
    (RP.≃-symm
      (RP.≃-trans
        (RP.+-cong
          (RP.*-cong RP.≃-refl
            (Parity.bishopCosNeg
              (Round11.round11ParityInputs inputs) x))
          (RP.*-cong RP.≃-refl
            (Parity.bishopSinNeg
              (Round11.round11ParityInputs inputs) x)))
        (let open RP.ℝ-Solver
         in solve 2
           (λ s c → (s ⊗ c) ⊕ (c ⊗ (⊝ s)) ⊜ Κ 0ℚᵘ)
           RP.≃-refl (sinB inputs x) (cosB inputs x))))

-- A precise K05 reducer: the cosine opposite-angle addition formula
-- is obtained from the SAME Round11 Pythagorean source statement.
-- This is not a proof of Pythagorean or the full cosine addition law.
round11CosineAdditionOppositeFromPythagorean :
  (inputs : Round11.Round11BishopCutset) (x : R.ℝ) →
  R._≃_
    (R._+_
      (R._*_ (cosB inputs x) (cosB inputs x))
      (R._*_ (sinB inputs x) (sinB inputs x)))
    R.1ℝ →
  R._≃_
    (cosB inputs (R._+_ x (R.- x)))
    (R._-_
      (R._*_ (cosB inputs x) (cosB inputs (R.- x)))
      (R._*_ (sinB inputs x) (sinB inputs (R.- x))))
round11CosineAdditionOppositeFromPythagorean
    inputs x pythagorean =
  RP.≃-trans
    (RP.≃-trans
      (TrigCong.bishopCosCongruent
        (Round11.round11ConcreteTermIdentification inputs)
        (RP.+-inverseʳ x))
      (round11CosineAtZero inputs))
    (RP.≃-symm
      (RP.≃-trans
        (RP.+-cong
          (RP.*-cong RP.≃-refl
            (Parity.bishopCosNeg
              (Round11.round11ParityInputs inputs) x))
          (RP.-‿cong
            (RP.*-cong RP.≃-refl
              (Parity.bishopSinNeg
                (Round11.round11ParityInputs inputs) x))))
        (RP.≃-trans
          (let open RP.ℝ-Solver
           in solve 2
             (λ s c →
               (c ⊗ c) ⊖ (s ⊗ (⊝ s))
               ⊜ (c ⊗ c) ⊕ (s ⊗ s))
             RP.≃-refl (sinB inputs x) (cosB inputs x))
          pythagorean)))
