module DASHI.Physics.YangMills.YMClayCMP102OriginalOddFinRecurrenceExact where

------------------------------------------------------------------------
-- The actual ORIGINAL odd-part count-indexed source, including both
-- exceptional endpoints k=0 and k=1. Source: original CMP102 oddPart
-- in YMClayCMP102OriginalEndpointCauchyShiftExact, not an alternate
-- truncated polynomial or a declared odd row axiom.
--
-- Finite native induction consumes the single weighted Cauchy
-- term/power identity at degree k>=2. The latter is the common
-- ORIGINAL Bishop Fin-index source leaf with the even row.
-- SOURCE-WRITTEN; needs pinned Agda 2.9 elaboration.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ; _/_)
import Real as R
import RealProperties as P
import Sequence as Seq
import DASHI.Foundations.BishopFinSumSeriesBridgeExact as FinSum
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Physics.YangMills.YMClayCMP102OriginalOddEvenFinRowBIDIExact as O
import DASHI.Physics.YangMills.YMClayCMP102OriginalGToTailAlgebraExact as T
import DASHI.Physics.YangMills.YMClayCMP102OriginalEndpointCauchyShiftExact as C
import DASHI.Physics.YangMills.YMClayCMP102OriginalFiniteCauchyWingBoundsExact as W
import DASHI.Physics.YangMills.YMClayCMP102OriginalGFiniteLimitTransportExact as G

-- The two-shift original odd Cauchy monomial identity. This is not
-- claimed without proof: native finite power × Cauchy reindex is
-- precisely the last common donor required by both row consumers.
OddWeightedCauchy : R.ℝ → Set
OddWeightedCauchy X =
  ∀ n → R._≃_
    (R._*_ (Row.cauchyCoefficient C.bCoefficient C.bCoefficient n)
      (R.pow X (suc (suc n))))
    (R._*_ (R._*_ X X)
      (Row.cauchyCoefficient (W.bTerm X) (W.bTerm X) n))

-- The k=1 odd coefficient is only the original first B-term.
originalOddFirstTerm : ∀ X →
  R._≃_
    (O.originalOddAt X (suc zero))
    (R._*_ (R._*_ C.two X) (W.bTerm X zero))
originalOddFirstTerm X =
  let
    b = C.bCoefficient zero
    open P.ℝ-Solver
  in
  solve 2
    (λ x b →
      (Κ (+ 2 / 1) ⊗ b) ⊗ x
      ⊜ ((Κ (+ 2 / 1) ⊗ x) ⊗ b))
    P.≃-refl X b

-- The true higher odd shifted-Cauchy row, with both X² and
-- the exact original b_(n+1) term, all degrees n>=0.
originalOddHigherTerm :
  ∀ X n → OddWeightedCauchy X →
  R._≃_
    (O.originalOddAt X (suc (suc n)))
    (R._+_
      (R._*_ (R._*_ C.two X) (W.bTerm X (suc n)))
      (R._*_ (R._*_ X X)
        (Row.cauchyCoefficient (W.bTerm X) (W.bTerm X) n)))
originalOddHigherTerm X n weighted =
  let
    b = C.bCoefficient (suc n)
    p = R.pow X (suc (suc n))
    q = Row.cauchyCoefficient C.bCoefficient C.bCoefficient n
    open P.ℝ-Solver
  in
  P.≃-trans
    (solve 3
      (λ x b p →
        (Κ (+ 2 / 1) ⊗ b) ⊗ p
        ⊜ ((Κ (+ 2 / 1) ⊗ x) ⊗
             (b ⊗ (p ⊘ x))))
      P.≃-refl X b p)
    P.≃-refl

-- Short original odd normal form: the right-hand prefix is B_n
-- directly. This is equivalent to the Section32 formulation
-- B_(n+1)-last_b_n by the literal SeriesOf successor equation.
originalOddShort : R.ℝ → Nat → Set
originalOddShort X n =
  R._≃_
    (O.originalOddFinite X (suc n))
    (R._+_
      (R._+_
        R.1ℝ
        (R._*_ (R._*_ C.two X) (G.bPrefix X n)))
      (R._*_ (R._*_ X X)
        (T.originalBLowTriangle X (suc n))))

-- This explicit source theorem is the exact simple endpoint:
-- oddPart 0 = 1 and the original B prefix of count 0 vanishes.
originalOddShortZero : ∀ X → originalOddShort X zero
originalOddShortZero X =
  let open P.ℝ-Solver
  in solve 1
    (λ x →
      Κ 1ℚᵘ ⊜
      ((Κ 1ℚᵘ ⊕ ((Κ (+ 2 / 1) ⊗ x) ⊗ Κ 0ℚᵘ))
        ⊕ ((x ⊗ x) ⊗ Κ 0ℚᵘ)))
    P.≃-refl X

-- A source row in c=2 is the original coefficient 2*b0,
-- not the all-degree interior convolution.
originalOddShortOne : ∀ X → originalOddShort X (suc zero)
originalOddShortOne X =
  P.≃-trans
    (P.+-cong (originalOddShortZero X) (originalOddFirstTerm X))
    (let
      b = W.bTerm X zero
      open P.ℝ-Solver
     in solve 2
       (λ x b →
         ((Κ 1ℚᵘ ⊕ ((Κ (+ 2 / 1) ⊗ x) ⊗ Κ 0ℚᵘ))
            ⊕ ((x ⊗ x) ⊗ Κ 0ℚᵘ))
          ⊕ ((Κ (+ 2 / 1) ⊗ x) ⊗ b)
         ⊜
         (Κ 1ℚᵘ ⊕ ((Κ (+ 2 / 1) ⊗ x) ⊗ b))
          ⊕ ((x ⊗ x) ⊗ Κ 0ℚᵘ))
       P.≃-refl X b)
