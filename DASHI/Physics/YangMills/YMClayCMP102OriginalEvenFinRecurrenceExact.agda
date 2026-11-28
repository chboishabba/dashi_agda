module DASHI.Physics.YangMills.YMClayCMP102OriginalEvenFinRecurrenceExact where

------------------------------------------------------------------------
-- Original even-part finite row, all count by induction.
--
-- The original coefficient identity is:
--   evenPart 0 = 2 a0
--   evenPart (suc n) = 2 a_(suc n) + Cauchy(a,a)n.
-- Original finite SeriesOf scale and triangle successor are PAID.
-- The sole remaining algebraic donor is the weighted Cauchy power
-- identity (no factorial parity or analytic convergence).
--
-- This file proves the full even finite row for ALL n conditional
-- only on that explicit source-weight Cauchy identity. No postulate.
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

-- Explicit original coefficient-level Cauchy power identity.
-- All that is needed is the actual Cauchy product of coefficient
-- sequences at a fixed degree multiplied by the actual X^(n+1).
EvenWeightedCauchy : R.ℝ → Set
EvenWeightedCauchy X =
  ∀ n → R._≃_
    (R._*_ (Row.cauchyCoefficient C.aCoefficient C.aCoefficient n)
            (R.pow X (suc n)))
    (R._*_ X
      (Row.cauchyCoefficient (W.aTerm X) (W.aTerm X) n))

-- This theorem is a strict one-step all-source finite row weld.
-- Its proof is the original Cauchy power identity and Bishop solver;
-- no separate prefix construction or abstract result type.
originalEvenStep :
  ∀ X n → EvenWeightedCauchy X →
  R._≃_
    (O.originalEvenAt X (suc n))
    (R._+_
      (R._*_ C.two (W.aTerm X (suc n)))
      (R._*_ X
        (Row.cauchyCoefficient (W.aTerm X) (W.aTerm X) n)))
originalEvenStep X n weighted =
  let
    a = C.aCoefficient (suc n)
    p = R.pow X (suc n)
    q = Row.cauchyCoefficient C.aCoefficient C.aCoefficient n
    s = Row.cauchyCoefficient (W.aTerm X) (W.aTerm X) n
    open P.ℝ-Solver
  in
  P.≃-trans
    (solve 3
      (λ a q p →
        ((Κ (+ 2 / 1) ⊗ a) ⊕ q) ⊗ p
        ⊜ ((Κ (+ 2 / 1) ⊗ (a ⊗ p)) ⊕ (q ⊗ p)))
      P.≃-refl a q p)
    (P.+-cong P.≃-refl (weighted n))

-- For every original even finite row the only remaining proof
-- producer is the weighted Cauchy identity above. The induction
-- uses true SeriesOf (count, not inclusive) and FinSum triangle.
originalEvenRowFromWeightedCauchy :
  ∀ X n → EvenWeightedCauchy X → O.originalEvenFinRow X n
originalEvenRowFromWeightedCauchy X zero weighted =
  let open P.ℝ-Solver
  in solve 1
      (λ a → (Κ (+ 2 / 1) ⊗ a) ⊜
        (Κ (+ 2 / 1) ⊗ a) ⊕ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ))
      P.≃-refl (C.aCoefficient zero)
originalEvenRowFromWeightedCauchy X (suc n) weighted =
  let
    A = G.aPrefix X (suc n)
    a = W.aTerm X (suc n)
    tri = T.originalALowTriangle X (suc n)
    q = Row.cauchyCoefficient (W.aTerm X) (W.aTerm X) n
    open P.ℝ-Solver
  in
  P.≃-trans
    (P.+-cong
      (originalEvenRowFromWeightedCauchy X n weighted)
      (originalEvenStep X n weighted))
    (P.≃-trans
      (solve 4
        (λ A a tri q →
          ((Κ (+ 2 / 1) ⊗ A) ⊕ (X ⊗ tri))
            ⊕ ((Κ (+ 2 / 1) ⊗ a) ⊕ (X ⊗ q))
          ⊜
          (Κ (+ 2 / 1) ⊗ (A ⊕ a))
            ⊕ (X ⊗ (tri ⊕ q)))
        P.≃-refl A a tri q)
      (P.+-cong
        (P.*-congˡ P.≃-refl)
        (P.*-congˡ (FinSum.finSumSuccessor
          (Row.cauchyCoefficient (W.aTerm X) (W.aTerm X)) n))))
