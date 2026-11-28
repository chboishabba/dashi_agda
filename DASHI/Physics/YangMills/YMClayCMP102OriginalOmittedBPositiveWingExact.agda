module DASHI.Physics.YangMills.YMClayCMP102OriginalOmittedBPositiveWingExact where

------------------------------------------------------------------------
-- Section39 ORIGINAL CMP102: full B LAST-ENDPOINT wing majorant.
--
-- Previously the actual source only supplied 2*b_n <= 1/3.
-- Now pay its true signed Bishop absolute-power transport and the
-- ORIGINAL quarter-radius inside premise. This is the omitted
-- row 2 X b_n X^n at c=suc n, NOT a newly chosen series.
--
-- This pays the MIDDLE of the THREE original positive wing leaves
-- at every signed X, including X=0, c=1.
-- Original A (c-1) and B (c-2) Cauchy wings remain separate.
-- Native pinned Agda 2.9 elaboration and --safe audit PENDING.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Integer.Base as Z using (+_; +≤+)
open import Data.Nat.Base using (z≤n; s≤s)
open import Data.Rational.Unnormalised as Q using (0ℚᵘ; 1ℚᵘ; _/_; *≤*)
import Real as R
import RealProperties as P
import Sequence as Seq
import DASHI.Physics.YangMills.BalabanCMP109BishopRootFreeSeriesExact as CMP109
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as Half
import DASHI.Physics.YangMills.YMClayCMP102OriginalEndpointCauchyShiftExact as CMP102
import DASHI.Physics.YangMills.YMClayCMP102OriginalFiniteTailGeometryExact as Tail
import DASHI.Physics.YangMills.YMClayCMP102OriginalLastBCoefficientCeilingExact as Last

originalThirdBelowOne :
  R._≤_ (R._⋆ (+ 1 / 3)) R.1ℝ
originalThirdBelowOne =
  P.p≤q⇒p⋆≤q⋆ (+ 1 / 3) 1ℚᵘ
    (Q.*≤* (Z.+≤+ (s≤s z≤n)))

originalLastBNonnegative : ∀ n →
  R.NonNegative
    (R._*_ CMP102.two (CMP102.bCoefficient n))
originalLastBNonnegative n =
  P.nonNegx,y⇒nonNegx*y
    Last.originalTwoNonnegative
    (CMP109.bNN n)

-- Actual signed original coefficient/monomial factorization.
-- There is no sign assumption on X: the modulus and native
-- |X^n|=|X|^n theorem are applied BEFORE coefficient order.
originalOmittedBAbsoluteFactor :
  ∀ X n →
  R._≃_
    (R.∣ Tail.originalOmittedLinearB X n ∣)
    (R._*_
      (R._*_ CMP102.two (CMP102.bCoefficient n))
      (R.pow (R.∣ X ∣) (suc n)))
originalOmittedBAbsoluteFactor X n =
  let
    two = CMP102.two
    b = CMP102.bCoefficient n
    p = R.pow X n
    v = R.∣ X ∣
    vp = R.pow v n
    open P.ℝ-Solver
  in
  P.≃-trans
    (P.∣x*y∣≃∣x∣*∣y∣
      (R._*_ two X)
      (R._*_ b p))
    (P.≃-trans
      (P.*-cong
        (P.∣x*y∣≃∣x∣*∣y∣ two X)
        (P.∣x*y∣≃∣x∣*∣y∣ b p))
      (P.≃-trans
        (P.*-cong
          (P.*-congʳ
            (P.nonNegx⇒∣x∣≃x Last.originalTwoNonnegative))
          (P.*-cong
            (P.nonNegx⇒∣x∣≃x (CMP109.bNN n))
            (Seq.∣xⁿ∣≃∣x∣ⁿ X n)))
        (solve 4
          (λ t b v p →
            (t ⊗ v) ⊗ (b ⊗ p)
              ⊜ (t ⊗ b) ⊗ (p ⊗ v))
          P.≃-refl two b v vp)))

-- The full original omitted B term, rather than its coefficient
-- alone, is now bounded by the exact original quarter^c
-- for EVERY c=suc n and every signed X in the original domain.
originalOmittedBQuarterWing :
  ∀ X →
  R._≤_ (R.∣ X ∣) Half.bishopQuarter →
  ∀ n →
  R._≤_
    (R.∣ Tail.originalOmittedLinearB X n ∣)
    (R.pow Half.bishopQuarter (suc n))
originalOmittedBQuarterWing X inside n =
  let
    degree = suc n
    power = R.pow (R.∣ X ∣) degree
    quarterPower = R.pow Half.bishopQuarter degree
    hpower =
      Seq.x≤y∧nonNegx⇒xⁿ≤yⁿ
        degree inside (P.nonNeg∣x∣ X)
    hscaled =
      P.*-mono-≤
        (originalLastBNonnegative n)
        (Seq.nonNegx⇒nonNegxⁿ degree (P.nonNeg∣x∣ X))
        (Last.originalTwiceBAtMostThird n)
        hpower
    hthird =
      P.≤-respʳ-≃
        (P.*-identityˡ quarterPower)
        (P.*-monoʳ-≤-nonNeg
          originalThirdBelowOne
          (Seq.nonNegx⇒nonNegxⁿ
            degree
            (P.0≤x⇒nonNegx
              (P.≤-trans
                (P.nonNegx⇒0≤x (P.nonNeg∣x∣ X))
                inside))))
  in
  P.≤-respˡ-≃
    (P.≃-symm (originalOmittedBAbsoluteFactor X n))
    (P.≤-trans hscaled hthird)
