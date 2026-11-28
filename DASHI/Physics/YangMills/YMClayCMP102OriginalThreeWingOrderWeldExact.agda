module DASHI.Physics.YangMills.YMClayCMP102OriginalThreeWingOrderWeldExact where

------------------------------------------------------------------------
-- ORIGINAL CMP102 finite tail: THE THREE actual signed physical
-- source pieces, with their correct c=suc n A/B triangle cutoffs.
--
-- Coarse solve: each component ≤ quarter^(suc n) in Bishop absolute
-- order, therefore their exact signed sum ≤ 3*quarter^(suc n).
-- This is the true original scalar geometric rate, not a fictional
-- limit or a substitute positive formal series. It is a complete
-- native theorem body conditional on three PRECISE source order
-- obligations; the latter still require the factorial-support
-- monomial / shifted positive Cauchy tail proof.
--
-- All n, all signed original represented Bishop X. No postulates.
-- Native Agda 2.9 typecheck still required.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Integer.Base as Z using (+_; +≤+)
open import Data.Nat.Base using (z≤n)
open import Data.Rational.Unnormalised as Q using (0ℚᵘ; 1ℚᵘ; _/_; *≤*)
import Real as R
import RealProperties as P
import Sequence as Seq

import DASHI.Physics.YangMills.YMClayCMP102OriginalFiniteTailGeometryExact as Tail
import DASHI.Physics.YangMills.YMClayCMP102OriginalShiftedWingOrderExact as Wing
import DASHI.Physics.YangMills.YMClayCMP102OriginalGeometricSqueezeReceiverExact as Rate
import DASHI.Physics.YangMills.YMClayCMP102OriginalFiniteTailToLimitExact as Limit
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as Half

-- Every source term here is the LITERAL original A/B shifted Cauchy
-- wing, with the omitted last B source term preserved separately.
OriginalThreeWingOrder : R.ℝ → Set
OriginalThreeWingOrder X =
  ∀ n →
    (R._≤_
      (R.∣ R.- (R._*_ X
        (Tail.originalAWing X (suc n))) ∣)
      (R.pow Half.bishopQuarter (suc n)))
    ×
    (R._≤_
      (R.∣ Tail.originalOmittedLinearB X n ∣)
      (R.pow Half.bishopQuarter (suc n)))
    ×
    (R._≤_
      (R.∣ R._*_
        (R._*_ X X) (Tail.originalBWing X (suc n)) ∣)
      (R.pow Half.bishopQuarter (suc n)))

originalThreeNonnegative : R.NonNegative Rate.three
originalThreeNonnegative =
  P.0≤x⇒nonNegx
    (P.p≤q⇒p⋆≤q⋆
      0ℚᵘ (+ 3 / 1)
      (Q.*≤* (Z.+≤+ z≤n)))

originalRateNonnegative : ∀ n →
  R.NonNegative (Rate.originalGeometricRate n)
originalRateNonnegative n =
  P.nonNegx,y⇒nonNegx*y
    originalThreeNonnegative
    (Seq.nonNegx⇒nonNegxⁿ n Rate.quarterNonnegative)

-- The complete native three-wing inequality, with no hidden
-- assumption that original G_count=0 or that positivity of a
-- polynomial automatically transfers to signed Bishop order.
originalPositiveTailFromThreeActualWings :
  ∀ X → OriginalThreeWingOrder X →
  Limit.OriginalPositiveTailOrder X
originalPositiveTailFromThreeActualWings X wing n =
  let
    qn = R.pow Half.bishopQuarter (suc n)
    A = R.- (R._*_ X (Tail.originalAWing X (suc n)))
    B = Tail.originalOmittedLinearB X n
    C = R._*_ (R._*_ X X) (Tail.originalBWing X (suc n))
    hA = (wing n).proj₁
    hB = (wing n).proj₂.proj₁
    hC = (wing n).proj₂.proj₂
    hSum = P.≤-trans
      (Wing.originalSignedCauchyTailTriangleBound X n)
      (P.+-mono-≤
        (P.+-mono-≤ hA hB)
        hC)
    hThree : R._≃_
      (R._+_ (R._+_ qn qn) qn)
      (Rate.originalGeometricRate (suc n))
    hThree =
      let open P.ℝ-Solver
      in solve 1
        (λ q → (q ⊕ q) ⊕ q ⊜ Κ (+ 3 / 1) ⊗ q)
        P.≃-refl qn
  in
  P.≤-respʳ-≃
    (P.≃-symm
      (P.nonNegx⇒∣x∣≃x
        (originalRateNonnegative (suc n))))
    (P.≤-respʳ-≃ hThree hSum)

-- The SAME original represented analytic function inherits the
-- scalar zero from the physical three-wing estimates plus the
-- exceptional original count-zero source order.
originalGZeroFromThreeActualWings :
  ∀ X (inside : R._≤_ (R.∣ X ∣) Half.bishopQuarter) →
  Limit.OriginalZeroCountOrder X →
  OriginalThreeWingOrder X →
  R._≃_ (Limit.Original.originalG X inside) R.0ℝ
originalGZeroFromThreeActualWings X inside hzero hwing =
  Limit.originalGZeroFromActualFiniteTailOrder
    X inside hzero
    (originalPositiveTailFromThreeActualWings X hwing)
