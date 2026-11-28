module DASHI.Moonshine.JInvariantBishopCM163HyperMajorantsExact where

-- SOURCE-WRITTEN, UNCOMPILED. The original unweighted factorial
-- recurrence gives the actual coefficient bound 0 <= h_k <= 1.
-- Compare its outer majorants against a fixed geometric ratio.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)
import Data.Rational.Unnormalised.Properties as QP
open import Relation.Nullary.Decidable.Core using (from-yes)
open import Data.Product.Base using (_,_; _×_; proj₁; proj₂)
import Real as R
open R using (ℝ; _≃_; _≤_; _<_; _*_; _+_; _⋆; ∣_∣)
import RealProperties as P
import Sequence as S
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NR
import DASHI.Foundations.BishopChudnovskyNativeFactorialEulerAttachmentExact as A
import DASHI.Analysis.BishopPolynomialGeometricSeriesConvergenceExact as Poly
import DASHI.Moonshine.JInvariantBishopCM163RadiusGuardExact as RG
import DASHI.Moonshine.JInvariantBishopCM163ReciprocalEvaluationExact as Z
import DASHI.Moonshine.JInvariantBishopCM163LiteralNormBudgetExact as B
import DASHI.Moonshine.JInvariantBishopCM163LiteralRealSliceEvaluationExact as Slice
import DASHI.Moonshine.JInvariantBishopCM163FormalEvaluationConsumerExact as V
import DASHI.Moonshine.JInvariantBishopCM163NativeJetReductionExact as End
import DASHI.Moonshine.JInvariantBishopHyperQCoefficientUniquenessExact as U
import DASHI.Moonshine.JInvariantBishopHyperQOriginalCoefficientsExact as H
import DASHI.Moonshine.JInvariantBishopHyperQFactorizationWeldExact as F
import DASHI.Moonshine.JInvariantBishopWeightedCauchyEvaluationExact as W
import DASHI.Moonshine.JInvariantBishopWeightedPowerLimitExact as Power
import DASHI.Foundations.BishopChudnovskyRawCoordinateWeldExact as Raw
import DASHI.Moonshine.JInvariantBishopLiteralRamanujanExact as Literal

cancelOrder : (v : ℝ) → R.Positive v → {x y : ℝ} →
  v * x ≤ v * y → x ≤ y
cancelOrder v p h = P.≮⇒≥ (λ y<x →
  P.<-irrefl P.≃-refl (P.<-≤-trans (P.*-monoˡ-<-pos p y<x) h))

lead : Nat → ℝ
lead n = R.pow (NR.natReal (suc n)) 3

factor : Nat → ℝ
factor n = (NR.natReal n + ((+ 1 / 6) ⋆)) *
  (NR.natReal n + ((+ 1 / 2) ⋆)) * (NR.natReal n + ((+ 5 / 6) ⋆))

leadPos : (n : Nat) → R.Positive (lead n)
leadPos n =
  let p = P.posp⇒posp⋆ (+ (suc n) / 1) (QP.positive⁻¹ (+ (suc n) / 1))
  in P.posx,y⇒posx*y
    (P.posx,y⇒posx*y (P.posx,y⇒posx*y
      (P.posp⇒posp⋆ 1ℚᵘ (QP.positive⁻¹ 1ℚᵘ)) p) p) p

oneSixNN : R.NonNegative ((+ 1 / 6) ⋆)
oneSixNN = RG.ratNN (+ 1 / 6) (from-yes (0ℚᵘ QP.≤? (+ 1 / 6)))

factorNN : (n : Nat) → R.NonNegative (factor n)
factorNN n = P.nonNegx,y⇒nonNegx*y
  (P.nonNegx,y⇒nonNegx*y
    (P.nonNegx,y⇒nonNegx+y (Poly.natRealNonnegative n) oneSixNN)
    (P.nonNegx,y⇒nonNegx+y (Poly.natRealNonnegative n)
      (RG.ratNN (+ 1 / 2) (from-yes (0ℚᵘ QP.≤? (+ 1 / 2))))))
  (P.nonNegx,y⇒nonNegx+y (Poly.natRealNonnegative n)
    (RG.ratNN (+ 5 / 6) (from-yes (0ℚᵘ QP.≤? (+ 5 / 6)))))

factorLE : (n : Nat) → factor n ≤ lead n
factorLE n =
  let
    x = NR.natReal n
    y = NR.natReal (suc n)
    a = x + ((+ 1 / 6) ⋆)
    b = x + ((+ 1 / 2) ⋆)
    c = x + ((+ 5 / 6) ⋆)
    aLE = P.≤-respʳ-≃ (P.≃-symm (NR.natRealSuccessor n))
      (P.+-monoʳ-≤ x (RG.ratLe (+ 1 / 6) 1ℚᵘ (from-yes ((+ 1 / 6) QP.≤? 1ℚᵘ))))
    bLE = P.≤-respʳ-≃ (P.≃-symm (NR.natRealSuccessor n))
      (P.+-monoʳ-≤ x (RG.ratLe (+ 1 / 2) 1ℚᵘ (from-yes ((+ 1 / 2) QP.≤? 1ℚᵘ))))
    cLE = P.≤-respʳ-≃ (P.≃-symm (NR.natRealSuccessor n))
      (P.+-monoʳ-≤ x (RG.ratLe (+ 5 / 6) 1ℚᵘ (from-yes ((+ 5 / 6) QP.≤? 1ℚᵘ))))
    bNN = P.nonNegx,y⇒nonNegx+y (Poly.natRealNonnegative n)
      (RG.ratNN (+ 1 / 2) (from-yes (0ℚᵘ QP.≤? (+ 1 / 2))))
    cNN = P.nonNegx,y⇒nonNegx+y (Poly.natRealNonnegative n)
      (RG.ratNN (+ 5 / 6) (from-yes (0ℚᵘ QP.≤? (+ 5 / 6))))
    yNN = Poly.natRealNonnegative (suc n)
    pairLE = P.≤-trans (P.*-monoʳ-≤-nonNeg aLE bNN)
      (P.*-monoˡ-≤-nonNeg bLE yNN)
  in P.≤-respʳ-≃
    (let open P.ℝ-Solver in solve 1 (λ y → y ⊗ y ⊗ y ⊜ ((Κ 1ℚᵘ ⊗ y) ⊗ y) ⊗ y)
      P.≃-refl y)
    (P.≤-trans (P.*-monoʳ-≤-nonNeg pairLE cNN)
      (P.*-monoˡ-≤-nonNeg cLE (P.nonNegx,y⇒nonNegx*y yNN yNN)))

clearedStep : (n : Nat) → lead n * H.hyperCoeff (suc n) ≃
  factor n * H.hyperCoeff n
clearedStep n = P.≃-trans (H.unweightedODE n)
  (let open P.ℝ-Solver in solve 2 (λ x h →
    (((Κ 1ℚᵘ ⊗ x) ⊗ x) ⊗ x) ⊗ h ⊕
    Κ (+ 3 / 2) ⊗ (((Κ 1ℚᵘ ⊗ x) ⊗ x) ⊗ h) ⊕
    Κ (+ 23 / 36) ⊗ ((Κ 1ℚᵘ ⊗ x) ⊗ h) ⊕ Κ (+ 5 / 72) ⊗ (Κ 1ℚᵘ ⊗ h)
    ⊜ (x ⊕ Κ (+ 1 / 6)) ⊗ (x ⊕ Κ (+ 1 / 2)) ⊗ (x ⊕ Κ (+ 5 / 6)) ⊗ h)
    P.≃-refl (NR.natReal n) (H.hyperCoeff n))

coeffBand : (n : Nat) → (R.0ℝ ≤ H.hyperCoeff n) × (H.hyperCoeff n ≤ R.1ℝ)
coeffBand zero = P.≤-respʳ-≃ (P.≃-symm (P.*-identityˡ (A.hTerm zero)))
  (P.nonNegx⇒0≤x Power.oneNN) ,
  P.≤-reflexive (P.*-identityˡ (A.hTerm zero))
coeffBand (suc n) =
  let h0 , h1 = coeffBand n
      l = lead n
      f = factor n
      h = H.hyperCoeff n
      step = clearedStep n
      lo = P.≤-respˡ-≃ (P.≃-symm (P.*-zeroʳ l))
        (P.≤-respʳ-≃ (P.≃-symm step)
          (P.nonNegx⇒0≤x (P.nonNegx,y⇒nonNegx*y (factorNN n) (P.0≤x⇒nonNegx h0))))
      hi = P.≤-respˡ-≃ (P.≃-symm step)
        (P.≤-respʳ-≃ (P.≃-symm (P.*-identityʳ l))
          (P.≤-trans
            (P.≤-respʳ-≃ (P.*-identityʳ f) (P.*-monoˡ-≤-nonNeg h1 (factorNN n)))
            (factorLE n)))
  in cancelOrder l (leadPos n) lo , cancelOrder l (leadPos n) hi

coeffAbsBound : (n : Nat) → ∣ H.hyperCoeff n ∣ ≤ R.1ℝ
coeffAbsBound n = P.≤-respˡ-≃
  (P.≃-symm (P.nonNegx⇒∣x∣≃x (P.0≤x⇒nonNegx (proj₁ (coeffBand n)))))
  (proj₂ (coeffBand n))

jetAbsBound : (n : Nat) → ∣ H.hyperJetCoeff n ∣ ≤ NR.natReal n
jetAbsBound n =
  P.≤-respˡ-≃
    (P.≃-symm (P.≃-trans (P.∣x*y∣≃∣x∣*∣y∣ (NR.natReal n) (H.hyperCoeff n))
      (P.*-congʳ (P.nonNegx⇒∣x∣≃x (Poly.natRealNonnegative n)))))
    (P.≤-respʳ-≃ (P.*-identityʳ (NR.natReal n))
      (P.*-monoˡ-≤-nonNeg (coeffAbsBound n) (Poly.natRealNonnegative n)))

ratio : ℝ
ratio = (+ 1 / 3) ⋆
ratioNN : R.NonNegative ratio
ratioNN = RG.ratNN (+ 1 / 3) (from-yes (0ℚᵘ QP.≤? (+ 1 / 3)))
ratioSmall : ratio < R.1ℝ
ratioSmall = RG.ratLt (+ 1 / 3) 1ℚᵘ (from-yes ((+ 1 / 3) QP.<? 1ℚᵘ))

zPowBound : (n : Nat) → R.pow (proj₁ (B.witness Z.zBound)) n ≤ R.pow ratio n
zPowBound = Z.powMono (proj₁ (B.witness Z.zBound)) ratio
  (Power.absNormNN (W.weighted V.q H.Zcoord) (B.witness Z.zBound))
  ratioNN (P.<⇒≤ Z.zNormSmall)

module AtRoot (root : End.CMRoot) where
  module C = V.AtOriginalZ (B.witness Z.zBound) (Z.zFromRoot root)

  hMajorantBound : (n : Nat) → C.HA.m n ≤ R.pow ratio n
  hMajorantBound n = P.≤-respʳ-≃ (P.*-identityˡ (R.pow ratio n))
    (P.≤-trans
      (P.*-monoʳ-≤-nonNeg (coeffAbsBound n)
        (S.nonNegx⇒nonNegxⁿ n (Power.absNormNN (W.weighted V.q H.Zcoord) (B.witness Z.zBound))))
      (P.*-monoˡ-≤-nonNeg (zPowBound n) Power.oneNN))

  jMajorantBound : (n : Nat) → C.JA.m n ≤ Poly.polynomialGeometricTerm ratio 1 n
  jMajorantBound n = P.≤-respʳ-≃
    (P.*-congʳ (P.≃-symm (P.*-identityˡ (NR.natReal n))))
    (P.≤-trans
      (P.*-monoʳ-≤-nonNeg (jetAbsBound n)
        (S.nonNegx⇒nonNegxⁿ n (Power.absNormNN (W.weighted V.q H.Zcoord) (B.witness Z.zBound))))
      (P.*-monoˡ-≤-nonNeg (zPowBound n) (Poly.natRealNonnegative n)))

  hMajorant : S._isConvergent (S.SeriesOf C.HA.m)
  hMajorant = S.proposition-3-5
    (S.geometric-series-isConvergent
      (P.<-respˡ-≃ (P.≃-symm (P.nonNegx⇒∣x∣≃x ratioNN)) ratioSmall))
    (zero , λ n _ → P.≤-respˡ-≃
      (P.≃-symm (P.nonNegx⇒∣x∣≃x (C.HA.mNN n))) (hMajorantBound n))

  jMajorant : S._isConvergent (S.SeriesOf C.JA.m)
  jMajorant = S.proposition-3-5
    (Poly.polynomialGeometricSeriesConvergent ratio 1
      (P.nonNegx⇒0≤x ratioNN) ratioSmall)
    (zero , λ n _ → P.≤-respˡ-≃
      (P.≃-symm (P.nonNegx⇒∣x∣≃x (C.JA.mNN n))) (jMajorantBound n))

  module Consumer = C.WithMajorants hMajorant jMajorant

  dxBound : B.Bounded Slice.dx (proj₁ Slice.dxAbs)
  dxBound = B.bounded Slice.dxAbs P.≤-refl

  uAbs : V.Abs Consumer.uSeries
  uAbs = B.normCong
    (λ n → let open P.ℝ-Solver in solve 1
      (λ d → d ⊕ d ⊕ d ⊜ Κ (+ 3 / 1) ⊗ d) P.≃-refl (Slice.dx n))
    (B.witness (B.addBound (B.addBound dxBound dxBound) dxBound))

  rawFromArithmeticAndCM : F.RamanujanX → F.RamanujanY → F.RamanujanE →
    End.SignedJet → (k : Nat) → Raw.RawCross k
  rawFromArithmeticAndCM hx hy he jet =
    Consumer.actualRaw hx hy he Slice.xAbs Slice.yAbs uAbs
      Slice.xEval Slice.yEval Slice.uEval root jet

  -- The arithmetic producer is now internal; only the CM root and signed jet remain.
  rawFromCM : End.SignedJet → (k : Nat) → Raw.RawCross k
  rawFromCM = rawFromArithmeticAndCM Literal.ramanujanX Literal.ramanujanY Literal.ramanujanE
