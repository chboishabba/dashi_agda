module DASHI.Moonshine.JInvariantBishopCM163ReciprocalEvaluationExact where

-- SOURCE-WRITTEN, UNCOMPILED. Evaluate the literal geometric
-- reciprocal using the existing two-cut theorem and positive norm.
-- Use the actual formal inverse identity to recover the selected
-- Z value from CMRoot, without another analytic reciprocal.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
import Data.Integer.Base as Int
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)
import Data.Rational.Unnormalised.Properties as QP
open import Relation.Nullary.Decidable.Core using (from-yes)
open import Data.Product.Base using (_,_; proj₁; proj₂)
import Real as R
open R using (ℝ; _≃_; _≤_; _<_; _*_; _+_; _-_; _⋆; ∣_∣)
import RealProperties as P
import Sequence as S
import DASHI.Foundations.BishopChudnovskySignedPeriodNormalizationExact as N
import DASHI.Foundations.BishopChudnovskyNativeHyperODEExact as Hyper
import DASHI.Moonshine.JInvariantBishopCM163RadiusGuardExact as RG
import DASHI.Moonshine.JInvariantBishopCM163TailGuardExact as Guard
import DASHI.Moonshine.JInvariantBishopCM163NativeJetReductionExact as End
import DASHI.Moonshine.JInvariantBishopCM163FormalEvaluationConsumerExact as V
import DASHI.Moonshine.JInvariantBishopCM163LiteralRealSliceEvaluationExact as Slice
import DASHI.Moonshine.JInvariantBishopCM163LiteralNormBudgetExact as B
import DASHI.Moonshine.JInvariantBishopFormalGeometricInverseExact as I
import DASHI.Moonshine.JInvariantBishopHyperQOriginalCoefficientsExact as H
import DASHI.Moonshine.JInvariantBishopHyperQCoefficientUniquenessExact as U
import DASHI.Moonshine.JInvariantBishopWeightedCauchyEvaluationExact as W
import DASHI.Moonshine.JInvariantBishopWeightedPowerLimitExact as Power
import DASHI.Moonshine.JInvariantBishopCompositionLimitExact as CL
import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as Ext
open U using (Series; _⊗s_; _⊖s_)
open V using (q; Abs; Eval)
open B using (Bounded; bounded; witness; bound; T; discBudget)

powMono : (a b : ℝ) → R.NonNegative a → R.NonNegative b → a ≤ b →
  (n : Nat) → R.pow a n ≤ R.pow b n
powMono a b ha hb h zero = P.≤-refl
powMono a b ha hb h (suc n) =
  P.≤-trans (P.*-monoʳ-≤-nonNeg (powMono a b ha hb h n) ha)
    (P.*-monoˡ-≤-nonNeg h (S.nonNegx⇒nonNegxⁿ n hb))

tNN : R.NonNegative T
tNN = RG.ratNN (+ 1951 / 15625) (from-yes (0ℚᵘ QP.≤? (+ 1951 / 15625)))

tSmall : ∣ T ∣ < R.1ℝ
tSmall = P.<-respˡ-≃ (P.≃-symm (P.nonNegx⇒∣x∣≃x tNN))
  (RG.ratLt (+ 1951 / 15625) 1ℚᵘ (from-yes ((+ 1951 / 15625) QP.<? 1ℚᵘ)))

geoPrefix : (n : Nat) → S.SeriesOf (R.pow T) (suc n) ≃
  R.1ℝ + T * S.SeriesOf (R.pow T) n
geoPrefix zero = let open P.ℝ-Solver in
  solve 1 (λ t → Κ 0ℚᵘ ⊕ Κ 1ℚᵘ ⊜ Κ 1ℚᵘ ⊕ t ⊗ Κ 0ℚᵘ) P.≃-refl T
geoPrefix (suc n) =
  P.≃-trans (P.+-cong (geoPrefix n) P.≃-refl)
    (let open P.ℝ-Solver in
      solve 3 (λ t s p → (Κ 1ℚᵘ ⊕ t ⊗ s) ⊕ p ⊗ t ⊜ Κ 1ℚᵘ ⊕ t ⊗ (s ⊕ p))
        P.≃-refl T (S.SeriesOf (R.pow T) n) (R.pow T n))

reciprocalBudget : ℝ
reciprocalBudget = (+ 15625 / 13674) ⋆

geoBound : (n : Nat) → S.SeriesOf (R.pow T) n ≤ reciprocalBudget
geoBound zero = P.nonNegx⇒0≤x
  (RG.ratNN (+ 15625 / 13674) (from-yes (0ℚᵘ QP.≤? (+ 15625 / 13674))))
geoBound (suc n) =
  P.≤-respˡ-≃ (P.≃-symm (geoPrefix n))
    (P.≤-respʳ-≃ (let open P.ℝ-Solver in solve 0
      (Κ 1ℚᵘ ⊕ Κ (+ 1951 / 15625) ⊗ Κ (+ 15625 / 13674) ⊜ Κ (+ 15625 / 13674)) P.≃-refl)
      (P.+-monoʳ-≤ R.1ℝ (P.*-monoˡ-≤-nonNeg (geoBound n) tNN)))

module Inv = CL.At q (λ _ → R.1ℝ) H.minusX3Tail H.inverseInnerZero (witness B.innerBound)

majorantBound : (k : Nat) → Inv.m k ≤ R.pow T k
majorantBound k =
  P.≤-respˡ-≃ (P.≃-symm (P.≃-trans
    (P.*-congʳ (P.nonNegx⇒∣x∣≃x Power.oneNN))
    (P.*-identityˡ (R.pow Inv.B k))))
    (powMono Inv.B T (Power.absNormNN (W.weighted q H.minusX3Tail) (witness B.innerBound))
      tNN (bound B.innerBound) k)

majorantConv : S._isConvergent (S.SeriesOf Inv.m)
majorantConv = S.proposition-3-5 (S.geometric-series-isConvergent tSmall)
  (zero , λ k _ → P.≤-respˡ-≃ (P.≃-symm (P.nonNegx⇒∣x∣≃x (Inv.mNN k)))
    (majorantBound k))

majorantLimitBound : proj₁ majorantConv ≤ reciprocalBudget
majorantLimitBound = S.xₙ≤y⇒limxₙ≤y
  (λ n → P.≤-trans (S.∑₀-mono-≤ majorantBound n) (geoBound n)) majorantConv

inverseBound : Bounded H.inverseX3 reciprocalBudget
inverseBound = bounded (Inv.compositionAbsolute majorantConv)
  (P.≤-trans (Inv.compositionNormBound majorantConv) majorantLimitBound)

zBudget : ℝ
zBudget = (+ 1517 / 4558) ⋆

zBound : Bounded H.Zcoord zBudget
zBound = B.transport (λ n → P.≃-refl)
  (let open P.ℝ-Solver in solve 0
    (Κ (+ 4551 / 15625) ⊗ Κ (+ 15625 / 13674) ⊜ Κ (+ 1517 / 4558)) P.≃-refl)
  (B.mulBound B.discBound inverseBound)

zNormSmall : proj₁ (witness zBound) < ((+ 1 / 3) ⋆)
zNormSmall = P.≤-<-trans (bound zBound)
  (RG.ratLt (+ 1517 / 4558) (+ 1 / 3)
    (from-yes ((+ 1517 / 4558) QP.<? (+ 1 / 3))))

x2Abs : Abs U.X2
x2Abs = W.weightedProductAbsolute q U.X U.X Slice.xAbs Slice.xAbs
x3Abs : Abs U.X3
x3Abs = W.weightedProductAbsolute q U.X2 U.X x2Abs Slice.xAbs
x3Eval : Eval U.X3 (N.cube End.X)
x3Eval = W.weightedProductLimit q U.X2 U.X (End.X * End.X) End.X x2Abs Slice.xAbs
  (W.weightedProductLimit q U.X U.X End.X End.X Slice.xAbs Slice.xAbs Slice.xEval Slice.xEval)
  Slice.xEval

y2Eval : Eval U.Y2 (N.sq End.Y)
y2Eval = W.weightedProductLimit q U.Y U.Y End.Y End.Y Slice.yAbs Slice.yAbs Slice.yEval Slice.yEval

discEval : Eval U.disc (N.cube End.X - N.sq End.Y)
discEval =
  let negY = Slice.negLimit (W.weighted q U.Y2) (N.sq End.Y) y2Eval
      h = B.sumConv (W.weighted q U.X3) (λ n → R.- (W.weighted q U.Y2 n))
        (N.cube End.X , x3Eval) (R.- (N.sq End.Y) , negY)
      eq : (n : Nat) → W.weighted q U.disc n ≃
        (W.weighted q U.X3 n + R.- (W.weighted q U.Y2 n))
      eq n = let open P.ℝ-Solver in solve 3
        (λ r a b → r ⊗ (a ⊖ b) ⊜ r ⊗ a ⊖ r ⊗ b)
        P.≃-refl (R.pow q n) (U.X3 n) (U.Y2 n)
  in Slice.transport _ _ (N.cube End.X - N.sq End.Y) eq (proj₂ h)

zConverges : S._isConvergent (S.SeriesOf (W.weighted q H.Zcoord))
zConverges = S.absolute⇒isConvergent (witness zBound)

zValue : ℝ
zValue = proj₁ zConverges

zCleared : (N.cube End.X * zValue) ≃ (N.cube End.X - N.sq End.Y)
zCleared = V.sameEval (U.X3 ⊗s H.Zcoord) U.disc
  (N.cube End.X * zValue) (N.cube End.X - N.sq End.Y)
  I.actualZDenominator
  (W.weightedProductLimit q U.X3 H.Zcoord (N.cube End.X) zValue
    x3Abs (witness zBound) x3Eval (proj₂ zConverges)) discEval

zFromRoot : End.CMRoot → Eval H.Zcoord Hyper.z
zFromRoot root =
  let cubic = Guard.Root.rootToCubic root
      x = N.cube End.X
      xPos = P.posx,y⇒posx*y (P.posx,y⇒posx*y Guard.xPositive Guard.xPositive) Guard.xPositive
      target : (x - N.sq End.Y) ≃ (x * Hyper.z)
      target = P.≃-trans (P.+-cong P.≃-refl (P.-‿cong cubic))
        (let open P.ℝ-Solver in solve 1
          (λ x → x ⊖ Κ (+ 262537412640769728 / 262537412640768000) ⊗ x
            ⊜ x ⊗ Κ (Int.-_ (+ 1728) / 262537412640768000)) P.≃-refl x)
  in S.xₙ→x∧x≃y⇒xₙ→y (proj₂ zConverges)
    (N.cancelLeft x xPos (P.≃-trans zCleared target))
