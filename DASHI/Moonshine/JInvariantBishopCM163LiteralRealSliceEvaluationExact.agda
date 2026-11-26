module DASHI.Moonshine.JInvariantBishopCM163LiteralRealSliceEvaluationExact where

-- SOURCE-WRITTEN, UNCOMPILED. Literal real slice of original complex
-- coefficients. Retain E6 sign, normalized head, Euler zero mode.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (s≤s)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
open import Data.Product.Base using (_,_; proj₁; proj₂)
import Real as R
open R using (ℝ; _≃_; _*_; _+_; _-_; _⋆; ∣_∣)
import RealProperties as P
import Sequence as S
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as Ext
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NR
import DASHI.Moonshine.JInvariantEisensteinBishopSetoidSeriesExact as E
import DASHI.Moonshine.JInvariantBishopUnitDiskEisensteinCompletionExact as Disk
import DASHI.Moonshine.JInvariantBishopEisensteinEulerJetExact as J
import DASHI.Moonshine.JInvariantBishopCM163SelectedDiskExact as CM
import DASHI.Moonshine.JInvariantBishopCM163TailGuardExact as Guard
import DASHI.Moonshine.JInvariantBishopCM163NativeJetReductionExact as End
import DASHI.Moonshine.JInvariantBishopHyperQCoefficientUniquenessExact as U
import DASHI.Moonshine.JInvariantBishopHyperQOriginalCoefficientsExact as H
import DASHI.Moonshine.JInvariantBishopWeightedCauchyEvaluationExact as W
import DASHI.Moonshine.JInvariantBishopCM163FormalEvaluationConsumerExact as V
open U using (Series; _⊖s_; scale)
open V using (q; Abs; Eval)

shift : Series → Series
shift f n = f (suc n)

prependPrefix : (f : Series) (n : Nat) →
  S.SeriesOf f (suc n) ≃ f zero + S.SeriesOf (shift f) n
prependPrefix f zero = P.≃-trans (P.+-identityˡ (f zero))
  (P.≃-symm (P.+-identityʳ (f zero)))
prependPrefix f (suc n) =
  P.≃-trans (P.+-cong (prependPrefix f n) P.≃-refl)
    (P.+-assoc (f zero) (S.SeriesOf (shift f) n) (f (suc n)))

prependDifference : (f : Series) (L : ℝ) (n : Nat) →
  (S.SeriesOf f (suc n) - (f zero + L)) ≃ (S.SeriesOf (shift f) n - L)
prependDifference f L n =
  P.≃-trans (P.+-congˡ (R.- (f zero + L)) (prependPrefix f n))
    (let open P.ℝ-Solver in
      solve 3 (λ a b l → (a ⊕ b) ⊖ (a ⊕ l) ⊜ b ⊖ l)
        P.≃-refl (f zero) (S.SeriesOf (shift f) n) L)

prependLimit : (f : Series) (L : ℝ) →
  S._ConvergesTo_ (S.SeriesOf (shift f)) L →
  S._ConvergesTo_ (S.SeriesOf f) (f zero + L)
prependLimit f L (S.con* h) = S.con* λ { (suc k) →
  let cut , bound = h (suc k) in
  suc cut , λ { (suc n) (s≤s hn) →
    P.≤-respˡ-≃ (P.≃-symm (P.∣-∣-cong (prependDifference f L n)))
      (bound n hn) } }

transport : (f g : Series) (L : ℝ) →
  (∀ n → f n ≃ g n) → S._ConvergesTo_ (S.SeriesOf g) L →
  S._ConvergesTo_ (S.SeriesOf f) L
transport f g L eq h =
  S.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ n {{_}} → Ext.seriesPartialSumsCongruent (λ k → P.≃-symm (eq k)) n)
    (L , h)

powRealPart : (n : Nat) → C.re (A.powC CM.q n) ≃ R.pow q n
powRealPart zero = P.≃-refl
powRealPart (suc n) =
  P.≃-trans (P.+-cong (P.*-congˡ (powRealPart n))
    (P.≃-trans (P.-‿cong (P.*-zeroˡ (C.im (A.powC CM.q n)))) (P.≃-symm P.0≃-0)))
    (P.≃-trans (P.+-identityʳ (q * R.pow q n)) (P.*-comm q (R.pow q n)))

xTail : (n : Nat) → W.weighted q U.X (suc n) ≃ Guard.t4 n
xTail n = P.≃-trans (P.*-comm (R.pow q (suc n)) (E.e4CoefficientReal n))
  (P.*-congˡ (P.≃-symm (powRealPart (suc n))))

yTail : (n : Nat) → W.weighted q U.Y (suc n) ≃ R.- (Guard.t6 n)
yTail n =
  P.≃-trans (let open P.ℝ-Solver in
    solve 2 (λ q a → q ⊗ (⊝ a) ⊜ ⊝ (a ⊗ q))
      P.≃-refl (R.pow q (suc n)) (E.e6CoefficientReal n))
    (P.-‿cong (P.*-congˡ (P.≃-symm (powRealPart (suc n)))))

xTailAbs : (n : Nat) → ∣ W.weighted q U.X (suc n) ∣ ≃ Guard.abs4 n
xTailAbs n = P.∣-∣-cong (xTail n)
yTailAbs : (n : Nat) → ∣ W.weighted q U.Y (suc n) ∣ ≃ Guard.abs6 n
yTailAbs n = P.≃-trans (P.∣-∣-cong (yTail n)) P.∣-x∣≃∣x∣

xAbs : Abs U.X
xAbs = ∣ W.weighted q U.X zero ∣ + Guard.l1X ,
  prependLimit (λ n → ∣ W.weighted q U.X n ∣) Guard.l1X
    (transport _ _ Guard.l1X xTailAbs (proj₂ Guard.abs4Cauchy))

yAbs : Abs U.Y
yAbs = ∣ W.weighted q U.Y zero ∣ + Guard.l1Y ,
  prependLimit (λ n → ∣ W.weighted q U.Y n ∣) Guard.l1Y
    (transport _ _ Guard.l1Y yTailAbs (proj₂ Guard.abs6Cauchy))

xEval : Eval U.X End.X
xEval = S.xₙ→x∧x≃y⇒xₙ→y
  (prependLimit (W.weighted q U.X) Guard.tail4
    (transport _ _ Guard.tail4 xTail
      (C.realConverges (Disk.e4Converges Guard.Actual.completion))))
  (P.+-cong (P.*-identityˡ R.1ℝ) P.≃-refl)

negPartial : (f : Series) (n : Nat) →
  S.SeriesOf (λ k → R.- (f k)) n ≃ R.- (S.SeriesOf f n)
negPartial f zero = P.0≃-0
negPartial f (suc n) =
  P.≃-trans (P.+-cong (negPartial f n) P.≃-refl)
    (let open P.ℝ-Solver in
      solve 2 (λ a b → (⊝ a) ⊕ (⊝ b) ⊜ ⊝ (a ⊕ b)) P.≃-refl
        (S.SeriesOf f n) (f n))

negLimit : (f : Series) (L : ℝ) → S._ConvergesTo_ (S.SeriesOf f) L →
  S._ConvergesTo_ (S.SeriesOf (λ k → R.- (f k))) (R.- L)
negLimit f L h =
  S.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀ (λ n {{_}} → P.≃-symm (negPartial f n))
    (R.- L , S.-xₙ→-x₀ (L , h))

yEval : Eval U.Y End.Y
yEval = S.xₙ→x∧x≃y⇒xₙ→y
  (prependLimit (W.weighted q U.Y) (R.- Guard.tail6)
    (transport _ _ (R.- Guard.tail6) yTail
      (negLimit Guard.t6 Guard.tail6
        (C.realConverges (Disk.e6Converges Guard.Actual.completion)))))
  (P.+-cong (P.*-identityˡ R.1ℝ) P.≃-refl)

tailZero : (f : Series) → f zero ≃ R.1ℝ →
  W.weighted q (f ⊖s H.unitSeries) zero ≃ R.0ℝ
tailZero f h = U.right0 (P.≃-trans (P.+-cong h P.≃-refl) (P.+-inverseʳ R.1ℝ))

tailSame : (f : Series) (n : Nat) →
  W.weighted q (f ⊖s H.unitSeries) (suc n) ≃ W.weighted q f (suc n)
tailSame f n = P.*-congˡ (P.≃-trans (P.+-cong P.≃-refl (P.≃-symm P.0≃-0))
  (P.+-identityʳ (f (suc n))))

tailNorm : (f : Series) → f zero ≃ R.1ℝ →
  (L : ℝ) → S._ConvergesTo_ (S.SeriesOf (λ n → ∣ W.weighted q f (suc n) ∣)) L →
  S._ConvergesTo_ (S.SeriesOf (λ n → ∣ W.weighted q (f ⊖s H.unitSeries) n ∣)) L
tailNorm f h L hL = S.xₙ→x∧x≃y⇒xₙ→y
  (prependLimit (λ n → ∣ W.weighted q (f ⊖s H.unitSeries) n ∣) L
    (transport _ _ L (λ n → P.∣-∣-cong (tailSame f n)) hL))
  (P.≃-trans (P.+-cong (P.≃-trans (P.∣-∣-cong (tailZero f h))
    (P.nonNegx⇒∣x∣≃x P.nonNeg0)) P.≃-refl) (P.+-identityˡ L))

xTailNorm : Abs (U.X ⊖s H.unitSeries)
xTailNorm = Guard.l1X , tailNorm U.X P.≃-refl Guard.l1X
  (transport _ _ Guard.l1X xTailAbs (proj₂ Guard.abs4Cauchy))
yTailNorm : Abs (U.Y ⊖s H.unitSeries)
yTailNorm = Guard.l1Y , tailNorm U.Y P.≃-refl Guard.l1Y
  (transport _ _ Guard.l1Y yTailAbs (proj₂ Guard.abs6Cauchy))

module Jet = J.AtDisk CM.input
dx : Series
dx = U.D 1 U.X

dxTail : (n : Nat) → W.weighted q dx (suc n) ≃ C.re (J.e4JetTerm CM.q 1 n)
dxTail n =
  P.≃-trans (let open P.ℝ-Solver in
    solve 3 (λ q n x → q ⊗ (n ⊗ x) ⊜ n ⊗ (q ⊗ x)) P.≃-refl
      (R.pow q (suc n)) (R.pow (NR.natReal (suc n)) 1) (U.X (suc n)))
    (P.*-congˡ (xTail n))

dxTailAbsolute : S.SeriesOf_ConvergesAbsolutely (λ n → C.re (J.e4JetTerm CM.q 1 n))
dxTailAbsolute = C.realAbsolute (Jet.e4JetAbsolute 1)

dxAbs : Abs dx
dxAbs = ∣ W.weighted q dx zero ∣ + proj₁ dxTailAbsolute ,
  prependLimit (λ n → ∣ W.weighted q dx n ∣) (proj₁ dxTailAbsolute)
    (transport _ _ (proj₁ dxTailAbsolute) (λ n → P.∣-∣-cong (dxTail n)) (proj₂ dxTailAbsolute))

dxEval : Eval dx (C.re (Jet.e4EulerJet 1))
dxEval = S.xₙ→x∧x≃y⇒xₙ→y
  (prependLimit (W.weighted q dx) (C.re (Jet.e4EulerJet 1))
    (transport _ _ (C.re (Jet.e4EulerJet 1)) dxTail
      (C.realConverges (Jet.e4JetConverges 1))))
  (P.≃-trans (P.+-cong (U.right0 (U.D0 U.X)) P.≃-refl)
    (P.+-identityˡ (C.re (Jet.e4EulerJet 1))))

uEval : Eval (scale ((+ 3 / 1) ⋆) dx) End.U
uEval = V.scaleEval ((+ 3 / 1) ⋆) dx (C.re (Jet.e4EulerJet 1)) dxEval
