module DASHI.Analysis.BishopOriginalMachinCayleyConservedPhaseExact where

-- Normalized original phase, without an ODE uniqueness premise.
-- H(t) = exp(2 i A(t)) conj(N(t))/(1+t^2).
-- For y=x+h, E=exp(2 i (A(y)-A(x)))-1-2 i h d(x),
-- R = D(x) conj(N(y))-D(y) conj(N(x))+2 i h conj(N(y))
--   = 2 h^2 (1-i y).
-- Therefore H(y)-H(x) = exp(2 i A(x)) d(y)
--                       [ E conj(N(y)) + d(x) R ].
-- All source increments below are actual Bishop trig/atan values.
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as Q using (_/_)
import Data.Rational.Unnormalised.Properties as QP
open import Relation.Nullary.Decidable.Core using (from-yes)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
import Real as R
open R using (ℝ; _≃_; _≤_; _+_; _-_; _*_; _⋆; ∣_∣)
import RealProperties as P
import DASHI.Analysis.BishopOriginalMachinAtanSmallPhaseExact as S
open S using (Point; x; nn; inside; atan; d; denom; two; half;
  absNN; boundAdd; boundSub; boundMul; dNN; dUpper; dCancels)
import DASHI.Analysis.BishopSetoidComplexExact as C
open C using (_≈C_; _*C_; _+C_; _-C_)
import DASHI.Analysis.BishopMachinCayleyNativeProductFirstZeroExact as Native
import DASHI.Analysis.BishopImaginaryProductPythagoreanReuseExact as Product
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
import DASHI.Moonshine.BishopMachinSetoidComplexInstanceExact as Route
import DASHI.Foundations.BishopSquareNonnegativeExact as Sq

scale : ℝ → C.BishopComplex → C.BishopComplex
scale a z = C.complex (a * C.re z) (a * C.im z)

Nbar : ℝ → C.BishopComplex
Nbar x = C.complex (R.1ℝ - x * x) (R.- (two * x))

Box : C.BishopComplex → ℝ → Set
Box z b = (∣ C.re z ∣ ≤ b) × (∣ C.im z ∣ ≤ b)

boxCong : ∀ {z w b} → z ≈C w → Box w b → Box z b
boxCong h (r , i) = P.≤-respˡ-≃ (P.∣-∣-cong (C.reEquivalent h)) r ,
  P.≤-respˡ-≃ (P.∣-∣-cong (C.imEquivalent h)) i

boxAdd : ∀ {z w a b} → Box z a → Box w b → Box (z +C w) (a + b)
boxAdd (zr , zi) (wr , wi) = boundAdd zr wr , boundAdd zi wi

boxMul : ∀ {z w a b} → Box z a → Box w b → Box (z *C w) ((a * b) + (a * b))
boxMul (zr , zi) (wr , wi) =
  boundSub (boundMul zr wr) (boundMul zi wi) ,
  boundAdd (boundMul zr wi) (boundMul zi wr)

boxScale : ∀ {a b z} → R.NonNegative a → a ≤ R.1ℝ → Box z b → Box (scale a z) b
boxScale {a} {b} an a1 (zr , zi) =
  scaled zr , scaled zi
  where
  scaled : ∀ {v} → ∣ v ∣ ≤ b → ∣ (a * v) ∣ ≤ b
  scaled h = P.≤-respʳ-≃ (P.*-identityˡ b)
    (boundMul (P.≤-respˡ-≃ (absNN an) a1) h)

boxWeaken : ∀ {z a b} → a ≤ b → Box z a → Box z b
boxWeaken h (zr , zi) = P.≤-trans zr h , P.≤-trans zi h

boxBudgetCong : ∀ {z a b} → a ≃ b → Box z a → Box z b
boxBudgetCong h (zr , zi) = P.≤-respʳ-≃ h zr , P.≤-respʳ-≃ h zi

xOne : ∀ p → x p ≤ R.1ℝ
xOne p = P.≤-trans (inside p) S.half≤one

squareOne : ∀ p → x p * x p ≤ R.1ℝ
squareOne p = P.≤-respʳ-≃ (P.*-identityˡ R.1ℝ)
  (P.*-mono-≤ (nn p) (nn p) (xOne p) (xOne p))

nbarBox : ∀ p → Box (Nbar (x p)) two
nbarBox p =
  P.≤-respʳ-≃
    (let open P.ℝ-Solver in solve 0 (Κ Q.1ℚᵘ ⊕ Κ Q.1ℚᵘ ⊜ Κ (+ 2 / 1)) P.≃-refl)
    (boundSub (P.≤-reflexive (absNN (P.pos⇒nonNeg (P.0<x⇒posx One.onePositive))))
      (P.≤-respˡ-≃ (absNN (Sq.bishopSquareNonnegative (x p))) (squareOne p))) ,
  P.≤-respˡ-≃ (P.∣-x∣≃∣x∣ {x = two * x p})
    (P.≤-respʳ-≃ (P.*-identityʳ two)
      (boundMul (P.≤-reflexive (absNN S.twoNN))
        (P.≤-respˡ-≃ (absNN (nn p)) (xOne p))))
  where
  import DASHI.Foundations.BishopNegativeExponentialGlobalUnitIntervalExact as One

-- Two denominators cancel exactly.  This is the reverse direction of
-- the same weighted cross used in the real LOG proof.
clearDifference : ∀ p q a b →
  (d q * a - d p * b) ≃ ((d p * d q) * (denom (x p) * a - denom (x q) * b))
clearDifference p q a b =
  P.≃-symm
    (P.≃-trans
      (let open P.ℝ-Solver in solve 6
        (λ i j u v a b → (i ⊗ j) ⊗ (u ⊗ a ⊖ v ⊗ b) ⊜
          (u ⊗ i) ⊗ (j ⊗ a) ⊖ (v ⊗ j) ⊗ (i ⊗ b))
        P.≃-refl (d p) (d q) (denom (x p)) (denom (x q)) a b)
      (P.≃-trans
        (P.+-cong (P.*-congʳ (dCancels p)) (P.-‿cong (P.*-congʳ (dCancels q))))
        (P.+-cong (P.*-identityˡ (d q * a)) (P.-‿cong (P.*-identityˡ (d p * b))))))

-- Native polynomial residual after the exact first-order cancellation.
residual : ℝ → ℝ → C.BishopComplex
residual x h = C.complex (two * (h * h)) (R.- ((two * (h * h)) * (x + h)))

crossReal : ∀ x h →
  (denom x * C.re (Nbar (x + h)) - denom (x + h) * C.re (Nbar x)
    - (two * h) * C.im (Nbar (x + h))) ≃ C.re (residual x h)
crossReal x h = let open P.ℝ-Solver in solve 2
  (λ x h → (Κ Q.1ℚᵘ ⊕ x ⊗ x) ⊗ (Κ Q.1ℚᵘ ⊖ (x ⊕ h) ⊗ (x ⊕ h))
    ⊖ (Κ Q.1ℚᵘ ⊕ (x ⊕ h) ⊗ (x ⊕ h)) ⊗ (Κ Q.1ℚᵘ ⊖ x ⊗ x)
    ⊖ (Κ (+ 2 / 1) ⊗ h) ⊗ (⊝ (Κ (+ 2 / 1) ⊗ (x ⊕ h)))
    ⊜ Κ (+ 2 / 1) ⊗ (h ⊗ h))
  P.≃-refl x h

crossImag : ∀ x h →
  (denom x * C.im (Nbar (x + h)) - denom (x + h) * C.im (Nbar x)
    + (two * h) * C.re (Nbar (x + h))) ≃ C.im (residual x h)
crossImag x h = let open P.ℝ-Solver in solve 2
  (λ x h → (Κ Q.1ℚᵘ ⊕ x ⊗ x) ⊗ (⊝ (Κ (+ 2 / 1) ⊗ (x ⊕ h)))
    ⊖ (Κ Q.1ℚᵘ ⊕ (x ⊕ h) ⊗ (x ⊕ h)) ⊗ (⊝ (Κ (+ 2 / 1) ⊗ x))
    ⊕ (Κ (+ 2 / 1) ⊗ h) ⊗ (Κ Q.1ℚᵘ ⊖ (x ⊕ h) ⊗ (x ⊕ h))
    ⊜ ⊝ ((Κ (+ 2 / 1) ⊗ (h ⊗ h)) ⊗ (x ⊕ h)))
  P.≃-refl x h

factorDifference : ∀ a b c d →
  (((a *C b) *C c) -C (a *C d)) ≈C (a *C ((b *C c) -C d))
factorDifference (C.complex a b) (C.complex c d) (C.complex e f) (C.complex g h) =
  C.complex-equivalent
    (let open P.ℝ-Solver in solve 8
      (λ a b c d e f g h →
        (((a ⊗ c ⊖ b ⊗ d) ⊗ e) ⊖ ((a ⊗ d ⊕ b ⊗ c) ⊗ f))
          ⊖ (a ⊗ g ⊖ b ⊗ h)
        ⊜ a ⊗ ((c ⊗ e ⊖ d ⊗ f) ⊖ g)
          ⊖ b ⊗ ((c ⊗ f ⊕ d ⊗ e) ⊖ h))
      P.≃-refl a b c d e f g h)
    (let open P.ℝ-Solver in solve 8
      (λ a b c d e f g h →
        (((a ⊗ c ⊖ b ⊗ d) ⊗ f) ⊕ ((a ⊗ d ⊕ b ⊗ c) ⊗ e))
          ⊖ (a ⊗ h ⊕ b ⊗ g)
        ⊜ a ⊗ ((c ⊗ f ⊕ d ⊗ e) ⊖ h)
          ⊕ b ⊗ ((c ⊗ e ⊖ d ⊗ f) ⊖ g))
      P.≃-refl a b c d e f g h)

module At (inputs : Round11.BishopCutset) where
  T = Route.machinTranscendentals inputs
  phase : Point → C.BishopComplex
  phase p = C.trigPair T (two * atan p)

  phaseBox : ∀ p → Box (phase p) R.1ℝ
  phaseBox p = Product.round11ModulusFromImaginaryProduct inputs
    (Native.originalNativeImaginaryExpProduct inputs) (two * atan p)

  H : Point → C.BishopComplex
  H p = phase p *C scale (d p) (Nbar (x p))

  module Step (p : Point) (h : ℝ) (hn : R.NonNegative h) (ht : h ≤ S.tiny)
              (yn : R.NonNegative (x p + h)) (yr : (x p + h) ≤ half) where
    module Cell = S.Cell p h hn ht yn yr
    module Trig = Cell.Trig inputs
    q = Cell.q
    z = C.trigPair T Cell.angle
    epsilon = C.complex (C.re z - R.1ℝ) (C.im z - (two * h) * d p)
    r = residual (x p) h
    inner = scale (d q) ((epsilon *C Nbar (x q)) +C scale (d p) r)

    phaseStep : phase q ≈C (phase p *C z)
    phaseStep =
      C.≈C-trans (C.≈C-sym (C.expImaginaryIsTrigPair T (two * atan q)))
        (C.≈C-trans
          (C.expCongruent T (C.complex-equivalent P.≃-refl
            (let open P.ℝ-Solver in solve 2
              (λ a b → Κ (+ 2 / 1) ⊗ b ⊜ Κ (+ 2 / 1) ⊗ a
                ⊕ Κ (+ 2 / 1) ⊗ (b ⊖ a)) P.≃-refl (atan p) (atan q))))
          (C.≈C-trans (Native.originalNativeImaginaryExpProduct inputs (two * atan p) Cell.angle)
            (C.mulCongruent (C.expImaginaryIsTrigPair T (two * atan p))
              (C.expImaginaryIsTrigPair T Cell.angle))))

    baseR : ℝ
    baseR = (d q * C.re (Nbar (x q)) - d p * C.re (Nbar (x p)))
      - ((two * h) * d p) * (d q * C.im (Nbar (x q)))

    baseI : ℝ
    baseI = (d q * C.im (Nbar (x q)) - d p * C.im (Nbar (x p)))
      + ((two * h) * d p) * (d q * C.re (Nbar (x q)))

    baseRRead : baseR ≃ (d p * d q) * C.re r
    baseRRead =
      P.≃-trans
        (P.+-cong (clearDifference p q (C.re (Nbar (x q))) (C.re (Nbar (x p)))) P.≃-refl)
        (P.≃-trans
          (let open P.ℝ-Solver in solve 5
            (λ i j b t u → (i ⊗ j) ⊗ b ⊖ (t ⊗ i) ⊗ (j ⊗ u)
              ⊜ (i ⊗ j) ⊗ (b ⊖ t ⊗ u))
            P.≃-refl (d p) (d q)
            (denom (x p) * C.re (Nbar (x q)) - denom (x q) * C.re (Nbar (x p)))
            (two * h) (C.im (Nbar (x q))))
          (P.*-congˡ (crossReal (x p) h)))

    baseIRead : baseI ≃ (d p * d q) * C.im r
    baseIRead =
      P.≃-trans
        (P.+-cong (clearDifference p q (C.im (Nbar (x q))) (C.im (Nbar (x p)))) P.≃-refl)
        (P.≃-trans
          (let open P.ℝ-Solver in solve 5
            (λ i j b t u → (i ⊗ j) ⊗ b ⊕ (t ⊗ i) ⊗ (j ⊗ u)
              ⊜ (i ⊗ j) ⊗ (b ⊕ t ⊗ u))
            P.≃-refl (d p) (d q)
            (denom (x p) * C.im (Nbar (x q)) - denom (x q) * C.im (Nbar (x p)))
            (two * h) (C.re (Nbar (x q))))
          (P.*-congˡ (crossImag (x p) h)))

    innerRead : ((z *C scale (d q) (Nbar (x q))) -C scale (d p) (Nbar (x p))) ≈C inner
    innerRead = C.complex-equivalent real imag
      where
      c = C.re z
      s = C.im z
      i = d p
      j = d q
      a = C.re (Nbar (x q))
      b = C.im (Nbar (x q))
      a0 = C.re (Nbar (x p))
      b0 = C.im (Nbar (x p))
      t = two * h
      real = P.≃-trans
        (let open P.ℝ-Solver in solve 8
          (λ c s i j a b a0 t →
            (c ⊗ (j ⊗ a) ⊖ s ⊗ (j ⊗ b)) ⊖ i ⊗ a0
            ⊜ j ⊗ ((c ⊖ Κ Q.1ℚᵘ) ⊗ a ⊖ (s ⊖ t ⊗ i) ⊗ b)
              ⊕ ((j ⊗ a ⊖ i ⊗ a0) ⊖ (t ⊗ i) ⊗ (j ⊗ b)))
          P.≃-refl c s i j a b a0 t)
        (P.≃-trans (P.+-cong P.≃-refl baseRRead)
          (let open P.ℝ-Solver in solve 4
            (λ j e i r → j ⊗ e ⊕ (i ⊗ j) ⊗ r ⊜ j ⊗ (e ⊕ i ⊗ r))
            P.≃-refl j (C.re (epsilon *C Nbar (x q))) i (C.re r)))
      imag = P.≃-trans
        (let open P.ℝ-Solver in solve 8
          (λ c s i j a b b0 t →
            (c ⊗ (j ⊗ b) ⊕ s ⊗ (j ⊗ a)) ⊖ i ⊗ b0
            ⊜ j ⊗ ((c ⊖ Κ Q.1ℚᵘ) ⊗ b ⊕ (s ⊖ t ⊗ i) ⊗ a)
              ⊕ ((j ⊗ b ⊖ i ⊗ b0) ⊕ (t ⊗ i) ⊗ (j ⊗ a)))
          P.≃-refl c s i j a b b0 t)
        (P.≃-trans (P.+-cong P.≃-refl baseIRead)
          (let open P.ℝ-Solver in solve 4
            (λ j e i r → j ⊗ e ⊕ (i ⊗ j) ⊗ r ⊜ j ⊗ (e ⊕ i ⊗ r))
            P.≃-refl j (C.im (epsilon *C Nbar (x q))) i (C.im r)))

    exactIncrement : (H q -C H p) ≈C (phase p *C inner)
    exactIncrement = C.≈C-trans
      (C.subCongruent (C.mulCongruent phaseStep (C.≈C-refl _)) (C.≈C-refl _))
      (C.≈C-trans
        (factorDifference (phase p) z (scale (d q) (Nbar (x q))) (scale (d p) (Nbar (x p))))
        (C.mulCongruent (C.≈C-refl _) innerRead))

    epsilonBox : Box epsilon (S.twentyfive * Cell.h2)
    epsilonBox = P.≤-trans Trig.cosError
      (P.*-monoʳ-≤-nonNeg
        (P.p≤q⇒p⋆≤q⋆ (+ 9 / 1) (+ 25 / 1) (from-yes ((+ 9 / 1) QP.≤? (+ 25 / 1))))
        Cell.h2NN) , Trig.sinError

    residualNN : R.NonNegative (two * Cell.h2)
    residualNN = P.nonNegx,y⇒nonNegx*y S.twoNN Cell.h2NN

    residualBox : Box r (two * Cell.h2)
    residualBox = P.≤-reflexive (absNN residualNN) ,
      P.≤-respˡ-≃ (P.∣-x∣≃∣x∣ {x = (two * Cell.h2) * x q})
        (P.≤-respʳ-≃ (P.*-identityʳ (two * Cell.h2))
          (boundMul (P.≤-reflexive (absNN residualNN))
            (P.≤-respˡ-≃ (absNN (nn q)) (xOne q))))

    innerBox : Box inner (((+ 102 / 1) ⋆) * Cell.h2)
    innerBox = boxBudgetCong
      (let open P.ℝ-Solver in solve 1
        (λ k → ((Κ (+ 25 / 1) ⊗ k) ⊗ Κ (+ 2 / 1)
          ⊕ (Κ (+ 25 / 1) ⊗ k) ⊗ Κ (+ 2 / 1))
          ⊕ Κ (+ 2 / 1) ⊗ k ⊜ Κ (+ 102 / 1) ⊗ k) P.≃-refl Cell.h2)
      (boxScale (dNN q) (dUpper q)
        (boxAdd (boxMul epsilonBox (nbarBox q)) (boxScale (dNN p) (dUpper p) residualBox)))

    quadraticIncrement : Box (H q -C H p) (((+ 204 / 1) ⋆) * (h * h))
    quadraticIncrement = boxCong exactIncrement
      (boxBudgetCong
        (let open P.ℝ-Solver in solve 1
          (λ k → Κ Q.1ℚᵘ ⊗ (Κ (+ 102 / 1) ⊗ k)
            ⊕ Κ Q.1ℚᵘ ⊗ (Κ (+ 102 / 1) ⊗ k) ⊜ Κ (+ 204 / 1) ⊗ k)
          P.≃-refl Cell.h2)
        (boxMul (phaseBox p) innerBox))
