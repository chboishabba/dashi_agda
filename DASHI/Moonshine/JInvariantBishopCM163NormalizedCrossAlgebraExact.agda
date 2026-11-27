module DASHI.Moonshine.JInvariantBishopCM163NormalizedCrossAlgebraExact where

-- SOURCE-WRITTEN. Clear the original shifted-product identities
-- without division by the centered j value or a Hecke factor.
-- On the real ray, N and M are the conjugate-branch products.
-- Cancel only w^4 off center; the center is paid by the literal packet.
open import Data.Integer.Base using (+_; -_)
open import Data.Rational.Unnormalised using (_/_)
import Data.Rational.Unnormalised as Q
import Real as R
open R using (ℝ; _≃_; _+_; _-_; _*_; _⋆)
import RealProperties as P
import DASHI.Moonshine.JInvariantBishopCM163DiskCrossCoefficientExact as Jet

-- The two exact original products before normalizing:
-- p*x² = m*D, s*x² = n*S, D-S=x*t.
-- D and S denote the actual forty-factor residual evaluated at x and 0.
rawCross : (x n m p s d h t : ℝ) →
  (p * (x * x)) ≃ (m * d) →
  (s * (x * x)) ≃ (n * h) →
  (d - h) ≃ (x * t) →
  (((n * p - m * s) * (x * x)) - n * m * x * t) ≃ R.0ℝ
rawCross x n m p s d h t hp hs ht =
  let open P.ℝ-Solver in
  P.≃-trans
    (P.+-cong (solve 5 (λ x n m p s →
      (n ⊗ p ⊖ m ⊗ s) ⊗ (x ⊗ x)
      ⊜ (n ⊗ (p ⊗ (x ⊗ x))) ⊖ (m ⊗ (s ⊗ (x ⊗ x))))
      P.≃-refl x n m p s) P.≃-refl)
    (P.≃-trans (P.+-cong (P.+-cong (P.*-congˡ hp)
      (P.-‿cong (P.*-congˡ hs))) P.≃-refl)
      (P.≃-trans
        (solve 6 (λ n m d h x t →
          (n ⊗ (m ⊗ d) ⊖ m ⊗ (n ⊗ h)) ⊖ n ⊗ m ⊗ x ⊗ t
          ⊜ (n ⊗ m) ⊗ ((d ⊖ h) ⊖ (x ⊗ t)))
          P.≃-refl n m d h x t)
        (P.≃-trans
          (P.*-congˡ (P.≃-trans (P.+-cong ht P.≃-refl) (P.+-inverseʳ (x * t))))
          (P.*-zeroʳ (n * m)))))
normalized : (w x n m p s d h t : ℝ) → R._≄0 w →
  (p * ((w * x) * (w * x))) ≃ (((w * w) * m) * d) →
  (s * ((w * x) * (w * x))) ≃ (((w * w) * n) * h) →
  (d - h) ≃ ((w * x) * t) →
  (((n * p - m * s) * (x * x)) - n * m * x * (w * t)) ≃ R.0ℝ
normalized w x n m p s d h t hw hp hs ht =
  let raw = rawCross (w * x) ((w * w) * n) ((w * w) * m) p s d h t hp hs ht
      v = ((n * p - m * s) * (x * x)) - n * m * x * (w * t)
      open P.ℝ-Solver
      expansion : (w * (w * (w * (w * v)))) ≃
        ((((w * w) * n) * p - ((w * w) * m) * s) * ((w * x) * (w * x))
          - ((w * w) * n) * ((w * w) * m) * (w * x) * t)
      expansion = solve 7 (λ w x n m p s t →
        w ⊗ (w ⊗ (w ⊗ (w ⊗ ((n ⊗ p ⊖ m ⊗ s) ⊗ (x ⊗ x) ⊖ n ⊗ m ⊗ x ⊗ (w ⊗ t)))))
        ⊜ (((w ⊗ w) ⊗ n) ⊗ p ⊖ ((w ⊗ w) ⊗ m) ⊗ s) ⊗ ((w ⊗ x) ⊗ (w ⊗ x))
          ⊖ ((w ⊗ w) ⊗ n) ⊗ ((w ⊗ w) ⊗ m) ⊗ (w ⊗ x) ⊗ t)
        P.≃-refl w x n m p s t
      zeroExpansion : R.0ℝ ≃ (w * (w * (w * (w * R.0ℝ))))
      zeroExpansion = solve 1 (λ w → Κ Q.0ℚᵘ ⊜ w ⊗ (w ⊗ (w ⊗ (w ⊗ Κ Q.0ℚᵘ)))) P.≃-refl w
  in Jet.cancelApart w hw (Jet.cancelApart w hw (Jet.cancelApart w hw
    (Jet.cancelApart w hw (P.≃-trans expansion (P.≃-trans raw zeroExpansion)))))

-- First-order truncated product on the actual Bishop carrier.
record FirstJet : Set where
  constructor jet
  field
    value slope : ℝ
open FirstJet

infixl 20 _+J_ _-J_
infixl 30 _*J_
_+J_ _-J_ _*J_ : FirstJet → FirstJet → FirstJet
jet a b +J jet c d = jet (a + c) (b + d)
jet a b -J jet c d = jet (a - c) (b - d)
jet a b *J jet c d = jet (a * c) (b * c + a * d)

-- No derivative of the forty-factor residual enters: w*T has
-- zero value and its slope is exactly the residual's center coefficient.
crossJet : (a b s t u v : ℝ) → FirstJet
crossJet a b s t u v =
  let x = jet a b
      n = jet (a * a) ((((- (+ 81)) / 41) ⋆) * a * b)
      m = jet (Jet.c * (a * a)) (Jet.m * a * b)
      p = jet u (v * a)
      q = jet s (t * a)
      wt = jet R.0ℝ t
  in ((n *J p -J m *J q) *J (x *J x)) -J (n *J m *J x *J wt)

-- Read the signed first coefficient into the existing scalar consumer.
slopeIsLiteral : (a b s t u v : ℝ) →
  slope (crossJet a b s t u v) ≃ Jet.literalResidual a b s t u v
slopeIsLiteral a b s t u v = let open P.ℝ-Solver in
  solve 6 (λ a b s t u v →
    ((((Κ ((- (+ 81)) / 41) ⊗ a ⊗ b) ⊗ u ⊕ (a ⊗ a) ⊗ (v ⊗ a))
      ⊖ ((Κ (+ 163 / 1681) ⊗ a ⊗ b) ⊗ s ⊕ (Κ (+ 163 / 41) ⊗ (a ⊗ a)) ⊗ (t ⊗ a)))
      ⊗ (a ⊗ a)
      ⊕ ((a ⊗ a) ⊗ u ⊖ (Κ (+ 163 / 41) ⊗ (a ⊗ a)) ⊗ s) ⊗ (b ⊗ a ⊕ a ⊗ b))
      ⊖ (((((Κ ((- (+ 81)) / 41) ⊗ a ⊗ b) ⊗ (Κ (+ 163 / 41) ⊗ (a ⊗ a))
           ⊕ (a ⊗ a) ⊗ (Κ (+ 163 / 1681) ⊗ a ⊗ b)) ⊗ a
          ⊕ ((a ⊗ a) ⊗ (Κ (+ 163 / 41) ⊗ (a ⊗ a))) ⊗ b) ⊗ Κ Q.0ℚᵘ)
        ⊕ (((a ⊗ a) ⊗ (Κ (+ 163 / 41) ⊗ (a ⊗ a))) ⊗ a) ⊗ t)
    ⊜ (((Κ ((- (+ 81)) / 41) ⊗ a ⊗ b ⊗ u ⊕ (a ⊗ a) ⊗ v ⊗ a
          ⊖ (Κ (+ 163 / 1681) ⊗ a ⊗ b ⊗ s ⊕ Κ (+ 163 / 41) ⊗ (a ⊗ a) ⊗ t ⊗ a))
         ⊗ (a ⊗ a))
        ⊕ ((a ⊗ a) ⊗ u ⊖ Κ (+ 163 / 41) ⊗ (a ⊗ a) ⊗ s) ⊗ (Κ (+ 2 / 1) ⊗ a ⊗ b)
        ⊖ ((a ⊗ a) ⊗ (Κ (+ 163 / 41) ⊗ (a ⊗ a)) ⊗ a ⊗ t)))
    P.≃-refl a b s t u v
