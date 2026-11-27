module DASHI.Moonshine.JInvariantBishopCM163DiskCrossCoefficientExact where

-- SOURCE-WRITTEN, UNCOMPILED. Native scalar first-jet cut of the
-- original reciprocal-disk cross in Lean Paper9ScalarCross / DiskGerm.
-- Along the real disk ray A,B are real: log(q/q0)=-2*p*w/(1-w).
-- This does NOT construct the original analytic germs or Hecke product.
open import Data.Integer.Base using (+_; -_)
open import Data.Rational.Unnormalised using (_/_)
import Data.Rational.Unnormalised as Q
import Real as R
open R using (ℝ; _≃_; _*_; _+_; _-_; _⋆)
import RealProperties as P
import Inverse as Inv
import DASHI.Moonshine.JInvariantBishopCM163NativeJetReductionExact as J
import DASHI.Foundations.BishopChudnovskySignedPeriodNormalizationExact as N

-- Use the actual signed literal kappa, never its absolute value.
kq : Q.ℚᵘ
kq = (- (+ 77859659565707)) / 19943834790540897829879824384000

c m : ℝ
c = (+ 163 / 41) ⋆
m = (+ 163 / 1681) ⋆

-- Normalize P2 and P3 with the literal packet relations:
-- 41 P2=163 S2, 41 P3-326 S3=163 kappa S2.
p2 : ℝ → ℝ
p2 s = c * s

p3 : ℝ → ℝ → ℝ
p3 s t = ((+ 326 / 41) ⋆) * t + c * J.κ * s

-- First coefficient of (N*P-M*S)*X^2 - N*M*X*(w*T).
-- The zero-mode term is retained explicitly. N0=A^2,
-- M0=(163/41)A^2, N1=-(81/41)AB, M1=(163/1681)AB.
residual : ℝ → ℝ → ℝ → ℝ → ℝ
residual a b s t =
  ((((- (+ 81)) / 41) ⋆) * a * b * p2 s +
    (a * a) * p3 s t * a -
    (m * a * b * s + c * (a * a) * t * a)) * (a * a) +
  ((a * a) * p2 s - c * (a * a) * s) * (((+ 2 / 1) ⋆) * a * b) -
  ((a * a) * (c * (a * a)) * a * t)

-- The entire forty-factor derivative is absent: only its center slope
-- S3 occurs, and cancels after using the original signed packet ratios.
factor : (a b s t : ℝ) → residual a b s t ≃
  (c * ((a * a) * a) * s) * (J.κ * (a * a) - ((+ 2 / 1) ⋆) * b)
factor a b s t = let open P.ℝ-Solver in
  solve 4 (λ a b s t →
    ((Κ ((- (+ 81)) / 41) ⊗ a ⊗ b ⊗ (Κ (+ 163 / 41) ⊗ s)
      ⊕ (a ⊗ a) ⊗ (Κ (+ 326 / 41) ⊗ t ⊕ Κ (+ 163 / 41) ⊗ Κ kq ⊗ s) ⊗ a
      ⊖ (Κ (+ 163 / 1681) ⊗ a ⊗ b ⊗ s
        ⊕ Κ (+ 163 / 41) ⊗ (a ⊗ a) ⊗ t ⊗ a)) ⊗ (a ⊗ a)
      ⊕ ((a ⊗ a) ⊗ (Κ (+ 163 / 41) ⊗ s)
        ⊖ Κ (+ 163 / 41) ⊗ (a ⊗ a) ⊗ s) ⊗ (Κ (+ 2 / 1) ⊗ a ⊗ b)
      ⊖ (a ⊗ a) ⊗ (Κ (+ 163 / 41) ⊗ (a ⊗ a)) ⊗ a ⊗ t)
    ⊜ (Κ (+ 163 / 41) ⊗ ((a ⊗ a) ⊗ a) ⊗ s)
      ⊗ (Κ kq ⊗ (a ⊗ a) ⊖ Κ (+ 2 / 1) ⊗ b))
    P.≃-refl a b s t

-- Cancel a genuine apartness witness, not classical negation of equality.
cancelApart : (v : ℝ) → R._≄0 v → ∀ {x y : ℝ} →
  (v * x) ≃ (v * y) → x ≃ y
cancelApart v hv {x} {y} h =
  P.≃-trans (P.≃-symm (cancel x))
    (P.≃-trans (P.*-congˡ h) (cancel y))
  where
  iv = Inv._⁻¹ v hv
  cancel : (z : ℝ) → (iv * (v * z)) ≃ z
  cancel z = P.≃-trans (P.≃-symm (P.*-assoc iv v z))
    (P.≃-trans (P.*-congʳ (P.≃-trans (P.*-comm iv v)
      (Inv.*-inverseʳ v hv))) (P.*-identityˡ z))

factorApart : (a s : ℝ) → R._≄0 a → R._≄0 s →
  ∀ {x : ℝ} → ((c * ((a * a) * a) * s) * x) ≃ R.0ℝ → x ≃ R.0ℝ
factorApart a s ha hs {x} h =
  cancelApart s hs (cancelApart a ha (cancelApart a ha
    (cancelApart a ha (N.cancelLeft c cPositive
      (P.≃-trans (P.≃-symm (shape x))
        (P.≃-trans h (shapeZero)))))))
  where
  import Data.Rational.Unnormalised.Properties as QP
  cPositive : R.Positive c
  cPositive = P.posp⇒posp⋆ (+ 163 / 41) (QP.positive⁻¹ (+ 163 / 41))
  shape : (z : ℝ) → (c * (a * (a * (a * (s * z))))) ≃
    ((c * ((a * a) * a) * s) * z)
  shape z = let open P.ℝ-Solver in solve 3 (λ a s z →
    Κ (+ 163 / 41) ⊗ (a ⊗ (a ⊗ (a ⊗ (s ⊗ z))))
    ⊜ (Κ (+ 163 / 41) ⊗ ((a ⊗ a) ⊗ a) ⊗ s) ⊗ z)
    P.≃-refl a s z
  shapeZero : R.0ℝ ≃ (c * (a * (a * (a * (s * R.0ℝ)))))
  shapeZero = let open P.ℝ-Solver in solve 2 (λ a s →
    Κ Q.0ℚᵘ ⊜ Κ (+ 163 / 41) ⊗ (a ⊗ (a ⊗ (a ⊗ (s ⊗ Κ Q.0ℚᵘ)))))
    P.≃-refl a s

correction : (a b s t : ℝ) → R._≄0 a → R._≄0 s →
  residual a b s t ≃ R.0ℝ →
  (J.κ * (a * a) - ((+ 2 / 1) ⋆) * b) ≃ R.0ℝ
correction a b s t ha hs h = factorApart a s ha hs
  (P.≃-trans (P.≃-symm (factor a b s t)) h)

-- On the actual real ray, q=q0*exp(-2*p*w/(1-w)).
-- If a=Dj,b=D^2j at q0, then the original germ coefficients are
-- A=-2*p*a and B=-2*p*a+2*p^2*b.
A : ℝ → ℝ → ℝ
A p a = (((- (+ 2)) / 1) ⋆) * p * a

diskB : ℝ → ℝ → ℝ → ℝ
diskB p a b = A p a + ((+ 2 / 1) ⋆) * (p * p) * b

diskShape : (p a b : ℝ) →
  (J.κ * (A p a * A p a) - ((+ 2 / 1) ⋆) * diskB p a b) ≃
  (((+ 4 / 1) ⋆) * p) * (p * J.κ * (a * a) - (p * b - a))
diskShape p a b = let open P.ℝ-Solver in solve 3 (λ p a b →
  Κ kq ⊗ ((Κ ((- (+ 2)) / 1) ⊗ p ⊗ a) ⊗
    (Κ ((- (+ 2)) / 1) ⊗ p ⊗ a))
  ⊖ Κ (+ 2 / 1) ⊗ (Κ ((- (+ 2)) / 1) ⊗ p ⊗ a
    ⊕ Κ (+ 2 / 1) ⊗ (p ⊗ p) ⊗ b)
  ⊜ (Κ (+ 4 / 1) ⊗ p) ⊗ (p ⊗ Κ kq ⊗ (a ⊗ a) ⊖ (p ⊗ b ⊖ a)))
  P.≃-refl p a b

import Data.Rational.Unnormalised.Properties as QP

diskJet : (a b s t : ℝ) → R.Positive J.p →
  R._≄0 (A J.p a) → R._≄0 s →
  residual (A J.p a) (diskB J.p a b) s t ≃ R.0ℝ →
  J.DiskJet a b
diskJet a b s t pp ha hs h =
  let
    four = (+ 4 / 1) ⋆
    pv = P.posx,y⇒posx*y (P.posp⇒posp⋆ (+ 4 / 1) (QP.positive⁻¹ (+ 4 / 1))) pp
    hz = N.cancelLeft (four * J.p) pv
      (P.≃-trans (P.≃-symm (diskShape J.p a b))
        (P.≃-trans (correction (A J.p a) (diskB J.p a b) s t ha hs h)
          (P.≃-symm (P.*-zeroʳ (four * J.p)))))
    open P.ℝ-Solver
  in P.≃-trans
    (solve 2 (λ x y → x ⊜ (x ⊖ y) ⊕ y) P.≃-refl
      (J.p * J.κ * (a * a)) (J.p * b - a))
    (P.≃-trans (P.+-cong hz P.≃-refl) (P.+-identityˡ (J.p * b - a)))

-- Consume the actual first/second q jets; no new period or cross owner.
signedJet : (a b s t : ℝ) → R.Positive J.p →
  R._≄0 (A J.p a) → R._≄0 s →
  J.FirstQJet a → J.SecondQJet b →
  residual (A J.p a) (diskB J.p a b) s t ≃ R.0ℝ →
  J.SignedJet
signedJet a b s t pp ha hs h1 h2 h =
  J.signedFromDiskJet a b h1 h2 (diskJet a b s t pp ha hs h)
