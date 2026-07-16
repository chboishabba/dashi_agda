module DASHI.Foundations.ComplexAxiomatic where

-- Concrete complex pairs over DASHI's axiomatic real carrier.  The L¹ norm
-- is deliberately used: it avoids square roots while retaining the triangle
-- and product majorants needed by the finite-polydisc Cauchy consumer.

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ ; 0ℝ ; _+ℝ_ ; _-ℝ_ ; _*ℝ_ ; -ℝ_ ; absℝ ; _≤ℝ_
  ; ≤ℝ-refl ; ≤ℝ-trans ; +-mono-≤ ; absAddSubadditive ; absSubadditive
  ; absMul ; mulMonotoneNonnegative ; +-comm ; +-assoc ; *-comm ; *-assoc
  ; *-distribˡ-+ ; *-distribʳ-+ )

infixl 20 _+ℂ_ _−ℂ_
infixl 30 _*ℂ_

ℂ : Set
ℂ = ℝ × ℝ

sym :
  {A : Set} →
  {x y : A} →
  x ≡ y →
  y ≡ x
sym refl = refl

cong :
  {A B : Set} →
  {x y : A} →
  (f : A → B) →
  x ≡ y →
  f x ≡ f y
cong f refl = refl

trans :
  {A : Set} →
  {x y z : A} →
  x ≡ y →
  y ≡ z →
  x ≡ z
trans refl yz = yz

equalityLe :
  {x y : ℝ} →
  x ≡ y →
  x ≤ℝ y
equalityLe refl = ≤ℝ-refl

fourSwap :
  ∀ a c b d →
  (a +ℝ c) +ℝ (b +ℝ d) ≡ (a +ℝ b) +ℝ (c +ℝ d)
fourSwap a c b d =
  trans
    (+-assoc a c (b +ℝ d))
    (trans
      (cong (λ q → a +ℝ q) (sym (+-assoc c b d)))
      (trans
        (cong (λ q → a +ℝ (q +ℝ d)) (+-comm c b))
        (trans
          (cong (λ q → a +ℝ q) (+-assoc b c d))
          (sym (+-assoc a b (c +ℝ d))))))

0ℂ : ℂ
0ℂ = 0ℝ , 0ℝ

_+ℂ_ : ℂ → ℂ → ℂ
(a , b) +ℂ (c , d) = (a +ℝ c) , (b +ℝ d)

_−ℂ_ : ℂ → ℂ → ℂ
(a , b) −ℂ (c , d) = (a -ℝ c) , (b -ℝ d)

_*ℂ_ : ℂ → ℂ → ℂ
(a , b) *ℂ (c , d) = (a *ℝ c -ℝ b *ℝ d) , (a *ℝ d +ℝ b *ℝ c)

norm₁ : ℂ → ℝ
norm₁ (a , b) = absℝ a +ℝ absℝ b

norm₁-add :
  ∀ z w →
  norm₁ (z +ℂ w) ≤ℝ norm₁ z +ℝ norm₁ w
norm₁-add (a , b) (c , d) =
  ≤ℝ-trans
    (+-mono-≤ (absAddSubadditive a c) (absAddSubadditive b d))
    (equalityLe (fourSwap (absℝ a) (absℝ c) (absℝ b) (absℝ d)))

-- The proof intentionally exposes the four scalar majorants.  The final
-- regrouping is a ring identity over ℝ, derived solely from the imported
-- distributive/commutative ordered-ring fragment.
norm₁-mul :
  ∀ z w →
  norm₁ (z *ℂ w) ≤ℝ norm₁ z *ℝ norm₁ w
norm₁-mul (a , b) (c , d) =
  ≤ℝ-trans
    (+-mono-≤
      (≤ℝ-trans
        (absSubadditive (a *ℝ c) (b *ℝ d))
        (+-mono-≤
          (rewriteAbs a c)
          (rewriteAbs b d)))
      (≤ℝ-trans
        (absAddSubadditive (a *ℝ d) (b *ℝ c))
        (+-mono-≤
          (rewriteAbs a d)
          (rewriteAbs b c))))
    (equalityLe (fourTermsFactor (absℝ a) (absℝ b) (absℝ c) (absℝ d)))
  where
  rewriteAbs :
    ∀ x y →
    absℝ (x *ℝ y) ≤ℝ absℝ x *ℝ absℝ y
  rewriteAbs x y rewrite absMul x y = ≤ℝ-refl

  regroup :
    ∀ AC AD BC BD →
    (AC +ℝ BD) +ℝ (AD +ℝ BC)
      ≡
    (AC +ℝ AD) +ℝ (BC +ℝ BD)
  regroup AC AD BC BD =
    trans
      (fourSwap AC BD AD BC)
      (cong (λ q → (AC +ℝ AD) +ℝ q) (+-comm BD BC))

  fourTermsFactor :
    ∀ A B C D →
    ((A *ℝ C +ℝ B *ℝ D) +ℝ (A *ℝ D +ℝ B *ℝ C))
      ≡
    (A +ℝ B) *ℝ (C +ℝ D)
  fourTermsFactor A B C D
    rewrite *-distribʳ-+ A B (C +ℝ D)
          | *-distribˡ-+ A C D
          | *-distribˡ-+ B C D
          | regroup (A *ℝ C) (A *ℝ D) (B *ℝ C) (B *ℝ D) = refl
