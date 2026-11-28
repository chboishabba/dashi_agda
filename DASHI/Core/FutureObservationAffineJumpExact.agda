module DASHI.Core.FutureObservationAffineJumpExact where

-- Source-written generic action-power and affine residual proof.
-- Instantiate with the existing future-observation projection and the
-- actual reduced GF(2) matrices; no assertion of an efficient producer
-- for arbitrary nonlinear dynamics.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

iterate : ∀ {S : Set} → (S → S) → Nat → S → S
iterate f zero x = x
iterate f (suc n) x = f (iterate f n x)

iterateAdd : ∀ {S : Set} (f : S → S) (m n : Nat) (x : S) →
  iterate f (m + n) x ≡ iterate f m (iterate f n x)
iterateAdd f zero n x = refl
iterateAdd f (suc m) n x = cong f (iterateAdd f m n x)

projectIterate : ∀ {S Q : Set} (q : S → Q) (f : S → S) (g : Q → Q) →
  (∀ x → q (f x) ≡ g (q x)) →
  ∀ n x → q (iterate f n x) ≡ iterate g n (q x)
projectIterate q f g square zero x = refl
projectIterate q f g square (suc n) x =
  trans (square (iterate f n x))
    (cong g (projectIterate q f g square n x))

squareStep : ∀ {S : Set} (f : S → S) → S → S
squareStep f x = f (f x)

squareIterate : ∀ {S : Set} (f : S → S) (n : Nat) (x : S) →
  iterate (squareStep f) n x ≡ iterate f (n + n) x
squareIterate f zero x = refl
squareIterate f (suc n) x =
  trans (cong (squareStep f) (squareIterate f n x))
    (cong f (sym (slide n)))
  where
    slide : ∀ k → iterate f (k + suc k) x ≡ f (iterate f (k + k) x)
    slide k = trans (iterateAdd f k (suc k) x)
      (trans (commute k (iterate f k x))
        (cong f (sym (iterateAdd f k k x))))
      where
        commute : ∀ j y → iterate f j (f y) ≡ f (iterate f j y)
        commute zero y = refl
        commute (suc j) y = cong f (commute j y)

-- Actual affine expansion over any associative additive carrier.
-- Linear map additivity is the only algebraic premise used here.
module AffineExpansion
  {S : Set} (_⊕_ : S → S → S) (z : S)
  (M : S → S) (b : S)
  (assoc : ∀ x y w → (x ⊕ y) ⊕ w ≡ x ⊕ (y ⊕ w))
  (rightZero : ∀ x → x ⊕ z ≡ x)
  (linear : ∀ x y → M (x ⊕ y) ≡ M x ⊕ M y)
  where
  affine : S → S
  affine x = M x ⊕ b

  offset : Nat → S
  offset zero = z
  offset (suc n) = M (offset n) ⊕ b

  affineIterate : ∀ n x →
    iterate affine n x ≡ iterate M n x ⊕ offset n
  affineIterate zero x = sym (rightZero x)
  affineIterate (suc n) x =
    trans (cong affine (affineIterate n x))
      (trans (cong (λ y → y ⊕ b) (linear (iterate M n x) (offset n)))
        (assoc (M (iterate M n x)) (M (offset n)) b))

-- Two-level bilinear input/linear output identity. The domain of P
-- need not be the domain of B: the NS rate projector is on incidences.
module BilinearOutput
  {V W : Set} (_+v_ : V → V → V) (_+w_ : W → W → W)
  (F : V → V → W)
  (leftAdd : ∀ x y w → F (x +v y) w ≡ F x w +w F y w)
  (rightAdd : ∀ x y w → F x (y +v w) ≡ F x y +w F x w)
  where
  fourTerms : ∀ x r →
    F (x +v r) (x +v r) ≡
    (F x x +w F x r) +w (F r x +w F r r)
  fourTerms x r =
    trans (leftAdd x r (x +v r))
      (trans (cong (λ y → y +w F r (x +v r)) (rightAdd x x r))
        (cong (λ y → (F x x +w F x r) +w y) (rightAdd r x r)))
