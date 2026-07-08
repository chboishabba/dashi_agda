module DASHI.Physics.ClaySupportingElementaryLemmas where

------------------------------------------------------------------------
-- Elementary, fully-proved supporting lemmas.
--
-- This module collects genuinely elementary mathematical facts that the
-- YM/NS proof packages lean on structurally.  Every declaration here is a
-- real Agda proof over concrete natural numbers -- there are NO `postulate`s
-- and NO extra axioms in this file.  These lemmas are honest "beams": they
-- do not, and are not claimed to, discharge any of the open Clay-level
-- analytic leaves (the uniform weighted-Schur operator bound, the P10
-- large-field suppression estimate, BKM closure, etc.).  They only make the
-- surrounding elementary algebra concrete and machine-checked.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _≤_)
open import Data.Nat.Properties
  using ( +-assoc; +-comm; *-distribˡ-+; *-distribʳ-+; *-zeroʳ
        ; +-mono-≤; ≤-refl )
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; sym; trans; subst)

------------------------------------------------------------------------
-- A local list sum, kept self-contained so the algebra below is
-- transparent and independent of stdlib API drift.

sumL : List ℕ → ℕ
sumL []       = 0
sumL (x ∷ xs) = x + sumL xs

sumL-++ : ∀ (xs ys : List ℕ) → sumL (xs ++ ys) ≡ sumL xs + sumL ys
sumL-++ []       ys = refl
sumL-++ (x ∷ xs) ys =
  trans (cong (x +_) (sumL-++ xs ys))
        (sym (+-assoc x (sumL xs) (sumL ys)))

-- Pulling a scalar out of a summed, scaled list:  Σ (c·yⱼ) = c · Σ yⱼ.
sumL-map-* : ∀ (c : ℕ) (ys : List ℕ) → sumL (map (c *_) ys) ≡ c * sumL ys
sumL-map-* c []       = sym (*-zeroʳ c)
sumL-map-* c (y ∷ ys) =
  trans (cong (c * y +_) (sumL-map-* c ys))
        (sym (*-distribˡ-+ c y (sumL ys)))

------------------------------------------------------------------------
-- Finite Cartesian product of two lists, term-by-term multiplied.
--   cart [x₁,…,xₘ] [y₁,…,yₙ] = [x₁y₁,…,x₁yₙ, x₂y₁,…, …, xₘyₙ]

cart : List ℕ → List ℕ → List ℕ
cart []       ys = []
cart (x ∷ xs) ys = map (x *_) ys ++ cart xs ys

------------------------------------------------------------------------
-- The finite Cauchy / Schur product identity:
--     (Σ xᵢ) · (Σ yⱼ)  =  Σ_{i,j} xᵢ·yⱼ.
--
-- This is exactly the algebra behind the NS package's §III warning: the
-- product of the two profile sums equals the FULL cross-term sum, not the
-- sum of the diagonal terms alone.

sumProd :
  ∀ (xs ys : List ℕ) →
  sumL xs * sumL ys ≡ sumL (cart xs ys)
sumProd []       ys = refl
sumProd (x ∷ xs) ys =
  trans (*-distribʳ-+ (sumL ys) x (sumL xs))
        (trans (cong₂ _+_ (sym (sumL-map-* x ys)) (sumProd xs ys))
               (sym (sumL-++ (map (x *_) ys) (cart xs ys))))

------------------------------------------------------------------------
-- Elementwise domination of lists and monotonicity of the sum.

data _≤*_ : List ℕ → List ℕ → Set where
  []  : [] ≤* []
  _∷_ : ∀ {x b xs bs} → x ≤ b → xs ≤* bs → (x ∷ xs) ≤* (b ∷ bs)

sumL-mono : ∀ {xs bs : List ℕ} → xs ≤* bs → sumL xs ≤ sumL bs
sumL-mono []           = ≤-refl
sumL-mono (x≤b ∷ rest) = +-mono-≤ x≤b (sumL-mono rest)

------------------------------------------------------------------------
-- Finite weighted-Schur / cross-product bound.
--
-- If every cross term xᵢ·yⱼ is dominated by a bound bₖ, then the product of
-- the two sums is dominated by the sum of the bounds:
--     (Σ xᵢ)·(Σ yⱼ) = Σ_{i,j} xᵢyⱼ ≤ Σ bₖ.
--
-- This is the correct, cross-term-aware inference; it is precisely what the
-- NS package flags as the step that must NOT be replaced by the false
-- "diagonal-only" inference.

schurCrossBound :
  ∀ (xs ys bs : List ℕ) →
  cart xs ys ≤* bs →
  sumL xs * sumL ys ≤ sumL bs
schurCrossBound xs ys bs dom =
  subst (λ z → z ≤ sumL bs) (sym (sumProd xs ys)) (sumL-mono dom)

------------------------------------------------------------------------
-- Powers and the finite geometric sum, with the root-ball / KP recursion
--     Σ_{j=0}^{R+1} bʲ = 1 + b · Σ_{j=0}^{R} bʲ.
--
-- This is the elementary identity behind the P06 bounded-degree root-ball
-- growth bound (package §II.1) and the KP geometric tail (package §V).

pow : ℕ → ℕ → ℕ
pow b zero    = 1
pow b (suc n) = b * pow b n

geomSum : ℕ → ℕ → ℕ           -- Σ_{j=0}^{n} bʲ  (that is, n+1 terms)
geomSum b zero    = 1
geomSum b (suc n) = pow b (suc n) + geomSum b n

-- b·p + (1 + b·g) = 1 + (b·p + b·g)
private
  lemA : ∀ (b p g : ℕ) → b * p + (1 + b * g) ≡ 1 + (b * p + b * g)
  lemA b p g =
    trans (sym (+-assoc (b * p) 1 (b * g)))
          (trans (cong (_+ (b * g)) (+-comm (b * p) 1))
                 (+-assoc 1 (b * p) (b * g)))

  helper : ∀ (b p g : ℕ) → b * p + (1 + b * g) ≡ 1 + b * (p + g)
  helper b p g =
    trans (lemA b p g)
          (cong (1 +_) (sym (*-distribˡ-+ b p g)))

geomSum-rec :
  ∀ (b n : ℕ) → geomSum b (suc n) ≡ 1 + b * geomSum b n
geomSum-rec b zero    = +-comm (b * pow b zero) (geomSum b zero)
geomSum-rec b (suc n) =
  trans (cong (λ z → b * pow b (suc n) + z) (geomSum-rec b n))
        (helper b (pow b (suc n)) (geomSum b n))

------------------------------------------------------------------------
-- Concrete four-profile instance of `schurCrossBound`, matching the NS
-- package's §III cross-matrix step (eqns (7)→(8)):
--   with profiles {FT, adv, trans, res}, if every one of the sixteen
--   cross terms rᵢ·cⱼ is bounded by Aᵢⱼ, then the product of the total
--   row-sum and column-sum is bounded by Σᵢⱼ Aᵢⱼ.

fourProfileCrossBound :
  ∀ (r1 r2 r3 r4 c1 c2 c3 c4 : ℕ)
    (A11 A12 A13 A14 A21 A22 A23 A24
     A31 A32 A33 A34 A41 A42 A43 A44 : ℕ) →
  r1 * c1 ≤ A11 → r1 * c2 ≤ A12 → r1 * c3 ≤ A13 → r1 * c4 ≤ A14 →
  r2 * c1 ≤ A21 → r2 * c2 ≤ A22 → r2 * c3 ≤ A23 → r2 * c4 ≤ A24 →
  r3 * c1 ≤ A31 → r3 * c2 ≤ A32 → r3 * c3 ≤ A33 → r3 * c4 ≤ A34 →
  r4 * c1 ≤ A41 → r4 * c2 ≤ A42 → r4 * c3 ≤ A43 → r4 * c4 ≤ A44 →
  sumL (r1 ∷ r2 ∷ r3 ∷ r4 ∷ []) * sumL (c1 ∷ c2 ∷ c3 ∷ c4 ∷ [])
    ≤ sumL ( A11 ∷ A12 ∷ A13 ∷ A14
         ∷ A21 ∷ A22 ∷ A23 ∷ A24
         ∷ A31 ∷ A32 ∷ A33 ∷ A34
         ∷ A41 ∷ A42 ∷ A43 ∷ A44 ∷ [])
fourProfileCrossBound r1 r2 r3 r4 c1 c2 c3 c4
  A11 A12 A13 A14 A21 A22 A23 A24 A31 A32 A33 A34 A41 A42 A43 A44
  h11 h12 h13 h14 h21 h22 h23 h24 h31 h32 h33 h34 h41 h42 h43 h44 =
  schurCrossBound (r1 ∷ r2 ∷ r3 ∷ r4 ∷ []) (c1 ∷ c2 ∷ c3 ∷ c4 ∷ []) _
    ( h11 ∷ h12 ∷ h13 ∷ h14
    ∷ h21 ∷ h22 ∷ h23 ∷ h24
    ∷ h31 ∷ h32 ∷ h33 ∷ h34
    ∷ h41 ∷ h42 ∷ h43 ∷ h44 ∷ [])
