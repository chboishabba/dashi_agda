module DASHI.Physics.YangMills.BalabanBlockDeterminantProduct where

-- Finite induction from a one-block determinant factorisation to the full
-- block-Cholesky product.
--
-- The source-specific work must prove, for the literal simultaneous covariance
-- determinant D and conditional shell factor Gamma,
--
--   D_{n+1} = D_n * Gamma_n.
--
-- Given that equality, this module proves
--
--   D_n = product_{r < n} Gamma_r
--
-- and its arbitrary-interval form.  No determinant law is postulated as a
-- field or status record; the one-step equality remains an explicit argument.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)

sym : {A : Set} → {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl y≡z = y≡z

cong :
  {A B : Set} →
  (f : A → B) →
  {x y : A} →
  x ≡ y →
  f x ≡ f y
cong f refl = refl

natAddAssoc :
  ∀ a b c →
  (a + b) + c ≡ a + (b + c)
natAddAssoc zero b c = refl
natAddAssoc (suc a) b c =
  cong suc (natAddAssoc a b c)

shellProduct :
  {Scalar : Set} →
  Scalar →
  (Scalar → Scalar → Scalar) →
  (ℕ → Scalar) →
  ℕ →
  Scalar
shellProduct one _*_ factor zero = one
shellProduct one _*_ factor (suc n) =
  shellProduct one _*_ factor n * factor n

blockDeterminantProductFromStep :
  {Scalar : Set} →
  (one : Scalar) →
  (_*_ : Scalar → Scalar → Scalar) →
  (determinant conditional : ℕ → Scalar) →
  determinant zero ≡ one →
  (∀ n → determinant (suc n) ≡ determinant n * conditional n) →
  ∀ n →
  determinant n ≡ shellProduct one _*_ conditional n
blockDeterminantProductFromStep
  one _*_ determinant conditional base step zero = base
blockDeterminantProductFromStep
  one _*_ determinant conditional base step (suc n) =
  trans
    (step n)
    (cong
      (λ prefix → prefix * conditional n)
      (blockDeterminantProductFromStep
        one _*_ determinant conditional base step n))

-- Interval product with factors k,...,k+n-1.
intervalProduct :
  {Scalar : Set} →
  Scalar →
  (Scalar → Scalar → Scalar) →
  (ℕ → Scalar) →
  ℕ → ℕ →
  Scalar
intervalProduct one _*_ factor k zero = one
intervalProduct one _*_ factor k (suc n) =
  intervalProduct one _*_ factor k n * factor (n + k)

intervalProductAppend :
  {Scalar : Set} →
  (one : Scalar) →
  (_*_ : Scalar → Scalar → Scalar) →
  (assoc : ∀ a b c → (a * b) * c ≡ a * (b * c)) →
  (rightIdentity : ∀ a → a * one ≡ a) →
  (factor : ℕ → Scalar) →
  ∀ k n m →
  intervalProduct one _*_ factor k (m + n)
    ≡ intervalProduct one _*_ factor k n
        * intervalProduct one _*_ factor (n + k) m
intervalProductAppend
  one _*_ assoc rightIdentity factor k n zero =
  sym (rightIdentity (intervalProduct one _*_ factor k n))
intervalProductAppend
  one _*_ assoc rightIdentity factor k n (suc m) =
  let
    leftPrefix = intervalProduct one _*_ factor k n
    rightPrefix = intervalProduct one _*_ factor (n + k) m
    leftIndex = (m + n) + k
    rightIndex = m + (n + k)
    leftFactor = factor leftIndex
    ih = intervalProductAppend
      one _*_ assoc rightIdentity factor k n m
    indexEquality = natAddAssoc m n k
    factorEquality = cong factor indexEquality
    p1 = cong (λ product → product * leftFactor) ih
    p2 = assoc leftPrefix rightPrefix leftFactor
    p3 = cong
      (λ finalFactor → leftPrefix * (rightPrefix * finalFactor))
      factorEquality
  in
    trans p1 (trans p2 p3)

-- The same induction starting from an arbitrary determinant D_k.
blockDeterminantIntervalFromStep :
  {Scalar : Set} →
  (one : Scalar) →
  (_*_ : Scalar → Scalar → Scalar) →
  (determinant conditional : ℕ → Scalar) →
  (assoc : ∀ a b c → (a * b) * c ≡ a * (b * c)) →
  (rightIdentity : ∀ a → a * one ≡ a) →
  (∀ j → determinant (suc j) ≡ determinant j * conditional j) →
  ∀ k n →
  determinant (n + k)
    ≡ determinant k * intervalProduct one _*_ conditional k n
blockDeterminantIntervalFromStep
  one _*_ determinant conditional assoc rightIdentity step k zero =
  sym (rightIdentity (determinant k))
blockDeterminantIntervalFromStep
  one _*_ determinant conditional assoc rightIdentity step k (suc n) =
  let
    index = n + k
    ih = blockDeterminantIntervalFromStep
      one _*_ determinant conditional assoc rightIdentity step k n
    p1 = step index
    p2 = cong (λ prefix → prefix * conditional index) ih
    p3 = assoc
      (determinant k)
      (intervalProduct one _*_ conditional k n)
      (conditional index)
  in
    trans p1 (trans p2 p3)
