module DASHI.Physics.YangMills.BalabanIntervalAdjointComposition where

-- Reverse semigroup law for the composed adjoints.  Together with
-- `BalabanIntervalConstraintComposition`, this identifies both sides of the
-- simultaneous covariance Q_{k:m} C Q_{k:m}* under an arbitrary interval
-- split.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)

open import DASHI.Physics.YangMills.BalabanNestedConstraintMinimum using
  ( cong
  ; trans
  )
open import DASHI.Physics.YangMills.BalabanIntervalConstraintCovariance using
  ( intervalAdjoint )
open import DASHI.Physics.YangMills.BalabanIntervalConstraintComposition using
  ( transport
  ; natAddAssocTransport
  )

sym : {A : Set} → {x y : A} → x ≡ y → y ≡ x
sym refl = refl

-- Pulling back after transporting a coarse vector equals transporting the
-- pulled-back vector at the preceding scale.
adjointTransportStep :
  (Space : ℕ → Set) →
  (Q* : (i : ℕ) → Space (suc i) → Space i) →
  ∀ {i j} →
  (indexEquality : i ≡ j) →
  (z : Space (suc i)) →
  Q* j (transport Space (cong suc indexEquality) z)
    ≡ transport Space indexEquality (Q* i z)
adjointTransportStep Space Q* refl z = refl

intervalAdjointAppend :
  (Space : ℕ → Set) →
  (Q* : (i : ℕ) → Space (suc i) → Space i) →
  ∀ k n m →
  (z : Space ((m + n) + k)) →
  intervalAdjoint Space Q* k (m + n) z
    ≡ intervalAdjoint Space Q* k n
        (intervalAdjoint Space Q* (n + k) m
          (transport Space (natAddAssocTransport m n k) z))
intervalAdjointAppend Space Q* k n zero z = refl
intervalAdjointAppend Space Q* k n (suc m) z =
  let
    leftIndex = (m + n) + k
    rightIndex = m + (n + k)
    indexEquality = natAddAssocTransport m n k
    pulled = Q* leftIndex z
    ih = intervalAdjointAppend Space Q* k n m pulled
    stepEquality = adjointTransportStep Space Q* indexEquality z
    p2 = cong
      (λ y →
        intervalAdjoint Space Q* k n
          (intervalAdjoint Space Q* (n + k) m y))
      (sym stepEquality)
  in
    trans ih p2
