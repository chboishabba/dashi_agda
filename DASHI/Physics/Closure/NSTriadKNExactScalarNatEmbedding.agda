module DASHI.Physics.Closure.NSTriadKNExactScalarNatEmbedding where

open import Agda.Builtin.Nat using (Nat; zero; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNExactAlgebraicRetainedTriadFiber as Exact

------------------------------------------------------------------------
-- Scalarization laws required before a Nat incidence formula can be
-- compared with an exact scalar-valued retained-triad aggregate.
------------------------------------------------------------------------

record NatToScalarAdditive (S : Exact.ExactScalarOperations) : Set₁ where
  field
    zeroLaw : Exact.natToScalar S zero ≡ Exact.zero S
    addLaw :
      (m n : Nat) →
      Exact.natToScalar S (m + n) ≡
      Exact._+_ S (Exact.natToScalar S m) (Exact.natToScalar S n)

open NatToScalarAdditive public

natListSum : {A : Set} → (A → Nat) → List A → Nat
natListSum f [] = zero
natListSum f (x ∷ xs) = f x + natListSum f xs

natToScalarWeightedListSum :
  {S : Exact.ExactScalarOperations} →
  (laws : NatToScalarAdditive S) →
  {A : Set} →
  (weight : A → Nat) →
  (xs : List A) →
  Exact.weightedListSum
    {S = S}
    (λ x → Exact.natToScalar S (weight x))
    xs
  ≡
  Exact.natToScalar S (natListSum (λ x → weight x) xs)
natToScalarWeightedListSum {S = S} laws weight [] =
  sym (NatToScalarAdditive.zeroLaw laws)
natToScalarWeightedListSum {S = S} laws weight (x ∷ xs) =
  trans
    (cong
      (λ z → Exact._+_ S (Exact.natToScalar S (weight x)) z)
      (natToScalarWeightedListSum laws weight xs))
    (sym
      (NatToScalarAdditive.addLaw laws
        (weight x)
        (natListSum (λ y → weight y) xs)))

------------------------------------------------------------------------
-- Pointwise transport into the scalar weighted-sum normal form.
------------------------------------------------------------------------

weightedListSumCong :
  {S : Exact.ExactScalarOperations} →
  {A : Set} →
  {f g : A → Exact.Carrier S} →
  ((x : A) → f x ≡ g x) →
  (xs : List A) →
  Exact.weightedListSum {S = S} f xs ≡
  Exact.weightedListSum {S = S} g xs
weightedListSumCong pointwise [] = refl
weightedListSumCong {S = S} {f = f} {g = g} pointwise (x ∷ xs) =
  trans
    (cong
      (λ z →
        Exact._+_ S z
          (Exact.weightedListSum {S = S} (λ y → f y) xs))
      (pointwise x))
    (cong
      (λ z → Exact._+_ S (g x) z)
      (weightedListSumCong pointwise xs))

natToScalarWeightedListSumFromAgreement :
  {S : Exact.ExactScalarOperations} →
  (laws : NatToScalarAdditive S) →
  {A : Set} →
  (scalarWeight : A → Exact.Carrier S) →
  (natWeight : A → Nat) →
  ((x : A) → scalarWeight x ≡ Exact.natToScalar S (natWeight x)) →
  (xs : List A) →
  Exact.weightedListSum {S = S} scalarWeight xs ≡
  Exact.natToScalar S (natListSum natWeight xs)
natToScalarWeightedListSumFromAgreement
  laws scalarWeight natWeight agreement xs =
  trans
    (weightedListSumCong agreement xs)
    (natToScalarWeightedListSum laws natWeight xs)
