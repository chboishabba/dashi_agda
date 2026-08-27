module DASHI.Mathematics.NumberTheory.FiniteOneToEnumerationExact where

------------------------------------------------------------------------
-- FINITE POSITIVE PREFIX RECEIPTS
--
-- The shared Hecke helper `oneTo n` enumerates 1,...,n.  This owner records
-- the exact completeness/order facts needed by the partition residual grouping
-- layer.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (_++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.List.Relation.Unary.Any as Any using ()
import Data.List.Relation.Unary.All as All
open import Data.Nat.Base using (_≤_; _<_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Data.Product using (_×_; _,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≢_; cong; subst)

import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as Hecke
import DASHI.Mathematics.NumberTheory.FiniteProductEnumerationExact as Product

oneToUpperBound :
  ∀ {n r : Nat} → r ∈ Hecke.oneTo n → r ≤ n
oneToUpperBound {zero} ()
oneToUpperBound {suc n} {r} member
  with ∈-++⁻ (Hecke.oneTo n) member
... | inj₁ earlier =
  NatP.≤-step (oneToUpperBound earlier)
... | inj₂ (Any.here equality) =
  subst (λ value → value ≤ suc n) equality NatP.≤-refl
... | inj₂ (Any.there ())

oneToPositive :
  ∀ {n r : Nat} → r ∈ Hecke.oneTo n → suc zero ≤ r
oneToPositive {zero} ()
oneToPositive {suc n} {r} member
  with ∈-++⁻ (Hecke.oneTo n) member
... | inj₁ earlier = oneToPositive earlier
... | inj₂ (Any.here equality) =
  subst (λ value → suc zero ≤ value) equality (s≤s z≤n)
... | inj₂ (Any.there ())

oneToAllBounds :
  (n : Nat) →
  All.All (λ r → (suc zero ≤ r) × (r ≤ n)) (Hecke.oneTo n)
oneToAllBounds n =
  All.tabulate λ member →
    oneToPositive member , oneToUpperBound member

------------------------------------------------------------------------
-- Completeness of the positive prefix.

strictFromLeDifferent :
  ∀ {m n : Nat} → m ≤ n → m ≢ n → m < n
strictFromLeDifferent {zero} {zero} z≤n different =
  ⊥-elim (different refl)
strictFromLeDifferent {zero} {suc n} z≤n different = s≤s z≤n
strictFromLeDifferent {suc m} {suc n} (s≤s bound) different =
  s≤s
    (strictFromLeDifferent bound
      (λ equality → different (cong suc equality)))

oneToComplete :
  ∀ {n r : Nat} →
  suc zero ≤ r → r ≤ n → r ∈ Hecke.oneTo n
oneToComplete {zero} {r} positive bound with bound
... | ()
oneToComplete {suc n} {zero} () bound
oneToComplete {suc n} {suc r} positive bound
  with suc r NatP.≟ suc n
... | yes equality =
  Product.appendMemberRight
    (Hecke.oneTo n)
    (Any.here equality)
... | no different =
  Product.appendMemberLeft
    (oneToComplete
      positive
      (strictFromLeDifferent bound different))

------------------------------------------------------------------------
-- Pure finite list/order facts.
------------------------------------------------------------------------
