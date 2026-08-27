module DASHI.Mathematics.NumberTheory.FiniteOneToEnumerationExact where

------------------------------------------------------------------------
-- FINITE POSITIVE PREFIX RECEIPTS
--
-- The shared Hecke helper `oneTo n` enumerates 1,...,n.  This owner records
-- the order facts needed by the partition residual grouping layer.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using (_++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.List.Relation.Unary.Any as Any using ()
import Data.List.Relation.Unary.All as All
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Data.Product using (_×_; _,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as Hecke

oneToUpperBound :
  ∀ {n r : Nat} → r ∈ Hecke.oneTo n → r ≤ n
oneToUpperBound {zero} ()
oneToUpperBound {suc n} {r} member
  with ∈-++⁻ (Hecke.oneTo n) member
... | inj₁ earlier =
  NatP.≤-step (oneToUpperBound earlier)
... | inj₂ (Any.here equality) =
  subst (λ value → value ≤ suc n) equality (NatP.≤-refl)
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
-- Pure finite list/order facts.
------------------------------------------------------------------------
