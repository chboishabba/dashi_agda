module DASHI.Mathematics.NumberTheory.FiniteDivisorSumBoundExact where

------------------------------------------------------------------------
-- FINITE DIVISOR-SUM GROWTH BOUND
--
-- This is deliberately coarse but exact:
--
--   sigma1(n) <= n^2.
--
-- It is proved from the same executable positive-divisor list already used by
-- the Hecke/partition lane.  No real analysis, harmonic estimates or
-- asymptotics enter here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.List.Base using (filter)
import Data.List.Relation.Unary.All as All
open import Data.Nat.Base using (_≤_; z≤n)
open import Data.Nat.Divisibility using (_∣?_)
import Data.Nat.Properties as NatP
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as Hecke
import DASHI.Mathematics.NumberTheory.FiniteDependentPairCardinalityExact as Card
import DASHI.Mathematics.NumberTheory.FiniteDivisorSumExact as Divisor
import DASHI.Mathematics.NumberTheory.FiniteOneToEnumerationExact as OneTo
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex

------------------------------------------------------------------------
-- Exact length of the shared positive prefix 1,...,n.

oneToLength : (n : Nat) → Reindex.listLength (Hecke.oneTo n) ≡ n
oneToLength zero = refl
oneToLength (suc n) =
  trans
    (Card.appendLength (Hecke.oneTo n) (suc n ∷ []))
    (cong suc (oneToLength n))

------------------------------------------------------------------------
-- Drop the positive-coordinate component from the existing oneTo bounds.

upperBoundsOnly :
  ∀ {n : Nat} {candidates : List Nat} →
  All.All (λ d → (suc zero ≤ d) × (d ≤ n)) candidates →
  All.All (λ d → d ≤ n) candidates
upperBoundsOnly All.[] = All.[]
upperBoundsOnly (All._∷_ bounds rest) =
  All._∷_ (proj₂ bounds) (upperBoundsOnly rest)

------------------------------------------------------------------------
-- Filtering a bounded candidate list by divisibility cannot make its element
-- sum exceed bound * original length.

divisorFilteredFoldBound :
  (n : Nat) →
  (candidates : List Nat) →
  All.All (λ d → d ≤ n) candidates →
  Reindex.foldNat (λ d → d)
    (filter (λ d → d ∣? n) candidates)
  ≤ n * Reindex.listLength candidates
divisorFilteredFoldBound n [] All.[] = z≤n
divisorFilteredFoldBound n (d ∷ ds) (All._∷_ d≤n rest)
  with d ∣? n
... | yes dividesProof =
  NatP.+-mono
    d≤n
    (divisorFilteredFoldBound n ds rest)
... | no notDivides =
  NatP.≤-trans
    (divisorFilteredFoldBound n ds rest)
    tailBelowNext
  where
  tail : Nat
  tail = n * Reindex.listLength ds

  tailBelowNext : tail ≤ n + tail
  tailBelowNext =
    NatP.≤-trans
      (NatP.m≤m+n tail n)
      (NatP.≤-reflexive (NatP.+-comm tail n))

------------------------------------------------------------------------
-- Every oneTo candidate is at most n, hence sigma1(n) <= n*n.

sigma1QuadraticBound : (n : Nat) → Divisor.sigma1 n ≤ n * n
sigma1QuadraticBound n =
  subst
    (λ length → Divisor.sigma1 n ≤ n * length)
    (oneToLength n)
    (divisorFilteredFoldBound
      n
      (Hecke.oneTo n)
      (upperBoundsOnly (OneTo.oneToAllBounds n)))

------------------------------------------------------------------------
-- This is only a finite coarse envelope.  The sharp average order and the
-- exponential partition estimates remain downstream analytic statements.
------------------------------------------------------------------------
