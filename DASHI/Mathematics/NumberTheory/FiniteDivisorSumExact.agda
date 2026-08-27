module DASHI.Mathematics.NumberTheory.FiniteDivisorSumExact where

------------------------------------------------------------------------
-- EXECUTABLE FIRST DIVISOR SUM
--
-- REPO CROSS-POLLINATION
-- `ClassicalHeckeWeightKSmallWordExact` already owns an executable positive
-- divisor enumeration for Hecke products.  Reuse that finite arithmetic here
-- instead of introducing a second divisibility scanner.
--
-- sigma1(n) = sum_{d | n, d>0} d.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (filter)
open import Data.Nat.Divisibility using (_∣?_)

import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as Hecke
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex

positiveDivisors : Nat → List Nat
positiveDivisors n = filter (λ d → d ∣? n) (Hecke.oneTo n)

sigma1 : Nat → Nat
sigma1 n = Reindex.foldNat (λ d → d) (positiveDivisors n)

------------------------------------------------------------------------
-- Small exact regressions.

sigma1Zero : sigma1 0 ≡ 0
sigma1Zero = refl

sigma1One : sigma1 1 ≡ 1
sigma1One = refl

sigma1Two : sigma1 2 ≡ 3
sigma1Two = refl

sigma1Three : sigma1 3 ≡ 4
sigma1Three = refl

sigma1Four : sigma1 4 ≡ 7
sigma1Four = refl

sigma1Five : sigma1 5 ≡ 6
sigma1Five = refl

sigma1Six : sigma1 6 ≡ 12
sigma1Six = refl

------------------------------------------------------------------------
-- This owner is finite arithmetic only.  Multiplicativity, Dirichlet series,
-- modular forms, and analytic estimates remain separate theorem layers.
------------------------------------------------------------------------
