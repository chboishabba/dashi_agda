{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21SignedGammaNumberTheoryExact where

------------------------------------------------------------------------
-- Karp N21: nontrivial SIGNED-GAMMA ARITHMETIC on source zigzag ℤ.
--
-- n+1 = 2M+1  => n=2M     => unzigzag(n) = +M
-- n+1 = 2M    => n=2M-1   => unzigzag(n) = -M  (M>=1).
--
-- Proved by the ORIGINAL zigzag twice/unzigzag definitions, including
-- the negative successor correction. This is a genuine arithmetic
-- lemma (not a guard/acceptance wrapper). The separate task of showing
-- that native Value.valueLE(reverse bits)=M is not smuggled in.
--
-- Source: DASHI original signed Karp gamma decoder (zigzag, twice,
-- unzigzag, unzigzagZigzag). Primary attribution: Elias, Karp.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_∸_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (ℤ; +_; -[1+_])
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Old

-- Gamma numeral (n+1) ending with a set bit represents the original
-- zigzag even index n=2M, hence the original nonnegative integer M.
positiveSuccessorZigzagNumerical :
  (magnitude : Nat) →
  Old.unzigzag
    (suc (Old.twice magnitude) ∸ suc zero)
    ≡ + magnitude
positiveSuccessorZigzagNumerical magnitude =
  Old.unzigzagZigzag (+ magnitude)

-- The negative gamma(n) successor numeral is 2(suc k), NOT
-- 2k or 2k+1. Its predecessor is exactly 2k+1 and represents
-- original integer -(k+1).
negativeSuccessorPredecessor :
  (k : Nat) →
  Old.twice (suc k) ∸ suc zero
    ≡ suc (Old.twice k)
negativeSuccessorPredecessor k = refl

negativeSuccessorZigzagNumerical :
  (k : Nat) →
  Old.unzigzag
    (Old.twice (suc k) ∸ suc zero)
    ≡ -[1+ k ]
negativeSuccessorZigzagNumerical k =
  trans
    (cong Old.unzigzag (negativeSuccessorPredecessor k))
    (Old.unzigzagZigzag (-[1+ k ]))

-- An explicitly positive magnitude can be represented as suc k.
-- This is the exact correction to sign-magnitude decoding:
-- for a gamma-successor numeral 2M, the original integer is -M,
-- and no negative-zero token is possible on this branch.
