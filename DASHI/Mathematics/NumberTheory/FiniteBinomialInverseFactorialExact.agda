module DASHI.Mathematics.NumberTheory.FiniteBinomialInverseFactorialExact where

------------------------------------------------------------------------
-- FINITE BINOMIAL / INVERSE-FACTORIAL COEFFICIENT IDENTITY
--
-- For k <= n,
--
--   C(n,k) * k! * (n-k)! = n!
--
-- and hence, in the unnormalised rational carrier used by vendor/bishop,
--
--   1/k! * 1/(n-k)! = C(n,k) * 1/n!.
--
-- The Nat theorem is entirely stdlib reuse:
--   Data.Nat.Combinatorics.nCk≡n!/k![n-k]!
--   Data.Nat.Combinatorics.k![n∸k]!∣n!
--   Data.Nat.DivMod.m*[n/m]≡n.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Integer.Base using (+_)
open import Data.Nat.Base using (_≤_; _∸_; _!; NonZero)
import Data.Nat.Combinatorics as Comb
open import Data.Nat.Divisibility using (_∣_)
open import Data.Nat.DivMod using (_/_; m*[n/m]≡n)
import Data.Nat.Properties as NatP
open import Data.Rational.Unnormalised as ℚ using (_/_; _*_; _≃_)
open import Data.Rational.Unnormalised.Properties using (*≡*)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

chooseFactorialProduct :
  ∀ {n k : Nat} →
  k ≤ n →
  (n Comb.C k) * (k ! * (n ∸ k) !) ≡ n !
chooseFactorialProduct {n} {k} k≤n =
  let
    denominator = k ! * (n ∸ k) !

    denominatorDivides : denominator ∣ n !
    denominatorDivides = Comb.k![n∸k]!∣n! k≤n

    chooseAsQuotient :
      n Comb.C k ≡ n ! / denominator
    chooseAsQuotient = Comb.nCk≡n!/k![n-k]! k≤n

    reconstructed :
      denominator * (n ! / denominator) ≡ n !
    reconstructed = m*[n/m]≡n denominatorDivides
  in
  trans
    (cong (λ value → value * denominator) chooseAsQuotient)
    (trans
      (NatP.*-comm (n ! / denominator) denominator)
      reconstructed)

inverseFactorialProductBinomial :
  ∀ {n k : Nat} →
  k ≤ n →
  ((+ 1 / k !) ℚ.* (+ 1 / (n ∸ k) !))
  ℚ.≃
  ((+ (n Comb.C k) / 1) ℚ.* (+ 1 / n !))
inverseFactorialProductBinomial {n} {k} k≤n =
  *≡* (cong +_ (sym (chooseFactorialProduct k≤n)))

finiteBinomialInverseFactorialLevel : ProofLevel
finiteBinomialInverseFactorialLevel = machineChecked
