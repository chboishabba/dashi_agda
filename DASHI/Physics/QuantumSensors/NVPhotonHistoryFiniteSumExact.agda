module DASHI.Physics.QuantumSensors.NVPhotonHistoryFiniteSumExact where

-- Exact all-words mass recursion for the MCG Bernoulli product law.
-- Reuses the existing photon likelihood and finite history semantics.

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_; _++_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (trans)
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Physics.QuantumSensors.NVPhotonBinaryLikelihoodExact as Photon
import DASHI.Physics.QuantumSensors.NVPhotonTwoShotKernelExact as Two
import DASHI.Physics.QuantumSensors.NVPhotonHistoryLikelihoodExact as Hist
import DASHI.Physics.QuantumSensors.NVPhotonHistoryNormalizationExact as Tree

prepend : Two.PhotonBit → List Hist.History → List Hist.History
prepend bit [] = []
prepend bit (x ∷ xs) = (bit ∷ x) ∷ prepend bit xs

words : Nat → List Hist.History
words zero = [] ∷ []
words (suc n) =
  prepend Two.click (words n) ++ prepend Two.dark (words n)

sum : List ℚ → ℚ
sum [] = 0ℚ
sum (x ∷ xs) = x + sum xs

mass : Photon.BinaryPhotonLikelihood → List Hist.History → ℚ
mass p [] = 0ℚ
mass p (x ∷ xs) = Hist.historyLikelihood p x + mass p xs

-- Explicitly enumerated normalized mass is connected to the already
-- verified binary tree by separately proving generic finite-list
-- distributivity and prefix recursion. No claim is made that this
-- final commuting-square lemma is discharged yet.

-- Generic finite-list sum decomposition.
massAppend :
  (p : Photon.BinaryPhotonLikelihood)
  (xs ys : List Hist.History) →
  mass p (xs ++ ys) ≡ mass p xs + mass p ys
massAppend p [] ys = refl
massAppend p (x ∷ xs) ys
  rewrite massAppend p xs ys =
  solve (Hist.historyLikelihood p x ∷ mass p xs ∷ mass p ys ∷ [])

-- Common scalar factor distributes through finite enumeration.
massPrepend :
  (p : Photon.BinaryPhotonLikelihood)
  (bit : Two.PhotonBit)
  (xs : List Hist.History) →
  mass p (prepend bit xs) ≡ Two.weight p bit * mass p xs
massPrepend p bit [] = refl
massPrepend p bit (x ∷ xs)
  rewrite massPrepend p bit xs =
  solve (Two.weight p bit ∷ Hist.historyLikelihood p x ∷ mass p xs ∷ [])

-- A commuting square between actual listed histories and binary-tree
-- recursion: both are exactly the same conditional product law.
listedMassEqualsTree :
  (p : Photon.BinaryPhotonLikelihood) (n : Nat) →
  mass p (words n) ≡ Tree.treeMass p n
listedMassEqualsTree p zero = refl
listedMassEqualsTree p (suc n)
  rewrite massAppend p (prepend Two.click (words n))
                       (prepend Two.dark (words n))
        | massPrepend p Two.click (words n)
        | massPrepend p Two.dark (words n)
        | listedMassEqualsTree p n = refl

-- The finite sum over all 2^n histories now inherits the one-shot
-- Bernoulli normalization of the source-owned MCG model.
listedMassNormalized :
  (p : Photon.BinaryPhotonLikelihood) (n : Nat) →
  mass p (words n) ≡ 1ℚ
listedMassNormalized p n =
  trans (listedMassEqualsTree p n) (Tree.treeMassNormalized p n)
