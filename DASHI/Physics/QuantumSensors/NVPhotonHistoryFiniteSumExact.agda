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
