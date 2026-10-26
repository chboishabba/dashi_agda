module DASHI.Physics.QuantumSensors.NVPhotonHistoryNormalizationExact where

-- Finite history mass over ALL length-n bit words under the existing
-- diamond MCG normalized Bernoulli likelihood. The independence/product
-- formula is a model assumption, not a hardware calibration.

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Relation.Binary.PropositionalEquality using (trans)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Physics.QuantumSensors.NVPhotonBinaryLikelihoodExact as Photon
import DASHI.Physics.QuantumSensors.NVPhotonTwoShotKernelExact as Two
import DASHI.Physics.QuantumSensors.NVPhotonHistoryLikelihoodExact as Hist

allHistories : Nat → List Hist.History
allHistories zero = [] ∷ []
allHistories (suc n) =
  prepend Two.click (allHistories n) ++
  prepend Two.dark (allHistories n)
  where
    open import Data.List.Base using (_++_)

    prepend : Two.PhotonBit → List Hist.History → List Hist.History
    prepend bit [] = []
    prepend bit (h ∷ hs) = (bit ∷ h) ∷ prepend bit hs

sumMass : Photon.BinaryPhotonLikelihood → List Hist.History → ℚ
sumMass p [] = 0ℚ
sumMass p (h ∷ hs) =
  Hist.historyLikelihood p h + sumMass p hs

-- A generic finite-list distributivity and prepend summation witness
-- is the one remaining formal leaf before n-shot normalization.
-- No postulated theorem or boolean flag is used as a substitute.
