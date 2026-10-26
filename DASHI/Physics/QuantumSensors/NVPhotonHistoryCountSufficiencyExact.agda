module DASHI.Physics.QuantumSensors.NVPhotonHistoryCountSufficiencyExact where

-- Source-native sufficient statistic for i.i.d. binary NV photon histories:
-- equal click/dark counts entail equal rational likelihood.
-- Mathematical statement only; no measured independence claim.

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Physics.QuantumSensors.NVPhotonBinaryLikelihoodExact as Photon
import DASHI.Physics.QuantumSensors.NVPhotonTwoShotKernelExact as Two
import DASHI.Physics.QuantumSensors.NVPhotonHistoryLikelihoodExact as Hist

clicks : Hist.History → Nat
clicks [] = zero
clicks (Two.click ∷ xs) = suc (clicks xs)
clicks (Two.dark ∷ xs) = clicks xs

darks : Hist.History → Nat
darks [] = zero
darks (Two.click ∷ xs) = darks xs
darks (Two.dark ∷ xs) = suc (darks xs)

-- Product powers are defined without importing another binomial algebra.
power : ℚ → Nat → ℚ
power x zero = 1ℚ
power x (suc n) = x * power x n

-- This is the target count-class factorisation; associativity and
-- commutativity are witnessed by the existing rational ring solver.
likelihoodByCounts : Photon.BinaryPhotonLikelihood → Hist.History → ℚ
likelihoodByCounts p xs =
  power (Photon.photon p) (clicks xs) *
  power (Photon.noPhoton p) (darks xs)

-- For one or two observations the factorisation is definitional or
-- an ordinary commutativity identity. General induction uses rational
-- associativity and is the future reusable theorem target.
emptyFactorisation :
  (p : Photon.BinaryPhotonLikelihood) →
  Hist.historyLikelihood p [] ≡ likelihoodByCounts p []
emptyFactorisation p = refl

oneClickFactorisation :
  (p : Photon.BinaryPhotonLikelihood) →
  Hist.historyLikelihood p (Two.click ∷ []) ≡
  likelihoodByCounts p (Two.click ∷ [])
oneClickFactorisation p =
  solve (Photon.photon p ∷ Photon.noPhoton p ∷ [])

oneDarkFactorisation :
  (p : Photon.BinaryPhotonLikelihood) →
  Hist.historyLikelihood p (Two.dark ∷ []) ≡
  likelihoodByCounts p (Two.dark ∷ [])
oneDarkFactorisation p =
  solve (Photon.photon p ∷ Photon.noPhoton p ∷ [])

-- Full finite-history sufficient statistic: the same number of clicks
-- and dark outcomes determines the full conditional product likelihood.
generalCountFactorisation :
  (p : Photon.BinaryPhotonLikelihood) (xs : Hist.History) →
  Hist.historyLikelihood p xs ≡ likelihoodByCounts p xs
generalCountFactorisation p [] = refl
generalCountFactorisation p (Two.click ∷ xs)
  rewrite generalCountFactorisation p xs =
  solve (Photon.photon p ∷
         power (Photon.photon p) (clicks xs) ∷
         power (Photon.noPhoton p) (darks xs) ∷ [])
generalCountFactorisation p (Two.dark ∷ xs)
  rewrite generalCountFactorisation p xs =
  solve (Photon.noPhoton p ∷
         power (Photon.photon p) (clicks xs) ∷
         power (Photon.noPhoton p) (darks xs) ∷ [])

sameCountsSameLikelihood :
  (p : Photon.BinaryPhotonLikelihood) (xs ys : Hist.History) →
  clicks xs ≡ clicks ys →
  darks xs ≡ darks ys →
  Hist.historyLikelihood p xs ≡ Hist.historyLikelihood p ys
sameCountsSameLikelihood p xs ys sameClicks sameDarks
  rewrite generalCountFactorisation p xs
        | generalCountFactorisation p ys
        | sameClicks | sameDarks = refl
