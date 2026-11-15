module DASHI.Physics.QuantumSensors.NVPhotonHistoryLikelihoodExact where

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _*_)
import DASHI.Physics.QuantumSensors.NVPhotonBinaryLikelihoodExact as Photon
import DASHI.Physics.QuantumSensors.NVPhotonTwoShotKernelExact as Two

History : Set
History = List Two.PhotonBit

historyLikelihood : Photon.BinaryPhotonLikelihood → History → ℚ
historyLikelihood p [] = 1ℚ
historyLikelihood p (x ∷ xs) = Two.weight p x * historyLikelihood p xs

sameKernelSameHistory :
  (p q : Photon.BinaryPhotonLikelihood) →
  (∀ x → Two.weight p x ≡ Two.weight q x) →
  (xs : History) → historyLikelihood p xs ≡ historyLikelihood q xs
sameKernelSameHistory p q equal [] = refl
sameKernelSameHistory p q equal (x ∷ xs)
  rewrite equal x | sameKernelSameHistory p q equal xs = refl

sameKernelSameStatistic :
  (p q : Photon.BinaryPhotonLikelihood) →
  (∀ x → Two.weight p x ≡ Two.weight q x) →
  (xs : History) (f : ℚ → ℚ) →
  f (historyLikelihood p xs) ≡ f (historyLikelihood q xs)
sameKernelSameStatistic p q eq xs f =
  cong f (sameKernelSameHistory p q eq xs)
