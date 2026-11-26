module DASHI.Mathematics.NumberTheory.FiniteFactorPairPowerReadoutExact where

-- SOURCE-WRITTEN, UNCOMPILED. Generalize the actual existing
-- sigma1 readout to any divisor observation without a new scan.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NP
open import Data.Empty using (⊥-elim)
open import Data.List.Base using (filter)
import Data.List.Relation.Unary.All as All
open import Data.Nat.Divisibility using (_∣_; _∣?_)
open import Data.Product.Base using (_×_)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; trans)
import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as Hecke
import DASHI.Mathematics.NumberTheory.FiniteOneToEnumerationExact as One
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as W
import DASHI.Mathematics.NumberTheory.FiniteFactorPairDivisorSumExact as F
import DASHI.Mathematics.NumberTheory.FinitePositiveFactorPairExact as P
import DASHI.Mathematics.NumberTheory.FiniteDivisorPowerSumExact as Pow
import DASHI.Mathematics.NumberTheory.FiniteDivisorSumExact as Div

factorReadoutFrom : (w : Nat → Nat) (r : Nat) (ds : List Nat) →
  W.foldNat (λ p → w (F.divisor p)) (F.factorPairsFrom r ds) ≡
  W.foldNat w (filter (λ d → d ∣? r) ds)
factorReadoutFrom w r [] = refl
factorReadoutFrom w r (d ∷ ds) with d ∣? r
... | yes h = cong (w d +_) (factorReadoutFrom w r ds)
... | no _ = factorReadoutFrom w r ds

positiveReadoutFrom : (w : Nat → Nat) (r : Nat) (pr : suc zero ≤ r)
  (ds : List Nat) (bounds : All.All (λ d → (suc zero ≤ d) × (d ≤ r)) ds) →
  W.foldNat (λ p → w (P.divisor p)) (P.positiveFactorPairsFrom r pr ds bounds) ≡
  W.foldNat (λ p → w (F.divisor p)) (F.factorPairsFrom r ds)
positiveReadoutFrom w r pr [] All.[] = refl
positiveReadoutFrom w r pr (d ∷ ds) (All._∷_ bounds rest)
  with d ∣? r
... | no _ = positiveReadoutFrom w r pr ds rest
... | yes h with _∣_.quotient h
...   | zero = ⊥-elim (P.positiveNotZero pr (trans (_∣_.equality h) refl))
...   | suc predecessor =
  cong (w d +_) (positiveReadoutFrom w r pr ds rest)

positiveDivisorReadout : (w : Nat → Nat) (r : Nat) (pr : suc zero ≤ r) →
  W.foldNat (λ p → w (P.divisor p)) (P.positiveFactorPairs r pr) ≡
  W.foldNat w (Div.positiveDivisors r)
positiveDivisorReadout w r pr =
  trans (positiveReadoutFrom w r pr (Hecke.oneTo r) (One.oneToAllBounds r))
    (factorReadoutFrom w r (Hecke.oneTo r))

positivePowerReadout : (k r : Nat) (pr : suc zero ≤ r) →
  W.foldNat (λ p → Pow.powNat (P.divisor p) k) (P.positiveFactorPairs r pr) ≡
  Pow.sigmaPower k r
positivePowerReadout k = positiveDivisorReadout (λ d → Pow.powNat d k)

sigmaPowerOne : (r : Nat) → Pow.sigmaPower 1 r ≡ Div.sigma1 r
sigmaPowerOne r = W.foldPointwise (λ d → Pow.powNat d 1) (λ d → d)
  (Div.positiveDivisors r) (λ d → NP.*-identityʳ d)
