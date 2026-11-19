{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayOriginalConnectingChargeSectorWeldExact where

-- Attachment to the original CMP116 connecting charge sum.
-- No alternate cluster family or effective action. Sector classification
-- is supplied by the actual C2/Step V support dictionary.
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _≤_)
import Data.Rational.Properties as Q
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (subst; sym; cong)
import DASHI.Physics.YangMills.BalabanClayT5TwoMarkedConnectedClusterTailExact as T

data Sector : Set where
  small large mixed : Sector

smallCharge : ∀ {A : Set} → (A → Sector) → (A → ℚ) → List A → ℚ
smallCharge tag w [] = 0ℚ
smallCharge tag w (a ∷ as) with tag a
... | small = w a + smallCharge tag w as
... | large = smallCharge tag w as
... | mixed = smallCharge tag w as

largeCharge : ∀ {A : Set} → (A → Sector) → (A → ℚ) → List A → ℚ
largeCharge tag w [] = 0ℚ
largeCharge tag w (a ∷ as) with tag a
... | small = largeCharge tag w as
... | large = w a + largeCharge tag w as
... | mixed = largeCharge tag w as

mixedCharge : ∀ {A : Set} → (A → Sector) → (A → ℚ) → List A → ℚ
mixedCharge tag w [] = 0ℚ
mixedCharge tag w (a ∷ as) with tag a
... | small = mixedCharge tag w as
... | large = mixedCharge tag w as
... | mixed = w a + mixedCharge tag w as

sectorChargeSum : ∀ {A : Set} (tag : A → Sector) (w : A → ℚ) (as : List A) →
  T.sumℚ (T.map w as) ≡ (smallCharge tag w as + largeCharge tag w as) + mixedCharge tag w as
sectorChargeSum tag w [] = Ring.solve-∀
sectorChargeSum tag w (a ∷ as) with tag a
... | small rewrite sectorChargeSum tag w as =
  Ring.solve-∀ (w a) (smallCharge tag w as) (largeCharge tag w as) (mixedCharge tag w as)
... | large rewrite sectorChargeSum tag w as =
  Ring.solve-∀ (w a) (smallCharge tag w as) (largeCharge tag w as) (mixedCharge tag w as)
... | mixed rewrite sectorChargeSum tag w as =
  Ring.solve-∀ (w a) (smallCharge tag w as) (largeCharge tag w as) (mixedCharge tag w as)

sectorChargeBelowShell : ∀ {A : Set} (tag : A → Sector) (w : A → ℚ) (as : List A)
  (s l m shell : ℚ) →
  smallCharge tag w as ≤ s →
  largeCharge tag w as ≤ l →
  mixedCharge tag w as ≤ m →
  (s + l) + m ≤ shell →
  T.sumℚ (T.map w as) ≤ shell
sectorChargeBelowShell tag w as s l m shell ps pl pm budget =
  subst (λ v → v ≤ shell) (sym (sectorChargeSum tag w as))
    (Q.≤-trans (Q.+-mono-≤ (Q.+-mono-≤ ps pl) pm) budget)

-- Instantiate as with BalabanLiteralTwoWilsonCMP116ConnectingTailExact.connectingClusters
-- and w with BalabanLiteralTwoWilsonMarkedPolymerExpansionExact.shellCharge.
-- The physical tag and three sector estimates are NOT constructed here.
