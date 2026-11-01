module DASHI.Physics.RealOperators where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Data.Vec using (Vec; []; _∷_; map)
open import Data.Vec.Base using (reverse)
open import Data.Vec.Properties using (map-reverse; reverse-involutive)
open import DASHI.Algebra.Trit using (Trit; zer; inv; neg; pos)
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Metric.FineAgreementUltrametric as FAM
open import DASHI.Metric.AgreementUltrametric as AM
open import Ultrametric as UMetric
open import DASHI.Geometry.StrictContractionComposition as SCC
open import Data.Nat using (_≤_; _≥_; z≤n)
open import Data.Nat.Properties as NatP

------------------------------------------------------------------------
-- Tail is fine detail: projection zeroes the last digit.
------------------------------------------------------------------------

setHead : ∀ {n : Nat} → Vec Trit (suc n) → Vec Trit (suc n)
setHead (_ ∷ xs) = zer ∷ xs

Pᵣ : ∀ {n : Nat} → RTC.Carrier n → RTC.Carrier n
Pᵣ {zero} [] = []
Pᵣ {suc n} x = reverse (setHead (reverse x))

-- Canonicalization / renormalization.
-- Minimal nontrivial instance: canonicalize by projecting away the last digit.
-- This keeps the change localized while staying nonexpansive under FAM.
Cᵣ : ∀ {n : Nat} → RTC.Carrier n → RTC.Carrier n
Cᵣ = Pᵣ

Rᵣ : ∀ {n : Nat} → RTC.Carrier n → RTC.Carrier n
Rᵣ x = x

------------------------------------------------------------------------
-- Involution commutation lemmas for Pᵣ.
------------------------------------------------------------------------

setHead-inv : ∀ {n : Nat} (xs : Vec Trit (suc n)) →
  map inv (setHead xs) ≡ setHead (map inv xs)
setHead-inv (x ∷ xs) = refl

invVec-Pᵣ : ∀ {n : Nat} (x : RTC.Carrier n) →
  RTC.invVec (Pᵣ x) ≡ Pᵣ (RTC.invVec x)
invVec-Pᵣ {zero} [] = refl
invVec-Pᵣ {suc n} x =
  let
    rx = reverse x
  in
  trans
    (map-reverse inv (setHead rx))
    (trans
      (cong reverse (setHead-inv rx))
      (cong (λ v → reverse (setHead v)) (map-reverse inv x))
    )

------------------------------------------------------------------------
-- Nonexpansive proofs under the fine agreement metric.
------------------------------------------------------------------------

agreeDepthFine-nondecrease :
  ∀ {n : Nat} (x y : RTC.Carrier n) →
  FAM.agreeDepthFine (Pᵣ x) (Pᵣ y) ≥ FAM.agreeDepthFine x y
agreeDepthFine-nondecrease {zero} [] [] = z≤n
agreeDepthFine-nondecrease {suc n} x y
  rewrite reverse-involutive (setHead (reverse x))
        | reverse-involutive (setHead (reverse y))
  = lemma (reverse x) (reverse y)
  where
    lemma : ∀ {m} (rx ry : Vec Trit (suc m)) →
      AM.agreeDepth (setHead rx) (setHead ry) ≥ AM.agreeDepth rx ry
    lemma (neg ∷ as) (neg ∷ bs) = NatP.≤-refl
    lemma (zer ∷ as) (zer ∷ bs) = NatP.≤-refl
    lemma (pos ∷ as) (pos ∷ bs) = NatP.≤-refl
    lemma (neg ∷ as) (zer ∷ bs) = z≤n
    lemma (neg ∷ as) (pos ∷ bs) = z≤n
    lemma (zer ∷ as) (neg ∷ bs) = z≤n
    lemma (zer ∷ as) (pos ∷ bs) = z≤n
    lemma (pos ∷ as) (neg ∷ bs) = z≤n
    lemma (pos ∷ as) (zer ∷ bs) = z≤n

nonexpPᵣ : ∀ {n : Nat} → SCC.NonExpansive (FAM.ultrametricVec {n = n}) (Pᵣ {n})
nonexpPᵣ {n} =
  record
    { nonexp = λ x y →
        let
          depth≥ = agreeDepthFine-nondecrease x y
        in
        NatP.∸-mono (NatP.≤-refl {n}) depth≥
    }

nonexpCᵣ : ∀ {n : Nat} → SCC.NonExpansive (FAM.ultrametricVec {n = n}) (Cᵣ {n})
nonexpCᵣ {n} = nonexpPᵣ {n}

nonexpRᵣ : ∀ {n : Nat} → SCC.NonExpansive (FAM.ultrametricVec {n = n}) (Rᵣ {n})
nonexpRᵣ {n} = record { nonexp = λ _ _ → NatP.≤-refl }
