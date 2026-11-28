module DASHI.Mathematics.Complexity.PNPF3SyndromeBoundaryExact where

-- Original F3 field, not cyclic carry mod 3^r. The source fibre is kept
-- as a dependent witness; the syndrome table counts these lifts.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Base369 using (TriTruth; tri-low; tri-mid; tri-high)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans; sym)
import DASHI.Foundations.Base369TriTruthField as F
import DASHI.Foundations.FiniteLinear.F3Subspace as L

V : Nat → Set
V n = Vec TriTruth n

zeroV : ∀ n → V n
zeroV zero = []
zeroV (suc n) = F.triZero ∷ zeroV n

addV : ∀ {n} → V n → V n → V n
addV [] [] = []
addV (x ∷ xs) (y ∷ ys) = F.triAdd x y ∷ addV xs ys

scaleV : ∀ {n} → TriTruth → V n → V n
scaleV a [] = []
scaleV a (x ∷ xs) = F.triMul a x ∷ scaleV a xs

negV : ∀ {n} → V n → V n
negV [] = []
negV (x ∷ xs) = F.triNeg x ∷ negV xs

minusV : ∀ {n} → V n → V n → V n
minusV t s = addV (negV s) t

zeroAdd : ∀ n → addV (zeroV n) (zeroV n) ≡ zeroV n
zeroAdd zero = refl
zeroAdd (suc n) = cong (F.triZero ∷_) (zeroAdd n)

zeroScale : ∀ n a → scaleV a (zeroV n) ≡ zeroV n
zeroScale zero a = refl
zeroScale (suc n) a = cong₂ _∷_ (F.triMul-zeroʳ a) (zeroScale n a)

syndromeSpace : Nat → L.F3Space
syndromeSpace n = record
  { Carrier = V n ; zero = zeroV n ; add = addV ; scale = scaleV
  ; addZeroZero = zeroAdd n ; scaleZero = zeroScale n }

cancelTrit : ∀ x y → F.triAdd (F.triNeg x) (F.triAdd x y) ≡ y
cancelTrit x y = trans (F.triAdd-assoc (F.triNeg x) x y)
  (trans (cong (λ a → F.triAdd a y) (F.triAdd-inverseˡ x))
    (F.triAdd-identityˡ y))

restoreTrit : ∀ x t → F.triAdd x (F.triAdd (F.triNeg x) t) ≡ t
restoreTrit x t = trans (F.triAdd-assoc x (F.triNeg x) t)
  (trans (cong (λ a → F.triAdd a t) (F.triAdd-inverseʳ x))
    (F.triAdd-identityˡ t))

cancelV : ∀ {n} (x y : V n) → minusV (addV x y) x ≡ y
cancelV [] [] = refl
cancelV (x ∷ xs) (y ∷ ys) = cong₂ _∷_ (cancelTrit x y) (cancelV xs ys)

restoreV : ∀ {n} (x t : V n) → addV x (minusV t x) ≡ t
restoreV [] [] = refl
restoreV (x ∷ xs) (t ∷ ts) = cong₂ _∷_ (restoreTrit x t) (restoreV xs ts)

uniqueRight : ∀ {n} {s t u : V n} → addV s t ≡ u → t ≡ minusV u s
uniqueRight {s = s} {t = t} refl = sym (cancelV s t)

-- Subspace membership is necessary for every original source pair.
-- Linear map image owners remain the existing F3Subspace API.
Boundary : ∀ {n} → L.F3Subspace (syndromeSpace n) →
  L.F3Subspace (syndromeSpace n) → V n → V n → Set
Boundary U W target s = L.Member U s × L.Member W (minusV target s)

imageBoundary : ∀ {n} {A B : L.F3Space}
  (f : L.F3LinearMap A (syndromeSpace n))
  (g : L.F3LinearMap B (syndromeSpace n))
  (x : L.Carrier A) (y : L.Carrier B) (target : V n) →
  addV (L.apply f x) (L.apply g y) ≡ target →
  Boundary (L.imageSubspace f) (L.imageSubspace g) target (L.apply f x)
imageBoundary f g x y target eq =
  L.imageMember x refl , L.imageMember y (uniqueRight eq)

module Source {n : Nat} {A B : Set} (left : A → V n) (right : B → V n)
              (target : V n) where
  Compatible : Set
  Compatible = Σ A (λ x → Σ B (λ y → addV (left x) (right y) ≡ target))

  Fibred : Set
  Fibred = Σ (V n) (λ s → Σ A (λ x → Σ B (λ y →
    (left x ≡ s) × (right y ≡ minusV target s))))

  split : Compatible → Fibred
  split (x , y , eq) = left x , x , y , refl , uniqueRight eq

  join : Fibred → Compatible
  join (s , x , y , lx , ry) = x , y ,
    trans (cong₂ addV lx ry) (restoreV s target)

  -- Original witnesses recovered exactly, not merely their syndromes.
  original : Compatible → A × B
  original (x , y , _) = x , y

  originalRoundtrip : ∀ p → original (join (split p)) ≡ original p
  originalRoundtrip (x , y , _) = refl

  labelled : Fibred → V n × (A × B)
  labelled (s , x , y , _) = s , x , y

  labelRoundtrip : ∀ p → labelled (split (join p)) ≡ labelled p
  labelRoundtrip (s , x , y , lx , ry) =
    cong (λ t → t , x , y) lx

-- A finite list/table implementation still needs native RREF and count
-- reification. This theorem pays the exact BIDI fibre partition only.

-- Reuse the previous rational character carrier. The retained-retained
-- term and the three omitted products are the exact four source pieces.
open import Data.Rational.Base using (ℚ; _+_; _*_)
open import Data.List.Base as List using ()
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Mathematics.Complexity.PNPSignedCharacterTailExact as H

hadd : H.Hist → H.Hist → H.Hist
hadd (H.hist a b c) (H.hist d e f) = H.hist (a + d) (b + e) (c + f)

mass : H.Hist → ℚ
mass (H.hist a b c) = a + b + c

massAdd : ∀ h k → mass (hadd h k) ≡ mass h + mass k
massAdd (H.hist a b c) (H.hist d e f) =
  solve (a List.∷ b List.∷ c List.∷ d List.∷ e List.∷ f List.∷ List.[])

massProduct : ∀ h k → mass (H.conv h k) ≡ mass h * mass k
massProduct (H.hist a b c) (H.hist d e f) =
  solve (a List.∷ b List.∷ c List.∷ d List.∷ e List.∷ f List.∷ List.[])

omitted : H.Hist → H.Hist → H.Hist → H.Hist → H.Hist
omitted h j p q = hadd (H.conv h q) (hadd (H.conv p j) (H.conv p q))

productPartition : ∀ h j p q →
  H.conv (hadd h p) (hadd j q) ≡ hadd (H.conv h j) (omitted h j p q)
productPartition (H.hist a b c) (H.hist d e f) (H.hist g h i) (H.hist j k l) =
  H.histEq (solve vars) (solve vars) (solve vars)
  where vars = a List.∷ b List.∷ c List.∷ d List.∷ e List.∷ f List.∷
               g List.∷ h List.∷ i List.∷ j List.∷ k List.∷ l List.∷ List.[]

omittedMass : ∀ h j p q →
  mass (omitted h j p q) ≡ mass h * mass q + mass j * mass p + mass p * mass q
omittedMass h j p q
  rewrite massAdd (H.conv h q) (hadd (H.conv p j) (H.conv p q))
        | massAdd (H.conv p j) (H.conv p q)
        | massProduct h q | massProduct p j | massProduct p q =
  solve (mass h List.∷ mass j List.∷ mass p List.∷ mass q List.∷ List.[])
