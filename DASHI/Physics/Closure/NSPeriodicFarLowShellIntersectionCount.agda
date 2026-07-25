module DASHI.Physics.Closure.NSPeriodicFarLowShellIntersectionCount where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literal supported-shell intersection and its safe cardinality bound.
------------------------------------------------------------------------

filterBy : ∀ {i} {A : Set i} → (A → Bool) → List A → List A
filterBy predicate [] = []
filterBy predicate (x ∷ xs) with predicate x
... | true = x ∷ filterBy predicate xs
... | false = filterBy predicate xs

length : ∀ {i} {A : Set i} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

data _≤count_ : Nat → Nat → Set where
  zero≤ : ∀ {n} → zero ≤count n
  suc≤suc : ∀ {m n} → m ≤count n → suc m ≤count suc n

filterLengthAtMostOriginal :
  ∀ {i} {A : Set i} (predicate : A → Bool) →
  ∀ items → length (filterBy predicate items) ≤count length items
filterLengthAtMostOriginal predicate [] = zero≤
filterLengthAtMostOriginal predicate (x ∷ xs) with predicate x
... | true = suc≤suc (filterLengthAtMostOriginal predicate xs)
... | false =
  weakenRight (filterLengthAtMostOriginal predicate xs)
  where
  weakenRight : ∀ {m n} → m ≤count n → m ≤count suc n
  weakenRight zero≤ = zero≤
  weakenRight (suc≤suc proof) = suc≤suc (weakenRight proof)

shellIntersection :
  ∀ {r c : Level} {Row : Set r} {Column : Set c} →
  (Row → Column → Bool) → Row → List Column → List Column
shellIntersection support row = filterBy (support row)

shellIntersectionCountBound :
  ∀ {r c : Level} {Row : Set r} {Column : Set c} →
  (support : Row → Column → Bool) →
  ∀ row columns →
  length (shellIntersection support row columns) ≤count length columns
shellIntersectionCountBound support row columns =
  filterLengthAtMostOriginal (support row) columns

farLowShellIntersectionCountLevel : ProofLevel
farLowShellIntersectionCountLevel = machineChecked
