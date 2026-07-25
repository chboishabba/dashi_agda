module DASHI.Physics.Closure.NSPeriodicFarHighTailReindexing where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Relation.Binary.PropositionalEquality using (cong)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSPeriodicFarHighFiniteTail as Tail
import DASHI.Physics.Closure.NSPeriodicFiniteWeightedSchurKernel as Fold
open import DASHI.Physics.YangMills.CompactLieProofLevel

map : ∀ {i j} {A : Set i} {B : Set j} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

mapTailSuccessor : ∀ start count →
  map suc (Tail.tailIndices start count) ≡ Tail.tailIndices (suc start) count
mapTailSuccessor start zero = refl
mapTailSuccessor start (suc count) =
  cong (λ rest → suc start ∷ rest)
    (mapTailSuccessor (suc start) count)

sumByMap :
  ∀ {i j} {A : AbsorptionArithmetic} {X : Set i} {Y : Set j} →
  (f : X → Y) → (term : Y → Scalar A) →
  ∀ xs → Fold.sumBy term (map f xs) ≡ Fold.sumBy (λ x → term (f x)) xs
sumByMap f term [] = refl
sumByMap {A = A} f term (x ∷ xs) =
  cong (λ tail → _+_ A (term (f x)) tail) (sumByMap f term xs)

finiteTailSuccessorReindex :
  ∀ {A : AbsorptionArithmetic} (term : Nat → Scalar A) start count →
  Tail.finiteTail term (suc start) count ≡
  Fold.sumBy (λ n → term (suc n)) (Tail.tailIndices start count)
finiteTailSuccessorReindex term start count =
  transEq
    (cong (Fold.sumBy term) (symEq (mapTailSuccessor start count)))
    (sumByMap suc term (Tail.tailIndices start count))
  where
  symEq : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
  symEq refl = refl

  transEq : ∀ {X : Set} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
  transEq refl refl = refl

farHighTailReindexingLevel : ProofLevel
farHighTailReindexingLevel = machineChecked
