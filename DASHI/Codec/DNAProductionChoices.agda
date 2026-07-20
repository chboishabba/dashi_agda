module DASHI.Codec.DNAProductionChoices where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Sigma using (Σ; _,_)

open import DASHI.Codec.DNAFirstFormalism using (Base; A; C; G; T)
open import DASHI.Codec.DNAProductionConstraints using
  ( ProductionState; legal?; step; IsTrue; trueWitness )

------------------------------------------------------------------------
-- Legal alphabet derived from the decision procedure.

include : Bool → Base → List Base → List Base
include true b xs = b ∷ xs
include false b xs = xs

legalBases : ProductionState → List Base
legalBases s =
  include (legal? s A) A
    (include (legal? s C) C
      (include (legal? s G) G
        (include (legal? s T) T [])))

length : ∀ {X : Set} → List X → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

branchCount : ProductionState → Nat
branchCount s = length (legalBases s)

data Arity : Set where
  arity0 arity1 arity2 arity3 arity4 : Arity

arityOf : List Base → Arity
arityOf [] = arity0
arityOf (x ∷ []) = arity1
arityOf (x ∷ y ∷ []) = arity2
arityOf (x ∷ y ∷ z ∷ []) = arity3
arityOf (x ∷ y ∷ z ∷ w ∷ xs) = arity4

branchArity : ProductionState → Arity
branchArity s = arityOf (legalBases s)

------------------------------------------------------------------------
-- Executable rank/unrank for the state-derived legal alphabet.

data Maybe (X : Set) : Set where
  nothing : Maybe X
  just : X → Maybe X

baseEq : Base → Base → Bool
baseEq A A = true
baseEq C C = true
baseEq G G = true
baseEq T T = true
baseEq _ _ = false

unrankList : Nat → List Base → Maybe Base
unrankList n [] = nothing
unrankList zero (x ∷ xs) = just x
unrankList (suc n) (x ∷ xs) = unrankList n xs

rankList : Base → List Base → Maybe Nat
rankList b [] = nothing
rankList b (x ∷ xs) with baseEq b x
... | true = just zero
... | false with rankList b xs
...   | nothing = nothing
...   | just n = just (suc n)

unrank : ProductionState → Nat → Maybe Base
unrank s n = unrankList n (legalBases s)

rank : ProductionState → Base → Maybe Nat
rank s b = rankList b (legalBases s)

-- These two lemmas cover the definitional boundary cases used by the range
-- coder. The general list theorem is exposed as a receipt below so alternative
-- list implementations can supply the same contract.
unrank-zero-head : ∀ {x xs} → unrankList zero (x ∷ xs) ≡ just x
unrank-zero-head = refl

rank-head : ∀ {x xs} → rankList x (x ∷ xs) ≡ just zero
rank-head {A} = refl
rank-head {C} = refl
rank-head {G} = refl
rank-head {T} = refl

record RankUnrankReceipt : Set₁ where
  field
    rankUnrank :
      ∀ (xs : List Base) (n : Nat) (b : Base) →
      unrankList n xs ≡ just b → rankList b xs ≡ just n
    unrankRank :
      ∀ (xs : List Base) (b : Base) (n : Nat) →
      rankList b xs ≡ just n → unrankList n xs ≡ just b

------------------------------------------------------------------------
-- Exact horizon-indexed completion object. A table entry is not merely a
-- Boolean: it carries every emitted-base legality witness along the path.

data Completion : Nat → ProductionState → Set where
  horizon0 : ∀ {s} → Completion zero s
  extend :
    ∀ {h s b} →
    IsTrue (legal? s b) →
    Completion h (step s b) →
    Completion (suc h) s

CompletionEntry : Nat → ProductionState → Set
CompletionEntry h s = Σ (List Base) (λ word → Completion h s)

record HorizonCompletionTable : Set₁ where
  field
    lookup : (h : Nat) → (s : ProductionState) → List (CompletionEntry h s)
    sound :
      ∀ h s word proof →
      (word , proof) ∈ lookup h s → Completion h s
  infix 4 _∈_
  data _∈_ {X : Set} (x : X) : List X → Set where
    here : ∀ {xs} → x ∈ (x ∷ xs)
    there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

------------------------------------------------------------------------
-- Receipt tying variable arity to the actual finite alphabet.

record VariableChoiceReceipt : Set where
  field
    choices : ProductionState → List Base
    count : ProductionState → Nat
    countIsLength : ∀ s → count s ≡ length (choices s)
    arity : ProductionState → Arity

variableChoiceReceipt : VariableChoiceReceipt
variableChoiceReceipt = record
  { choices = legalBases
  ; count = branchCount
  ; countIsLength = λ s → refl
  ; arity = branchArity
  }
