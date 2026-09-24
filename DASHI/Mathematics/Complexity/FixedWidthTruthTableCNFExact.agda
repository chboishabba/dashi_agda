module DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact where

------------------------------------------------------------------------
-- FIXED-WIDTH BOOLEAN PREDICATE -> CNF
--
-- Every Boolean predicate on n bits has a canonical truth-table CNF: for each
-- rejected assignment, add one clause excluding exactly that assignment.
--
-- This is intentionally exponential in n.  For Cook--Levin's local-window
-- predicate, n is a machine-dependent constant (six fixed-width cells), so the
-- resulting clause template is constant-size and can be replicated across the
-- polynomial tableau grid without smuggling in an unproved CNF conversion.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin.Base as Fin

notBool : Bool → Bool
notBool false = true
notBool true = false

orBool : Bool → Bool → Bool
orBool false right = right
orBool true right = true

andBool : Bool → Bool → Bool
andBool false right = false
andBool true right = right

data Bits : Nat → Set where
  []ᵇ : Bits zero
  _∷ᵇ_ : ∀ {n} → Bool → Bits n → Bits (suc n)

infixr 5 _∷ᵇ_

lookupBit : ∀ {n} → Bits n → Fin.Fin n → Bool
lookupBit (bit ∷ᵇ bits) Fin.zero = bit
lookupBit (bit ∷ᵇ bits) (Fin.suc index) = lookupBit bits index

mapList : ∀ {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

append : ∀ {A : Set} → List A → List A → List A
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

prependBit : ∀ {n} → Bool → List (Bits n) → List (Bits (suc n))
prependBit bit = mapList (λ bits → bit ∷ᵇ bits)

allBits : (n : Nat) → List (Bits n)
allBits zero = []ᵇ ∷ []
allBits (suc n) =
  append
    (prependBit false (allBits n))
    (prependBit true (allBits n))

data Member {A : Set} (value : A) : List A → Set where
  here : ∀ {values} → Member value (value ∷ values)
  there : ∀ {other values} →
    Member value values →
    Member value (other ∷ values)

memberMap :
  ∀ {A B : Set} {x : A} {xs : List A}
    (f : A → B) →
  Member x xs →
  Member (f x) (mapList f xs)
memberMap f here = here
memberMap f (there membership) =
  there (memberMap f membership)

memberAppendLeft :
  ∀ {A : Set} {x : A} {xs ys : List A} →
  Member x xs →
  Member x (append xs ys)
memberAppendLeft here = here
memberAppendLeft (there membership) =
  there (memberAppendLeft membership)

memberAppendRight :
  ∀ {A : Set} {x : A} (xs : List A) {ys : List A} →
  Member x ys →
  Member x (append xs ys)
memberAppendRight [] membership = membership
memberAppendRight (x ∷ xs) membership =
  there (memberAppendRight xs membership)

allBitsComplete :
  ∀ {n} (bits : Bits n) →
  Member bits (allBits n)
allBitsComplete []ᵇ = here
allBitsComplete {suc n} (false ∷ᵇ bits) =
  memberAppendLeft
    (memberMap
      (λ tail → false ∷ᵇ tail)
      (allBitsComplete bits))
allBitsComplete {suc n} (true ∷ᵇ bits) =
  memberAppendRight
    (prependBit false (allBits n))
    (memberMap
      (λ tail → true ∷ᵇ tail)
      (allBitsComplete bits))

data Literal (n : Nat) : Set where
  positive : Fin.Fin n → Literal n
  negative : Fin.Fin n → Literal n

Clause : Nat → Set
Clause n = List (Literal n)

CNF : Nat → Set
CNF n = List (Clause n)

evaluateLiteral :
  ∀ {n} → Literal n → Bits n → Bool
evaluateLiteral (positive index) bits =
  lookupBit bits index
evaluateLiteral (negative index) bits =
  notBool (lookupBit bits index)

evaluateClause :
  ∀ {n} → Clause n → Bits n → Bool
evaluateClause [] bits = false
evaluateClause (literal ∷ literals) bits =
  orBool
    (evaluateLiteral literal bits)
    (evaluateClause literals bits)

evaluateCNF :
  ∀ {n} → CNF n → Bits n → Bool
evaluateCNF [] bits = true
evaluateCNF (clause ∷ clauses) bits =
  andBool
    (evaluateClause clause bits)
    (evaluateCNF clauses bits)

liftLiteral :
  ∀ {n} → Literal n → Literal (suc n)
liftLiteral (positive index) = positive (Fin.suc index)
liftLiteral (negative index) = negative (Fin.suc index)

liftClause :
  ∀ {n} → Clause n → Clause (suc n)
liftClause = mapList liftLiteral

evaluateLiftClause :
  ∀ {n} (clause : Clause n) bit bits →
  evaluateClause (liftClause clause) (bit ∷ᵇ bits)
  ≡ evaluateClause clause bits
evaluateLiftClause [] bit bits = refl
evaluateLiftClause (literal ∷ literals) bit bits
    with literal
... | positive index
    with evaluateLiftClause literals bit bits
... | refl = refl
... | negative index
    with evaluateLiftClause literals bit bits
... | refl = refl

oppositeHeadLiteral :
  ∀ {n} → Bool → Literal (suc n)
oppositeHeadLiteral false = positive Fin.zero
oppositeHeadLiteral true = negative Fin.zero

forbidClause :
  ∀ {n} → Bits n → Clause n
forbidClause []ᵇ = []
forbidClause (bit ∷ᵇ bits) =
  oppositeHeadLiteral bit ∷ liftClause (forbidClause bits)

forbidClauseRejectsSelf :
  ∀ {n} (bits : Bits n) →
  evaluateClause (forbidClause bits) bits ≡ false
forbidClauseRejectsSelf []ᵇ = refl
forbidClauseRejectsSelf (false ∷ᵇ bits)
    with evaluateLiftClause (forbidClause bits) false bits
       | forbidClauseRejectsSelf bits
... | refl | refl = refl
forbidClauseRejectsSelf (true ∷ᵇ bits)
    with evaluateLiftClause (forbidClause bits) true bits
       | forbidClauseRejectsSelf bits
... | refl | refl = refl

forbidClauseFalseImpliesEqual :
  ∀ {n} (forbidden candidate : Bits n) →
  evaluateClause (forbidClause forbidden) candidate ≡ false →
  candidate ≡ forbidden
forbidClauseFalseImpliesEqual []ᵇ []ᵇ rejected = refl
forbidClauseFalseImpliesEqual
    (false ∷ᵇ forbidden)
    (false ∷ᵇ candidate)
    rejected
    with evaluateLiftClause (forbidClause forbidden) false candidate
... | refl =
  prependFalseCongruence
    (forbidClauseFalseImpliesEqual forbidden candidate rejected)
  where
    prependFalseCongruence :
      ∀ {n} {left right : Bits n} →
      left ≡ right →
      false ∷ᵇ left ≡ false ∷ᵇ right
    prependFalseCongruence refl = refl
forbidClauseFalseImpliesEqual
    (false ∷ᵇ forbidden)
    (true ∷ᵇ candidate)
    ()
forbidClauseFalseImpliesEqual
    (true ∷ᵇ forbidden)
    (false ∷ᵇ candidate)
    ()
forbidClauseFalseImpliesEqual
    (true ∷ᵇ forbidden)
    (true ∷ᵇ candidate)
    rejected
    with evaluateLiftClause (forbidClause forbidden) true candidate
... | refl =
  prependTrueCongruence
    (forbidClauseFalseImpliesEqual forbidden candidate rejected)
  where
    prependTrueCongruence :
      ∀ {n} {left right : Bits n} →
      left ≡ right →
      true ∷ᵇ left ≡ true ∷ᵇ right
    prependTrueCongruence refl = refl

compileRejectedRows :
  ∀ {n} →
  (Bits n → Bool) →
  List (Bits n) →
  CNF n
compileRejectedRows predicate [] = []
compileRejectedRows predicate (row ∷ rows)
    with predicate row
... | true = compileRejectedRows predicate rows
... | false =
  forbidClause row ∷ compileRejectedRows predicate rows

truthTableCNF :
  ∀ {n} →
  (Bits n → Bool) →
  CNF n
truthTableCNF {n} predicate =
  compileRejectedRows predicate (allBits n)

andTrueGivesRight :
  ∀ left right →
  andBool left right ≡ true →
  right ≡ true
andTrueGivesRight false right ()
andTrueGivesRight true right proof = proof

compiledRowsComplete :
  ∀ {n}
    (predicate : Bits n → Bool)
    (rows : List (Bits n))
    (assignment : Bits n) →
  predicate assignment ≡ true →
  evaluateCNF
    (compileRejectedRows predicate rows)
    assignment
  ≡ true
compiledRowsComplete predicate [] assignment accepted = refl
compiledRowsComplete predicate (row ∷ rows) assignment accepted
    with predicate row
... | true =
  compiledRowsComplete predicate rows assignment accepted
... | false
    with evaluateClause (forbidClause row) assignment
... | true =
  compiledRowsComplete predicate rows assignment accepted
... | false
    with forbidClauseFalseImpliesEqual row assignment refl
... | refl
    with accepted
... | ()

compiledRowsSoundAtMember :
  ∀ {n}
    (predicate : Bits n → Bool)
    (rows : List (Bits n))
    (assignment : Bits n) →
  Member assignment rows →
  evaluateCNF
    (compileRejectedRows predicate rows)
    assignment
  ≡ true →
  predicate assignment ≡ true
compiledRowsSoundAtMember predicate [] assignment () cnfTrue
compiledRowsSoundAtMember predicate (row ∷ rows) assignment here cnfTrue
    with predicate assignment
... | true = refl
... | false
    with forbidClauseRejectsSelf assignment
... | rejected
    with cnfTrue
... | ()
compiledRowsSoundAtMember predicate (row ∷ rows) assignment
    (there membership) cnfTrue
    with predicate row
... | true =
  compiledRowsSoundAtMember
    predicate rows assignment membership cnfTrue
... | false =
  compiledRowsSoundAtMember
    predicate rows assignment membership
    (andTrueGivesRight
      (evaluateClause (forbidClause row) assignment)
      (evaluateCNF
        (compileRejectedRows predicate rows)
        assignment)
      cnfTrue)

truthTableCNFComplete :
  ∀ {n}
    (predicate : Bits n → Bool)
    (assignment : Bits n) →
  predicate assignment ≡ true →
  evaluateCNF (truthTableCNF predicate) assignment ≡ true
truthTableCNFComplete {n} predicate assignment =
  compiledRowsComplete
    predicate
    (allBits n)
    assignment

truthTableCNFSound :
  ∀ {n}
    (predicate : Bits n → Bool)
    (assignment : Bits n) →
  evaluateCNF (truthTableCNF predicate) assignment ≡ true →
  predicate assignment ≡ true
truthTableCNFSound {n} predicate assignment =
  compiledRowsSoundAtMember
    predicate
    (allBits n)
    assignment
    (allBitsComplete assignment)

record TruthTableCNFEquivalence
    {n : Nat}
    (predicate : Bits n → Bool) : Set where
  field
    sound :
      ∀ assignment →
      evaluateCNF (truthTableCNF predicate) assignment ≡ true →
      predicate assignment ≡ true
    complete :
      ∀ assignment →
      predicate assignment ≡ true →
      evaluateCNF (truthTableCNF predicate) assignment ≡ true

canonicalTruthTableCNFEquivalence :
  ∀ {n} (predicate : Bits n → Bool) →
  TruthTableCNFEquivalence predicate
canonicalTruthTableCNFEquivalence predicate = record
  { sound = truthTableCNFSound predicate
  ; complete = truthTableCNFComplete predicate
  }
