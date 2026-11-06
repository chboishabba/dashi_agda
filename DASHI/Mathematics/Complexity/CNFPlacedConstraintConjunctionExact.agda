module DASHI.Mathematics.Complexity.CNFPlacedConstraintConjunctionExact where

------------------------------------------------------------------------
-- FINITE CONJUNCTION OF PLACED LOCAL CNF CONSTRAINTS
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.CNFVariableRenamingExact as Rename

private
  trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans refl refl = refl

  sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
  sym refl = refl

  cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
  cong f refl = refl

  andBoolAssociative :
    ∀ (a b c : Bool) →
    CNF.andBool a (CNF.andBool b c) ≡ CNF.andBool (CNF.andBool a b) c
  andBoolAssociative true b c = refl
  andBoolAssociative false b c = refl

  andBoolLeftTrue : ∀ (a b : Bool) → CNF.andBool a b ≡ true → a ≡ true
  andBoolLeftTrue false b ()
  andBoolLeftTrue true b refl = refl

  andBoolRightTrue : ∀ (a b : Bool) → CNF.andBool a b ≡ true → b ≡ true
  andBoolRightTrue false b ()
  andBoolRightTrue true b proof = proof

  andBoolBothTrue : ∀ {a b : Bool} → a ≡ true → b ≡ true → CNF.andBool a b ≡ true
  andBoolBothTrue refl refl = refl

append :
  ∀ {A : Set} →
  List A → List A → List A
append [] ys = ys
append (x ∷ xs) ys =
  x ∷ append xs ys

evaluateCNFAppend :
  ∀ {n}
    (left right : CNF.CNF n)
    (assignment : CNF.Bits n) →
  CNF.evaluateCNF
    (append left right)
    assignment
  ≡ CNF.andBool
      (CNF.evaluateCNF left assignment)
      (CNF.evaluateCNF right assignment)
evaluateCNFAppend [] right assignment = refl
evaluateCNFAppend (clause ∷ clauses) right assignment =
  trans
    (cong (CNF.andBool (CNF.evaluateClause clause assignment))
      (evaluateCNFAppend clauses right assignment))
    (andBoolAssociative
      (CNF.evaluateClause clause assignment)
      (CNF.evaluateCNF clauses assignment)
      (CNF.evaluateCNF right assignment))

record PlacedPredicate
    (local global : Nat) : Set₁ where
  constructor placed-predicate
  field
    rename :
      Fin.Fin local → Fin.Fin global
    predicate :
      CNF.Bits local → Bool

open PlacedPredicate public

compilePlaced :
  ∀ {local global} →
  PlacedPredicate local global →
  CNF.CNF global
compilePlaced placed =
  Rename.renameCNF
    (rename placed)
    (CNF.truthTableCNF
      (predicate placed))

compilePlacedAll :
  ∀ {local global} →
  List (PlacedPredicate local global) →
  CNF.CNF global
compilePlacedAll [] = []
compilePlacedAll (placed ∷ rest) =
  append
    (compilePlaced placed)
    (compilePlacedAll rest)

data AllPlacedSatisfied
    {local global : Nat}
    (assignment : CNF.Bits global) :
    List (PlacedPredicate local global) →
    Set₁ where
  allPlacedDone :
    AllPlacedSatisfied assignment []
  allPlacedStep :
    ∀ {placed rest} →
    predicate placed
      (Rename.pullbackBits
        (rename placed)
        assignment)
    ≡ true →
    AllPlacedSatisfied assignment rest →
    AllPlacedSatisfied assignment (placed ∷ rest)

compilePlacedAllSound :
  ∀ {local global}
    (placed : List (PlacedPredicate local global))
    (assignment : CNF.Bits global) →
  CNF.evaluateCNF
    (compilePlacedAll placed)
    assignment
  ≡ true →
  AllPlacedSatisfied assignment placed
compilePlacedAllSound [] assignment accepted =
  allPlacedDone
compilePlacedAllSound (placed ∷ rest) assignment accepted =
  allPlacedStep
    (Rename.placedTruthTableCNFSound
      (rename placed)
      (predicate placed)
      assignment
      leftAccepted)
    (compilePlacedAllSound
      rest
      assignment
      rightAccepted)
  where
    split :
      CNF.andBool
        (CNF.evaluateCNF
          (compilePlaced placed)
          assignment)
        (CNF.evaluateCNF
          (compilePlacedAll rest)
          assignment)
      ≡ true
    split =
      trans
        (sym (evaluateCNFAppend
          (compilePlaced placed)
          (compilePlacedAll rest)
          assignment))
        accepted

    leftAccepted :
      CNF.evaluateCNF
        (compilePlaced placed)
        assignment
      ≡ true
    leftAccepted =
      andBoolLeftTrue
        (CNF.evaluateCNF (compilePlaced placed) assignment)
        (CNF.evaluateCNF (compilePlacedAll rest) assignment)
        split

    rightAccepted :
      CNF.evaluateCNF
        (compilePlacedAll rest)
        assignment
      ≡ true
    rightAccepted =
      andBoolRightTrue
        (CNF.evaluateCNF (compilePlaced placed) assignment)
        (CNF.evaluateCNF (compilePlacedAll rest) assignment)
        split

compilePlacedAllComplete :
  ∀ {local global}
    (placed : List (PlacedPredicate local global))
    (assignment : CNF.Bits global) →
  AllPlacedSatisfied assignment placed →
  CNF.evaluateCNF
    (compilePlacedAll placed)
    assignment
  ≡ true
compilePlacedAllComplete [] assignment allPlacedDone = refl
compilePlacedAllComplete (placed ∷ rest) assignment
    (allPlacedStep current remainder) =
  trans
    (evaluateCNFAppend
      (compilePlaced placed)
      (compilePlacedAll rest)
      assignment)
    (andBoolBothTrue
      (Rename.placedTruthTableCNFComplete
        (rename placed)
        (predicate placed)
        assignment
        current)
      (compilePlacedAllComplete rest assignment remainder))
