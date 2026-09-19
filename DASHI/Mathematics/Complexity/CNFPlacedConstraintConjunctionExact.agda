module DASHI.Mathematics.Complexity.CNFPlacedConstraintConjunctionExact where

------------------------------------------------------------------------
-- FINITE CONJUNCTION OF PLACED LOCAL CNF CONSTRAINTS
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.CNFVariableRenamingExact as Rename

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
evaluateCNFAppend (clause ∷ clauses) right assignment
    with evaluateCNFAppend clauses right assignment
... | refl
    with CNF.evaluateClause clause assignment
       | CNF.evaluateCNF clauses assignment
       | CNF.evaluateCNF right assignment
... | true | true | true = refl
... | true | true | false = refl
... | true | false | true = refl
... | true | false | false = refl
... | false | true | true = refl
... | false | true | false = refl
... | false | false | true = refl
... | false | false | false = refl

record PlacedPredicate
    (local global : Agda.Builtin.Nat.Nat) : Set₁ where
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
    {local global : Agda.Builtin.Nat.Nat}
    (assignment : CNF.Bits global) :
    List (PlacedPredicate local global) →
    Set where
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
    split
      with evaluateCNFAppend
        (compilePlaced placed)
        (compilePlacedAll rest)
        assignment
    ... | refl = accepted

    leftAccepted :
      CNF.evaluateCNF
        (compilePlaced placed)
        assignment
      ≡ true
    leftAccepted
      with CNF.evaluateCNF
        (compilePlaced placed)
        assignment
       | CNF.evaluateCNF
        (compilePlacedAll rest)
        assignment
       | split
    ... | true | true | proof = refl
    ... | true | false | ()
    ... | false | true | ()
    ... | false | false | ()

    rightAccepted :
      CNF.evaluateCNF
        (compilePlacedAll rest)
        assignment
      ≡ true
    rightAccepted
      with CNF.evaluateCNF
        (compilePlaced placed)
        assignment
       | CNF.evaluateCNF
        (compilePlacedAll rest)
        assignment
       | split
    ... | true | true | proof = refl
    ... | true | false | ()
    ... | false | true | ()
    ... | false | false | ()

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
  transport
    localAccepted
    (compilePlacedAllComplete rest assignment remainder)
  where
    localAccepted :
      CNF.evaluateCNF
        (compilePlaced placed)
        assignment
      ≡ true
    localAccepted =
      Rename.placedTruthTableCNFComplete
        (rename placed)
        (predicate placed)
        assignment
        current

    transport :
      CNF.evaluateCNF
        (compilePlaced placed)
        assignment
      ≡ true →
      CNF.evaluateCNF
        (compilePlacedAll rest)
        assignment
      ≡ true →
      CNF.evaluateCNF
        (compilePlacedAll (placed ∷ rest))
        assignment
      ≡ true
    transport leftProof rightProof
      with evaluateCNFAppend
        (compilePlaced placed)
        (compilePlacedAll rest)
        assignment
    ... | equality
      with CNF.evaluateCNF (compilePlaced placed) assignment
         | CNF.evaluateCNF (compilePlacedAll rest) assignment
         | leftProof
         | rightProof
    ... | true | true | refl | refl
      with equality
    ... | refl = refl
