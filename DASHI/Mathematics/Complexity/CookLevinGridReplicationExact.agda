module DASHI.Mathematics.Complexity.CookLevinGridReplicationExact where

------------------------------------------------------------------------
-- FIXED LOCAL CNF TEMPLATE -> GLOBAL TABLEAU CLAUSE COUNT
--
-- Once a machine-local predicate has been compiled to a fixed CNF template,
-- Cook--Levin repeats that same template over the finite tableau grid.
-- This owner proves the exact counting identity:
--
--   clauses(replicate positions template)
--     = positions * clauses(template).
--
-- Hence the remaining polynomial-size theorem is ordinary closure of the
-- chosen time/space bounds under multiplication by a machine-dependent
-- constant; no further SAT semantics are hidden here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

append : ∀ {A : Set} → List A → List A → List A
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

lengthAppend :
  ∀ {A : Set} (xs ys : List A) →
  listLength (append xs ys)
  ≡ listLength xs + listLength ys
lengthAppend [] ys = refl
lengthAppend (x ∷ xs) ys =
  cong suc (lengthAppend xs ys)

replicateTemplate :
  ∀ {width} →
  Nat →
  CNF.CNF width →
  CNF.CNF width
replicateTemplate zero template = []
replicateTemplate (suc positions) template =
  append template (replicateTemplate positions template)

replicatedClauseCount :
  ∀ {width}
    (positions : Nat)
    (template : CNF.CNF width) →
  listLength (replicateTemplate positions template)
  ≡ positions * listLength template
replicatedClauseCount zero template = refl
replicatedClauseCount (suc positions) template =
  trans
    (lengthAppend template
      (replicateTemplate positions template))
    (trans
      (cong
        (λ n → listLength template + n)
        (replicatedClauseCount positions template))
      (sym
        (sucTimes positions (listLength template))))
  where
    trans : ∀ {A : Set} {x y z : A} →
      x ≡ y → y ≡ z → x ≡ z
    trans refl second = second

    sym : ∀ {A : Set} {x y : A} →
      x ≡ y → y ≡ x
    sym refl = refl

    sucTimes : ∀ left right →
      suc left * right
      ≡ right + left * right
    sucTimes left right = refl

tableauGridPositions :
  Nat → Nat → Nat
tableauGridPositions time space =
  time * space

gridReplicatedClauseCount :
  ∀ {width}
    (time space : Nat)
    (template : CNF.CNF width) →
  listLength
    (replicateTemplate
      (tableauGridPositions time space)
      template)
  ≡ (time * space) * listLength template
gridReplicatedClauseCount time space template =
  replicatedClauseCount
    (tableauGridPositions time space)
    template

record CookLevinGridAccountingBoundary : Set where
  constructor cook-levin-grid-accounting-boundary
  field
    exactTemplateReplicationCountPaid : Agda.Builtin.Bool.Bool
    localTemplateSemanticsPaid : Agda.Builtin.Bool.Bool
    polynomialTimeSpaceClosurePaid : Agda.Builtin.Bool.Bool
    fullGenericCookLevinPaid : Agda.Builtin.Bool.Bool

canonicalCookLevinGridAccountingBoundary :
  CookLevinGridAccountingBoundary
canonicalCookLevinGridAccountingBoundary =
  cook-levin-grid-accounting-boundary
    Agda.Builtin.Bool.true
    Agda.Builtin.Bool.true
    Agda.Builtin.Bool.false
    Agda.Builtin.Bool.false
