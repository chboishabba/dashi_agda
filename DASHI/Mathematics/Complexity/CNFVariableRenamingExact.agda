module DASHI.Mathematics.Complexity.CNFVariableRenamingExact where

------------------------------------------------------------------------
-- CNF VARIABLE RENAMING / WINDOW PLACEMENT
--
-- A local Cook--Levin clause template is written over a fixed set of local
-- variables.  Every tableau window supplies a map from those local variables
-- into the global tableau variable space.
--
-- Renaming literals/clauses/CNFs along that map preserves evaluation exactly
-- when the global assignment is pulled back along the same map.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

tabulateBits :
  ∀ {n} →
  (Fin.Fin n → Bool) →
  CNF.Bits n
tabulateBits {zero} function = CNF.[]ᵇ
tabulateBits {suc n} function =
  function Fin.zero
  CNF.∷ᵇ
  tabulateBits (λ index → function (Fin.suc index))

lookupTabulateBits :
  ∀ {n}
    (function : Fin.Fin n → Bool)
    (index : Fin.Fin n) →
  CNF.lookupBit (tabulateBits function) index
  ≡ function index
lookupTabulateBits {suc n} function Fin.zero = refl
lookupTabulateBits {suc n} function (Fin.suc index) =
  lookupTabulateBits
    (λ inner → function (Fin.suc inner))
    index

pullbackBits :
  ∀ {local global} →
  (Fin.Fin local → Fin.Fin global) →
  CNF.Bits global →
  CNF.Bits local
pullbackBits rename globalBits =
  tabulateBits
    (λ localIndex →
      CNF.lookupBit globalBits (rename localIndex))

pullbackLookup :
  ∀ {local global}
    (rename : Fin.Fin local → Fin.Fin global)
    (globalBits : CNF.Bits global)
    (localIndex : Fin.Fin local) →
  CNF.lookupBit
    (pullbackBits rename globalBits)
    localIndex
  ≡ CNF.lookupBit globalBits (rename localIndex)
pullbackLookup rename globalBits localIndex =
  lookupTabulateBits
    (λ index →
      CNF.lookupBit globalBits (rename index))
    localIndex

renameLiteral :
  ∀ {local global} →
  (Fin.Fin local → Fin.Fin global) →
  CNF.Literal local →
  CNF.Literal global
renameLiteral rename (CNF.positive index) =
  CNF.positive (rename index)
renameLiteral rename (CNF.negative index) =
  CNF.negative (rename index)

renameClause :
  ∀ {local global} →
  (Fin.Fin local → Fin.Fin global) →
  CNF.Clause local →
  CNF.Clause global
renameClause rename [] = []
renameClause rename (literal ∷ literals) =
  renameLiteral rename literal
  ∷ renameClause rename literals

renameCNF :
  ∀ {local global} →
  (Fin.Fin local → Fin.Fin global) →
  CNF.CNF local →
  CNF.CNF global
renameCNF rename [] = []
renameCNF rename (clause ∷ clauses) =
  renameClause rename clause
  ∷ renameCNF rename clauses

renamedLiteralEvaluation :
  ∀ {local global}
    (rename : Fin.Fin local → Fin.Fin global)
    (literal : CNF.Literal local)
    (globalBits : CNF.Bits global) →
  CNF.evaluateLiteral
    (renameLiteral rename literal)
    globalBits
  ≡ CNF.evaluateLiteral
      literal
      (pullbackBits rename globalBits)
renamedLiteralEvaluation rename
    (CNF.positive index) globalBits =
  sym
    (pullbackLookup rename globalBits index)
  where
    sym : ∀ {A : Set} {x y : A} →
      x ≡ y → y ≡ x
    sym refl = refl
renamedLiteralEvaluation rename
    (CNF.negative index) globalBits =
  cong CNF.notBool
    (sym (pullbackLookup rename globalBits index))
  where
    sym : ∀ {A : Set} {x y : A} →
      x ≡ y → y ≡ x
    sym refl = refl

renamedClauseEvaluation :
  ∀ {local global}
    (rename : Fin.Fin local → Fin.Fin global)
    (clause : CNF.Clause local)
    (globalBits : CNF.Bits global) →
  CNF.evaluateClause
    (renameClause rename clause)
    globalBits
  ≡ CNF.evaluateClause
      clause
      (pullbackBits rename globalBits)
renamedClauseEvaluation rename [] globalBits = refl
renamedClauseEvaluation rename (literal ∷ literals) globalBits =
  cong₂ CNF.orBool
    (renamedLiteralEvaluation rename literal globalBits)
    (renamedClauseEvaluation rename literals globalBits)

renamedCNFEvaluation :
  ∀ {local global}
    (rename : Fin.Fin local → Fin.Fin global)
    (formula : CNF.CNF local)
    (globalBits : CNF.Bits global) →
  CNF.evaluateCNF
    (renameCNF rename formula)
    globalBits
  ≡ CNF.evaluateCNF
      formula
      (pullbackBits rename globalBits)
renamedCNFEvaluation rename [] globalBits = refl
renamedCNFEvaluation rename (clause ∷ clauses) globalBits =
  cong₂ CNF.andBool
    (renamedClauseEvaluation rename clause globalBits)
    (renamedCNFEvaluation rename clauses globalBits)

placedTruthTableCNFSound :
  ∀ {local global}
    (rename : Fin.Fin local → Fin.Fin global)
    (predicate : CNF.Bits local → Bool)
    (globalBits : CNF.Bits global) →
  CNF.evaluateCNF
    (renameCNF rename (CNF.truthTableCNF predicate))
    globalBits
  ≡ true →
  predicate (pullbackBits rename globalBits)
  ≡ true
placedTruthTableCNFSound rename predicate globalBits accepted =
  CNF.truthTableCNFSound
    predicate
    (pullbackBits rename globalBits)
    (transport accepted)
  where
    transport :
      CNF.evaluateCNF
        (renameCNF rename (CNF.truthTableCNF predicate))
        globalBits
      ≡ true →
      CNF.evaluateCNF
        (CNF.truthTableCNF predicate)
        (pullbackBits rename globalBits)
      ≡ true
    transport proof
      with renamedCNFEvaluation
        rename
        (CNF.truthTableCNF predicate)
        globalBits
    ... | refl = proof

placedTruthTableCNFComplete :
  ∀ {local global}
    (rename : Fin.Fin local → Fin.Fin global)
    (predicate : CNF.Bits local → Bool)
    (globalBits : CNF.Bits global) →
  predicate (pullbackBits rename globalBits)
  ≡ true →
  CNF.evaluateCNF
    (renameCNF rename (CNF.truthTableCNF predicate))
    globalBits
  ≡ true
placedTruthTableCNFComplete rename predicate globalBits accepted
    with renamedCNFEvaluation
      rename
      (CNF.truthTableCNF predicate)
      globalBits
... | refl =
  CNF.truthTableCNFComplete
    predicate
    (pullbackBits rename globalBits)
    accepted
