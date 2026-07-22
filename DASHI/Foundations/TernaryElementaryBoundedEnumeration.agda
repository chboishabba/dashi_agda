module DASHI.Foundations.TernaryElementaryBoundedEnumeration where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using (List; []; _∷_)

open import DASHI.Foundations.ElementarySingleOperator using (Var)
open import DASHI.Foundations.TernaryElementaryOperatorCandidate
  using (TernaryExpr; varT; nodeT)

------------------------------------------------------------------------
-- Concrete finite enumeration used by bounded external and internal searches.
-- `enumerateAtMost variables d` contains all leaves and every ternary node built
-- recursively from the previous at-most-depth pool.  Structural and semantic
-- deduplication remain separate certified passes.

append : ∀ {A : Set} → List A → List A → List A
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

mapList :
  ∀ {A B : Set} →
  (A → B) →
  List A →
  List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

flatMap :
  ∀ {A B : Set} →
  (A → List B) →
  List A →
  List B
flatMap f [] = []
flatMap f (x ∷ xs) = append (f x) (flatMap f xs)

nodesForLeftRight :
  TernaryExpr →
  TernaryExpr →
  List TernaryExpr →
  List TernaryExpr
nodesForLeftRight left middle rights =
  mapList (λ right → nodeT left middle right) rights

nodesForLeft :
  TernaryExpr →
  List TernaryExpr →
  List TernaryExpr
nodesForLeft left pool =
  flatMap (λ middle → nodesForLeftRight left middle pool) pool

allTernaryNodes :
  List TernaryExpr →
  List TernaryExpr
allTernaryNodes pool =
  flatMap (λ left → nodesForLeft left pool) pool

variableLeaves : List Var → List TernaryExpr
variableLeaves = mapList varT

enumerateAtMost :
  List Var →
  Nat →
  List TernaryExpr
enumerateAtMost variables zero = variableLeaves variables
enumerateAtMost variables (suc depth) =
  append prior (allTernaryNodes prior)
  where
    prior = enumerateAtMost variables depth

------------------------------------------------------------------------
-- Search passes are explicit so that numerical signatures cannot silently
-- become theorem-level quotienting.

record StructuralDeduplicator : Set₁ where
  field
    deduplicate : List TernaryExpr → List TernaryExpr
    preservesCandidateMeaning : Set

open StructuralDeduplicator public

record SemanticDeduplicator : Set₁ where
  field
    deduplicateSemantically : List TernaryExpr → List TernaryExpr
    semanticEqualityCertificate : Set

open SemanticDeduplicator public

record BoundedEnumerationReceipt : Set₁ where
  field
    variables : List Var
    depth : Nat
    literalCandidates : List TernaryExpr
    literalCandidatesAreCanonical :
      literalCandidates ≡ enumerateAtMost variables depth

open BoundedEnumerationReceipt public
