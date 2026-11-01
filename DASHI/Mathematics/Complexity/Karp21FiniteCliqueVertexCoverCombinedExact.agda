module DASHI.Mathematics.Complexity.Karp21FiniteCliqueVertexCoverCombinedExact where

------------------------------------------------------------------------
-- HISTORICAL ORIGINAL: R. M. Karp (1972), CLIQUE -> NODE COVER,
-- "Reducibility Among Combinatorial Problems",
-- DOI 10.1007/978-1-4684-2001-2_9.
--
-- DASHI: SAME-OBJECT finite Agda conjunction. A witness is indexed by
-- Fin n, so duplicate *labels* cannot collapse vertex positions.
-- Reuse existing Clique/Cover complement equivalence and independent
-- exact finite selection threshold arithmetic. This module proves a
-- constructive fully quantified iff for one graph, one finite selection,
-- and every k, including k > n.
--
-- Still not a binary graph serializer / machine-polynomial reduction.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _≤_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

import Data.Fin.Base as Fin
import Data.Vec.Base as Vec
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.Karp21CliqueVertexCoverExact as Graph
import DASHI.Mathematics.Complexity.Karp21FiniteCliqueCoverCardinalityExact as Count

-- We use the actual Vec lookup map for every semantic occurrence.
selected :
  ∀ {n : Nat} → Vec.Vec Bool n → Fin.Fin n → Bool
selected choices = Vec.lookup choices

selectedCount : ∀ {n} → Vec.Vec Bool n → Nat
selectedCount choices = Count.countChosen (Vec.toList choices)

complementCount : ∀ {n} → Vec.Vec Bool n → Nat
complementCount choices =
  Count.countChosen (Count.flipChoices (Vec.toList choices))

-- No external length or cardinality axiom: structural vector induction.
selectionListLength :
  ∀ {n} (choices : Vec.Vec Bool n) →
  Count.length (Vec.toList choices) ≡ n
selectionListLength Vec.[] = refl
selectionListLength (x Vec.∷ xs) =
  cong suc (selectionListLength xs)

FiniteCliqueAt :
  ∀ {n} →
  (Fin.Fin n → Fin.Fin n → Bool) →
  Vec.Vec Bool n → Nat → Set
FiniteCliqueAt adjacency choices k =
  Graph.Clique adjacency (selected choices)
  × (k ≤ selectedCount choices)

FiniteComplementCoverAt :
  ∀ {n} →
  (Fin.Fin n → Fin.Fin n → Bool) →
  Vec.Vec Bool n → Nat → Set
FiniteComplementCoverAt {n} adjacency choices k =
  Graph.VertexCover
    (Graph.complementAdjacency adjacency)
    (Graph.complementSelection (selected choices))
  × (complementCount choices + k ≤ n)

finiteCliqueToComplementCover :
  ∀ {n}
    (adjacency : Fin.Fin n → Fin.Fin n → Bool)
    (choices : Vec.Vec Bool n)
    (k : Nat) →
  FiniteCliqueAt adjacency choices k →
  FiniteComplementCoverAt adjacency choices k
finiteCliqueToComplementCover adjacency choices k (clique , enough) =
  Graph.cliqueToComplementCover
    adjacency (selected choices) clique ,
  subst
    (λ size → complementCount choices + k ≤ size)
    (selectionListLength choices)
    (PR.forward
      (Count.karpCliqueCoverFiniteThresholdIff
        (Vec.toList choices) k)
      enough)

finiteComplementCoverToClique :
  ∀ {n}
    (adjacency : Fin.Fin n → Fin.Fin n → Bool)
    (choices : Vec.Vec Bool n)
    (k : Nat) →
  FiniteComplementCoverAt adjacency choices k →
  FiniteCliqueAt adjacency choices k
finiteComplementCoverToClique adjacency choices k (cover , enough) =
  Graph.complementCoverToClique
    adjacency (selected choices) cover ,
  PR.backward
    (Count.karpCliqueCoverFiniteThresholdIff
      (Vec.toList choices) k)
    (subst
      (λ size → complementCount choices + k ≤ size)
      (sym (selectionListLength choices))
      enough)

karpFiniteCliqueVertexCoverIff :
  ∀ {n}
    (adjacency : Fin.Fin n → Fin.Fin n → Bool)
    (choices : Vec.Vec Bool n)
    (k : Nat) →
  PR.Iff
    (FiniteCliqueAt adjacency choices k)
    (FiniteComplementCoverAt adjacency choices k)
karpFiniteCliqueVertexCoverIff adjacency choices k =
  PR.iff
    (finiteCliqueToComplementCover adjacency choices k)
    (finiteComplementCoverToClique adjacency choices k)
