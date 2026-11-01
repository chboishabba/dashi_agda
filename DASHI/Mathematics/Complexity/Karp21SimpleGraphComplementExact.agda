module DASHI.Mathematics.Complexity.Karp21SimpleGraphComplementExact where

------------------------------------------------------------------------
-- Karp 1972: CLIQUE -> NODE COVER on the complement SIMPLE graph.
-- A naive Boolean negate creates self-loops when the original diagonal
-- is false. This owner fixes the same-object finite representation:
-- the complement is negated ONLY on distinct Fin n vertices.
--
-- Source mathematics: R. Karp, Reducibility Among Combinatorial
-- Problems (1972), DOI 10.1007/978-1-4684-2001-2_9.
-- DASHI: explicit loop-free/symmetric finite graph complement and
-- witness transport. Encoded bitstring/machine cost remains open.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Nat.Base using (_≤_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
open import Relation.Nullary.Decidable.Core using (yes; no)

import Data.Fin.Base as Fin
import Data.Fin.Properties as FinP
import Data.Vec.Base as Vec
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.Karp21CliqueVertexCoverExact as Graph
import DASHI.Mathematics.Complexity.Karp21FiniteCliqueVertexCoverCombinedExact as Combined

record SimpleGraph (n : Nat) : Set where
  field
    adjacency : Fin.Fin n → Fin.Fin n → Bool
    symmetric : ∀ u v → adjacency u v ≡ adjacency v u
    loopFree : ∀ u → adjacency u u ≡ false

open SimpleGraph public

simpleComplementAdjacency :
  ∀ {n} → SimpleGraph n →
  Fin.Fin n → Fin.Fin n → Bool
simpleComplementAdjacency graph u v
  with FinP._≟_ u v
... | yes _ = false
... | no _ = Graph.negBool (adjacency graph u v)

simpleComplementLoopFree :
  ∀ {n} (graph : SimpleGraph n) (u : Fin.Fin n) →
  simpleComplementAdjacency graph u u ≡ false
simpleComplementLoopFree graph u with FinP._≟_ u u
... | yes _ = refl
... | no neq = ⊥-elim (neq refl)

simpleComplementSymmetric :
  ∀ {n} (graph : SimpleGraph n)
    (u v : Fin.Fin n) →
  simpleComplementAdjacency graph u v ≡
  simpleComplementAdjacency graph v u
simpleComplementSymmetric graph u v
  with FinP._≟_ u v | FinP._≟_ v u
... | yes _ | yes _ = refl
... | yes equal | no unequal = ⊥-elim (unequal (sym equal))
... | no unequal | yes equal = ⊥-elim (unequal (sym equal))
... | no _ | no _ =
  cong Graph.negBool (symmetric graph u v)

simpleComplementOffDiagonal :
  ∀ {n} (graph : SimpleGraph n)
    (u v : Fin.Fin n) →
  (u ≡ v → ⊥) →
  simpleComplementAdjacency graph u v ≡
  Graph.complementAdjacency (adjacency graph) u v
simpleComplementOffDiagonal graph u v distinct
  with FinP._≟_ u v
... | yes equal = ⊥-elim (distinct equal)
... | no _ = refl

complementSimpleGraph :
  ∀ {n} → SimpleGraph n → SimpleGraph n
complementSimpleGraph graph = record
  { adjacency = simpleComplementAdjacency graph
  ; symmetric = simpleComplementSymmetric graph
  ; loopFree = simpleComplementLoopFree graph
  }

-- Combine an actual simple target graph with the SAME selection bits and
-- the additive cardinality inequality already established by Combined.
FiniteSimpleComplementCoverAt :
  ∀ {n} → SimpleGraph n → Vec.Vec Bool n → Nat → Set
FiniteSimpleComplementCoverAt {n} graph choices k =
  Graph.VertexCover
    (adjacency (complementSimpleGraph graph))
    (Graph.complementSelection (Combined.selected choices))
  ×
  (Combined.complementCount choices + k ≤ n)

finiteAbstractCoverToSimpleCover :
  ∀ {n} (graph : SimpleGraph n)
    (choices : Vec.Vec Bool n) (k : Nat) →
  Combined.FiniteComplementCoverAt (adjacency graph) choices k →
  FiniteSimpleComplementCoverAt graph choices k
finiteAbstractCoverToSimpleCover graph choices k (cover , budget) =
  (λ u v distinct connected →
    cover u v distinct
      (trans (sym (simpleComplementOffDiagonal graph u v distinct))
        connected)) ,
  budget

finiteSimpleCoverToAbstractCover :
  ∀ {n} (graph : SimpleGraph n)
    (choices : Vec.Vec Bool n) (k : Nat) →
  FiniteSimpleComplementCoverAt graph choices k →
  Combined.FiniteComplementCoverAt (adjacency graph) choices k
finiteSimpleCoverToAbstractCover graph choices k (cover , budget) =
  (λ u v distinct connected →
    cover u v distinct
      (trans (simpleComplementOffDiagonal graph u v distinct)
        connected)) ,
  budget

finiteCliqueToSimpleComplementCover :
  ∀ {n} (graph : SimpleGraph n)
    (choices : Vec.Vec Bool n) (k : Nat) →
  Combined.FiniteCliqueAt (adjacency graph) choices k →
  FiniteSimpleComplementCoverAt graph choices k
finiteCliqueToSimpleComplementCover graph choices k source =
  finiteAbstractCoverToSimpleCover graph choices k
    (Combined.finiteCliqueToComplementCover
      (adjacency graph) choices k source)

finiteSimpleComplementCoverToClique :
  ∀ {n} (graph : SimpleGraph n)
    (choices : Vec.Vec Bool n) (k : Nat) →
  FiniteSimpleComplementCoverAt graph choices k →
  Combined.FiniteCliqueAt (adjacency graph) choices k
finiteSimpleComplementCoverToClique graph choices k target =
  Combined.finiteComplementCoverToClique
    (adjacency graph) choices k
    (finiteSimpleCoverToAbstractCover graph choices k target)

karpCliqueSimpleComplementCoverIff :
  ∀ {n} (graph : SimpleGraph n)
    (choices : Vec.Vec Bool n) (k : Nat) →
  PR.Iff
    (Combined.FiniteCliqueAt (adjacency graph) choices k)
    (FiniteSimpleComplementCoverAt graph choices k)
karpCliqueSimpleComplementCoverIff graph choices k =
  PR.iff
    (finiteCliqueToSimpleComplementCover graph choices k)
    (finiteSimpleComplementCoverToClique graph choices k)


------------------------------------------------------------------------
-- Instance-level existential reduction, now with a genuine simple
-- complement graph: both directions preserve the finite selected
-- witness and its additive cover budget. There is no search/oracle.
------------------------------------------------------------------------

CliqueYES :
  ∀ {n} → SimpleGraph n → Nat → Set
CliqueYES {n} graph k =
  Σ (Vec.Vec Bool n)
    (λ choices →
      Combined.FiniteCliqueAt (adjacency graph) choices k)

ComplementCoverYES :
  ∀ {n} → SimpleGraph n → Nat → Set
ComplementCoverYES {n} graph k =
  Σ (Vec.Vec Bool n)
    (λ choices → FiniteSimpleComplementCoverAt graph choices k)

simpleGraphCliqueToComplementCoverYES :
  ∀ {n} (graph : SimpleGraph n) (k : Nat) →
  CliqueYES graph k → ComplementCoverYES graph k
simpleGraphCliqueToComplementCoverYES graph k
  (choices , witness) =
  choices , finiteCliqueToSimpleComplementCover graph choices k witness

simpleGraphComplementCoverToCliqueYES :
  ∀ {n} (graph : SimpleGraph n) (k : Nat) →
  ComplementCoverYES graph k → CliqueYES graph k
simpleGraphComplementCoverToCliqueYES graph k
  (choices , witness) =
  choices , finiteSimpleComplementCoverToClique graph choices k witness

karpSimpleGraphCliqueCoverInstanceIff :
  ∀ {n} (graph : SimpleGraph n) (k : Nat) →
  PR.Iff (CliqueYES graph k) (ComplementCoverYES graph k)
karpSimpleGraphCliqueCoverInstanceIff graph k =
  PR.iff
    (simpleGraphCliqueToComplementCoverYES graph k)
    (simpleGraphComplementCoverToCliqueYES graph k)
