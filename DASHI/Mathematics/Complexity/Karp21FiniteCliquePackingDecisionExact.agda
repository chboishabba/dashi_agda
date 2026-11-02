module DASHI.Mathematics.Complexity.Karp21FiniteCliquePackingDecisionExact where

------------------------------------------------------------------------
-- Historical E04, Karp (1972): CLIQUE -> SET PACKING by sets of
-- incident NONEDGES. Use the already written generic Karp21CliqueSet-
-- PackingExact witness transport and the same Fin n / Vec Bool n
-- owner previously used by E05, without adding a second graph carrier.
--
-- Each chosen vertex is an indexed set. Duplicates of vertex *names*
-- cannot collapse positions. All k, including k>n, are supported by
-- the same finite Nat lower-bound predicate.
--
-- This proves the actual FINITE EXISTENTIAL YES equivalence; a word
-- level set-family codec, size bound and polynomial machine map must
-- be proven separately before crediting E04 as an NP-hardness edge.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_)
open import Data.Product using (Σ; _×_; _,_)
import Data.Fin.Base as Fin
import Data.Vec.Base as Vec

import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.Karp21CliqueVertexCoverExact as Graph
import DASHI.Mathematics.Complexity.Karp21CliqueSetPackingExact as Packing
import DASHI.Mathematics.Complexity.Karp21SimpleGraphComplementExact as Simple
import DASHI.Mathematics.Complexity.Karp21FiniteCliqueVertexCoverCombinedExact as Finite

FinitePackingAt :
  ∀ {n} → Simple.SimpleGraph n → Vec.Vec Bool n → Nat → Set
FinitePackingAt graph choices k =
  Packing.Packing (Simple.adjacency graph) (Finite.selected choices)
  × (k ≤ Finite.selectedCount choices)

finiteCliqueToPacking :
  ∀ {n} (graph : Simple.SimpleGraph n)
    (choices : Vec.Vec Bool n) (k : Nat) →
  Finite.FiniteCliqueAt (Simple.adjacency graph) choices k →
  FinitePackingAt graph choices k
finiteCliqueToPacking graph choices k (clique , enough) =
  Packing.cliqueToPacking
    (Simple.adjacency graph)
    (Finite.selected choices)
    (Simple.symmetric graph)
    clique ,
  enough

finitePackingToClique :
  ∀ {n} (graph : Simple.SimpleGraph n)
    (choices : Vec.Vec Bool n) (k : Nat) →
  FinitePackingAt graph choices k →
  Finite.FiniteCliqueAt (Simple.adjacency graph) choices k
finitePackingToClique graph choices k (pack , enough) =
  Packing.packingToClique
    (Simple.adjacency graph)
    (Finite.selected choices)
    pack ,
  enough

FiniteCliqueYES :
  ∀ {n} → Simple.SimpleGraph n → Nat → Set
FiniteCliqueYES {n} graph k =
  Σ (Vec.Vec Bool n) (λ choices →
    Finite.FiniteCliqueAt (Simple.adjacency graph) choices k)

FinitePackingYES :
  ∀ {n} → Simple.SimpleGraph n → Nat → Set
FinitePackingYES {n} graph k =
  Σ (Vec.Vec Bool n) (λ choices → FinitePackingAt graph choices k)

karpFiniteCliquePackingInstanceIff :
  ∀ {n} (graph : Simple.SimpleGraph n) (k : Nat) →
  PR.Iff (FiniteCliqueYES graph k) (FinitePackingYES graph k)
karpFiniteCliquePackingInstanceIff graph k =
  PR.iff
    (λ { (choices , witness) →
      choices , finiteCliqueToPacking graph choices k witness })
    (λ { (choices , witness) →
      choices , finitePackingToClique graph choices k witness })
