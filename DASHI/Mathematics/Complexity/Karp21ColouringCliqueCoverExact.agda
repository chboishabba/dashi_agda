module DASHI.Mathematics.Complexity.Karp21ColouringCliqueCoverExact where

------------------------------------------------------------------------
-- SOURCE: Karp (1972), pp. 99, CHROMATIC NUMBER -> CLIQUE COVER.
-- DOI: 10.1007/978-1-4684-2001-2_9.
-- DASHI: same palette assignment is a colouring of G iff its fibres
-- are cliques in the complement of G. Finite palette/cardinality and
-- graph encoding/machine cost remain unpaid.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)

import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.Karp21CliqueVertexCoverExact as Graph

ProperColouring :
  ∀ {Vertex Colour : Set} →
  (Vertex → Vertex → Bool) →
  (Colour → Colour → Bool) →
  (Vertex → Colour) → Set
ProperColouring {Vertex} adjacent sameColour colouring =
  ∀ u v → (u ≡ v → ⊥) →
    adjacent u v ≡ true →
    sameColour (colouring u) (colouring v) ≡ false

CliqueFibres :
  ∀ {Vertex Colour : Set} →
  (Vertex → Vertex → Bool) →
  (Colour → Colour → Bool) →
  (Vertex → Colour) → Set
CliqueFibres {Vertex} adjacent sameColour colouring =
  ∀ u v → (u ≡ v → ⊥) →
    sameColour (colouring u) (colouring v) ≡ true →
    Graph.complementAdjacency adjacent u v ≡ true

trueFalseImpossible : ∀ {value : Bool} → value ≡ true → value ≡ false → ⊥
trueFalseImpossible {true} refl ()
trueFalseImpossible {false} () _

colouringToComplementCliqueFibres :
  ∀ {Vertex Colour : Set}
    (adjacent : Vertex → Vertex → Bool)
    (sameColour : Colour → Colour → Bool)
    (colouring : Vertex → Colour) →
  ProperColouring adjacent sameColour colouring →
  CliqueFibres adjacent sameColour colouring
colouringToComplementCliqueFibres adjacent sameColour colouring proper
  u v distinct same
  with adjacent u v
... | false = refl
... | true =
  ⊥-elim (trueFalseImpossible same (proper u v distinct refl))

complementCliqueFibresToColouring :
  ∀ {Vertex Colour : Set}
    (adjacent : Vertex → Vertex → Bool)
    (sameColour : Colour → Colour → Bool)
    (colouring : Vertex → Colour) →
  CliqueFibres adjacent sameColour colouring →
  ProperColouring adjacent sameColour colouring
complementCliqueFibresToColouring adjacent sameColour colouring fibres
  u v distinct connected
  with sameColour (colouring u) (colouring v)
... | false = refl
... | true =
  ⊥-elim
    (Graph.trueAndNegationImpossible
      (adjacent u v)
      connected
      (fibres u v distinct refl))

karpColouringCliqueCoverWitnessIff :
  ∀ {Vertex Colour : Set}
    (adjacent : Vertex → Vertex → Bool)
    (sameColour : Colour → Colour → Bool)
    (colouring : Vertex → Colour) →
  PR.Iff
    (ProperColouring adjacent sameColour colouring)
    (CliqueFibres adjacent sameColour colouring)
karpColouringCliqueCoverWitnessIff adjacent sameColour colouring =
  PR.iff
    (colouringToComplementCliqueFibres adjacent sameColour colouring)
    (complementCliqueFibresToColouring adjacent sameColour colouring)
