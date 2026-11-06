module DASHI.Mathematics.Complexity.Karp21FiniteColouringCliqueCoverExact where

------------------------------------------------------------------------
-- HISTORICAL ROOT: Karp (1972), CHROMATIC NUMBER -> CLIQUE COVER,
-- DOI 10.1007/978-1-4684-2001-2_9.
--
-- DASHI: all-palette/all-graph constructive existential witness iff on
-- a finite, symmetric, loop-free graph, using exactly the same labelled
-- graph complement as E05. Colouring assignments are Vec (Fin k) n,
-- and positions remain distinct even if names/labels coincide.
--
-- This is NOT the binary serialization or polynomial-clock theorem.
-- In particular k can be binary encoded in a real source word, so
-- enumerate-colour constructions must carry explicit k>n guards.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (sym; trans)
open import Relation.Nullary.Decidable.Core using (yes; no)

import Data.Fin.Base as Fin
import Data.Fin.Properties as FinP
import Data.Vec.Base as Vec
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.Karp21ColouringCliqueCoverExact as Old
import DASHI.Mathematics.Complexity.Karp21SimpleGraphComplementExact as Simple

samePaletteColour :
  ∀ {k} → Fin.Fin k → Fin.Fin k → Bool
samePaletteColour left right
  with FinP._≟_ left right
... | yes _ = true
... | no _ = false

samePaletteColourReflexive :
  ∀ {k} (colour : Fin.Fin k) →
  samePaletteColour colour colour ≡ true
samePaletteColourReflexive colour
  with FinP._≟_ colour colour
... | yes _ = refl
... | no unequal = ⊥-elim (unequal refl)

samePaletteColourTrueImpliesEqual :
  ∀ {k} (left right : Fin.Fin k) →
  samePaletteColour left right ≡ true →
  left ≡ right
samePaletteColourTrueImpliesEqual left right observed
  with FinP._≟_ left right
... | yes equal = equal
... | no _ with observed
...   | ()

-- Exactly one palette colour for each finite vertex position.
ColourLabels : Nat → Nat → Set
ColourLabels n k = Vec.Vec (Fin.Fin k) n

FiniteProperColouring :
  ∀ {n k} →
  Simple.SimpleGraph n →
  ColourLabels n k → Set
FiniteProperColouring graph colours =
  Old.ProperColouring
    (Simple.adjacency graph)
    samePaletteColour
    (Vec.lookup colours)

FiniteSimpleCliqueCover :
  ∀ {n k} →
  Simple.SimpleGraph n →
  ColourLabels n k → Set
FiniteSimpleCliqueCover {n} graph colours =
  ∀ u v → (u ≡ v → ⊥) →
  samePaletteColour (Vec.lookup colours u)
                    (Vec.lookup colours v) ≡ true →
  Simple.simpleComplementAdjacency graph u v ≡ true

colouringToSimpleCliqueCover :
  ∀ {n k} (graph : Simple.SimpleGraph n)
    (colours : ColourLabels n k) →
  FiniteProperColouring graph colours →
  FiniteSimpleCliqueCover graph colours
colouringToSimpleCliqueCover graph colours proper u v distinct same =
  trans
    (Simple.simpleComplementOffDiagonal graph u v distinct)
    (Old.colouringToComplementCliqueFibres
      (Simple.adjacency graph)
      samePaletteColour
      (Vec.lookup colours)
      proper u v distinct same)

simpleCliqueCoverToColouring :
  ∀ {n k} (graph : Simple.SimpleGraph n)
    (colours : ColourLabels n k) →
  FiniteSimpleCliqueCover graph colours →
  FiniteProperColouring graph colours
simpleCliqueCoverToColouring graph colours cover =
  Old.complementCliqueFibresToColouring
    (Simple.adjacency graph)
    samePaletteColour
    (Vec.lookup colours)
    (λ u v distinct same →
      trans
        (sym (Simple.simpleComplementOffDiagonal graph u v distinct))
        (cover u v distinct same))

FiniteColouringYES :
  ∀ {n} → Simple.SimpleGraph n → (k : Nat) → Set
FiniteColouringYES {n} graph k =
  Σ (ColourLabels n k) (FiniteProperColouring graph)

FiniteCliqueCoverYES :
  ∀ {n} → Simple.SimpleGraph n → (k : Nat) → Set
FiniteCliqueCoverYES {n} graph k =
  Σ (ColourLabels n k) (FiniteSimpleCliqueCover graph)

finiteColouringToCliqueCoverYES :
  ∀ {n} (graph : Simple.SimpleGraph n) (k : Nat) →
  FiniteColouringYES graph k →
  FiniteCliqueCoverYES graph k
finiteColouringToCliqueCoverYES graph k (colours , proper) =
  colours , colouringToSimpleCliqueCover graph colours proper

finiteCliqueCoverToColouringYES :
  ∀ {n} (graph : Simple.SimpleGraph n) (k : Nat) →
  FiniteCliqueCoverYES graph k →
  FiniteColouringYES graph k
finiteCliqueCoverToColouringYES graph k (colours , cover) =
  colours , simpleCliqueCoverToColouring graph colours cover

karpFiniteColouringCliqueCoverInstanceIff :
  ∀ {n} (graph : Simple.SimpleGraph n) (k : Nat) →
  PR.Iff
    (FiniteColouringYES graph k)
    (FiniteCliqueCoverYES graph k)
karpFiniteColouringCliqueCoverInstanceIff graph k =
  PR.iff
    (finiteColouringToCliqueCoverYES graph k)
    (finiteCliqueCoverToColouringYES graph k)
