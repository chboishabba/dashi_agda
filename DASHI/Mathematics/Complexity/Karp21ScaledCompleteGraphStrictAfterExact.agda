module DASHI.Mathematics.Complexity.Karp21ScaledCompleteGraphStrictAfterExact where

------------------------------------------------------------------------
-- E20 / N21: EXISTING STRICT PARSER BOOLEAN ORDER REFLECTION.
--
-- Original graph parser Decode.strictAfter prev u v returns true
-- precisely for lex-increasing vertex pairs. The previous Karp21
-- UpperPair owners source-write strict numeric lex order for ALL
-- previous/later edges on Gen.completeScaledPairEdges.
--
-- This module converts that strong mathematical relation into actual
-- executable Bool true equalities for the parser's existing comparator.
-- No replacement graph, comparator, source witness or sorting pass.
--
-- The subsequent Fin.fromℕ< reconstructed graph SAME-OBJECT theorem,
-- threshold, and machine verifier clocks remain independent.
-- Attribution: Karp 1972; DASHI existing parser/enumerator owners.
-- Source-written only. Agda kernel acceptance NOT performed.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_<_)
open import Data.Product using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Base using (List; []; _∷_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary.Decidable.Core using (yes; no)
import Data.Nat.Properties as NatP
import Data.Fin.Base as Fin
import Data.Vec.Base as Vec
open import Data.Integer.Base using (ℤ)

import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21FiniteCompleteGraphGeneratorExact as Gen
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Decode
import DASHI.Mathematics.Complexity.Karp21UpperPairStructuralLexOrderExact as Lex
import DASHI.Mathematics.Complexity.Karp21ScaledCompleteGraphStrictLexExact as Order

------------------------------------------------------------------------
-- The actual source-owned comparator uses first-key <, or a tie on
-- the first key and a strict increase of the second key.
------------------------------------------------------------------------

strictAfterRecognizesLex :
  (previousFirst previousSecond nextFirst nextSecond : Nat) →
  (previousFirst < nextFirst)
  ⊎ ((previousFirst ≡ nextFirst) ×
     (previousSecond < nextSecond)) →
  Decode.strictAfter
    (Decode.previous previousFirst previousSecond)
    nextFirst nextSecond ≡ true
strictAfterRecognizesLex a b u v (inj₁ less)
  with NatP._<?_ a u
... | yes _ = refl
... | no notLess = ⊥-elim (notLess less)
strictAfterRecognizesLex a b u v (inj₂ (same , less))
  with NatP._<?_ a u
... | yes _ = refl
... | no notFirst with NatP._≟_ a u
...   | no distinct = ⊥-elim (distinct same)
...   | yes _ with NatP._<?_ b v
...     | yes _ = refl
...     | no notSecond = ⊥-elim (notSecond less)

ParserStrictlyAfterEdge :
  ∀ {n : Nat} →
  Cut.SignedUndirectedEdge n →
  Cut.SignedUndirectedEdge n → Set
ParserStrictlyAfterEdge first second =
  Decode.strictAfter
    (Decode.previous
      (Fin.toℕ (Cut.first first))
      (Fin.toℕ (Cut.second first)))
    (Fin.toℕ (Cut.first second))
    (Fin.toℕ (Cut.second second)) ≡ true

numericLexImpliesActualParserAfter :
  ∀ {n : Nat}
    (first second : Cut.SignedUndirectedEdge n) →
  Order.CanonicalEdgeNumericBefore first second →
  ParserStrictlyAfterEdge first second
numericLexImpliesActualParserAfter first second less =
  strictAfterRecognizesLex
    (Fin.toℕ (Cut.first first))
    (Fin.toℕ (Cut.second first))
    (Fin.toℕ (Cut.first second))
    (Fin.toℕ (Cut.second second))
    less

------------------------------------------------------------------------
-- Relation conversion on the ORIGINAL globally-ordered list. No map
-- and no changed edge identities; this is all-pairs, not adjacent-only.
------------------------------------------------------------------------

allAfterRelationTransport :
  ∀ {A : Set}
    {R S : A → A → Set}
    (transport : ∀ {x y} → R x y → S x y)
    (x : A) (rest : List A) →
  Lex.AllAfter R x rest →
  Lex.AllAfter S x rest
allAfterRelationTransport transport x [] Lex.afterNil =
  Lex.afterNil
allAfterRelationTransport transport x (y ∷ rest)
  (Lex.afterCons before remainder) =
  Lex.afterCons
    (transport before)
    (allAfterRelationTransport transport x rest remainder)

strictSortedRelationTransport :
  ∀ {A : Set}
    {R S : A → A → Set}
    (transport : ∀ {x y} → R x y → S x y)
    (xs : List A) →
  Lex.StrictSorted R xs →
  Lex.StrictSorted S xs
strictSortedRelationTransport transport [] Lex.sortedNil =
  Lex.sortedNil
strictSortedRelationTransport transport (x ∷ rest)
  (Lex.sortedCons earlier sortedRest) =
  Lex.sortedCons
    (allAfterRelationTransport transport x rest earlier)
    (strictSortedRelationTransport transport rest sortedRest)

------------------------------------------------------------------------
-- Every later emitted edge is accepted as strictly later than each
-- earlier edge by the ACTUAL parser Boolean order guard.
------------------------------------------------------------------------

sourceIndexedScaledGraphPassesStrictAfter :
  ∀ {n : Nat} (source : Vec.Vec ℤ n) →
  Lex.StrictSorted ParserStrictlyAfterEdge
    (Gen.completeScaledPairEdges source)
sourceIndexedScaledGraphPassesStrictAfter source =
  strictSortedRelationTransport
    (λ {first} {second} order →
      numericLexImpliesActualParserAfter first second order)
    (Gen.completeScaledPairEdges source)
    (Order.sourceIndexedScaledCompleteGraphStrictLex source)
