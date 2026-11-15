{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21FinDecoderIndexBidiExact where

------------------------------------------------------------------------
-- E20/N21 exact finite-index decoder reconstruction.
--
-- The existing gamma graph parser uses Fin.fromℕ< after proving
-- u < v < n. The original graph uses Fin n endpoint objects.
-- Their *numeric* addresses determine the Fin objects uniquely:
-- the particular choice of a bound proof must not change the index.
--
-- This is the actual Agda stdlib Fin carrier, not a new vertex type.
-- No graph imports, postulates or proof-function extensionality.
--
-- Reuse: Data.Fin.Properties.toℕ-fromℕ< / toℕ-injective / toℕ<n.
-- Source attribution: Agda standard-library Fin maintainers;
-- original DASHI E20/N21 gamma graph-parser and weighted-graph owners.
-- Kernel acceptance remains to be checked independently.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat.Base using (_<_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
import Data.Nat.Properties as NatP
import Data.Fin.Base as Fin
import Data.Fin.Properties as FinP
import Data.Vec.Base as Vec

-- Arbitrary well-founded bounds on the SAME original endpoint yield
-- the SAME Fin index. No equality of the inequality proof is needed.
reconstructOriginalFin :
  ∀ {n : Nat} (index : Fin.Fin n)
    (inRange : Fin.toℕ index < n) →
  Fin.fromℕ< inRange ≡ index
reconstructOriginalFin index inRange =
  FinP.toℕ-injective (FinP.toℕ-fromℕ< inRange)

reconstructCanonicalFin :
  ∀ {n : Nat} (index : Fin.Fin n) →
  Fin.fromℕ< (FinP.toℕ<n index) ≡ index
reconstructCanonicalFin index =
  reconstructOriginalFin index (FinP.toℕ<n index)

-- Exactly the first endpoint expression used inside the original
-- validateRawEdges, when u and v come from original Fin endpoints.
reconstructOrderedFirst :
  ∀ {n : Nat} (first second : Fin.Fin n)
    (firstBeforeSecond : Fin.toℕ first < Fin.toℕ second) →
  Fin.fromℕ<
    (NatP.<-trans firstBeforeSecond (FinP.toℕ<n second))
    ≡ first
reconstructOrderedFirst first second firstBeforeSecond =
  reconstructOriginalFin first
    (NatP.<-trans firstBeforeSecond (FinP.toℕ<n second))

-- Exactly the second endpoint expression in the same validator.
reconstructOrderedSecond :
  ∀ {n : Nat} (second : Fin.Fin n)
    (inRange : Fin.toℕ second < n) →
  Fin.fromℕ< inRange ≡ second
reconstructOrderedSecond second inRange =
  reconstructOriginalFin second inRange

-- The decoder's choice of a successful numerical range proof has no
-- effect on vertex lookup. This is the property cut scoring needs,
-- rather than a literal equality of offDiagonal impossibility fields.
lookupAfterReconstruction :
  ∀ {n : Nat} {A : Set}
    (values : Vec.Vec A n)
    (index : Fin.Fin n)
    (inRange : Fin.toℕ index < n) →
  Vec.lookup values (Fin.fromℕ< inRange)
    ≡ Vec.lookup values index
lookupAfterReconstruction values index inRange =
  cong (Vec.lookup values)
    (reconstructOriginalFin index inRange)

-- Any two successful in-range proofs decode to the same endpoint.
reconstructProofIndependent :
  ∀ {n : Nat}
    (index : Fin.Fin n)
    (firstBound secondBound : Fin.toℕ index < n) →
  Fin.fromℕ< firstBound ≡ Fin.fromℕ< secondBound
reconstructProofIndependent index firstBound secondBound =
  trans
    (reconstructOriginalFin index firstBound)
    (sym (reconstructOriginalFin index secondBound))
