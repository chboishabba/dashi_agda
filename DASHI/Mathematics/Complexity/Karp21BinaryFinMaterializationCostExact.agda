{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21BinaryFinMaterializationCostExact where

------------------------------------------------------------------------
-- N21 CONCRETE MACHINE-CLOCK OBSTRUCTION: EXPLICIT FIN REPRESENTATION.
--
-- Original grammar encodes a vertex index u by Elias gamma(u+1),
-- with O(log(u+1)) input bits. The original dependent decoder calls
-- Data.Fin.Base.fromℕ<, which constructs a unary inductive Fin value.
--
-- This module proves EXACTLY that its explicit constructor-tree
-- depth is suc u, not O(log u). This does NOT prove a universal lower
-- bound on every possible compiler/erasure backend, but it prevents
-- using the direct inductive Fin constructor traversal as an unargued
-- polynomial bit-tape implementation.
--
-- Consequence for P1: the polynomial N21 verifier must operate on a
-- BINARY-native endpoint-address representation and the sparse 2m
-- witness. Use the original Python binary codec and DASHI Agda Fin
-- semantics as different *representation layers*, joined by an
-- observational theorem; never allocate a full n-vertex label vector.
--
-- This module is source-written only and requires Agda --safe
-- kernel acceptance. Attribution: Agda stdlib Fin properties and
-- DASHI original N21 gamma/Fin decoder owners; Karp (1972).
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_<_)
open import Relation.Binary.PropositionalEquality using (cong; trans)
import Data.Nat.Properties as NatP
import Data.Fin.Base as Fin
import Data.Fin.Properties as FinP

-- Number of explicit constructors in the value's inductive syntax:
-- one zero plus one for every suc. The erased bound n is not counted.
finConstructorDepth :
  ∀ {n : Nat} → Fin.Fin n → Nat
finConstructorDepth Fin.zero = suc zero
finConstructorDepth (Fin.suc index) =
  suc (finConstructorDepth index)

finConstructorDepthExact :
  ∀ {n : Nat} (index : Fin.Fin n) →
  finConstructorDepth index ≡ suc (Fin.toℕ index)
finConstructorDepthExact Fin.zero = refl
finConstructorDepthExact (Fin.suc index) =
  cong suc (finConstructorDepthExact index)

-- This is the ACTUAL Fin.fromℕ< used by validateRawEdges, not a
-- second or hypothetical decoder with hand-picked cost fields.
decodedFinConstructorDepthExact :
  ∀ {n u : Nat} (bound : u < n) →
  finConstructorDepth (Fin.fromℕ< bound) ≡ suc u
decodedFinConstructorDepthExact bound =
  trans
    (finConstructorDepthExact (Fin.fromℕ< bound))
    (cong suc (FinP.toℕ-fromℕ< bound))

-- For an edge using the largest address in Fin(suc u), its explicit
-- returned vertex needs exactly suc u constructors even if the
-- binary gamma word encoding u is very short.
lastVertexConstructorDepth :
  (u : Nat) →
  finConstructorDepth
    (Fin.fromℕ< (NatP.≤-refl {x = suc u})) ≡ suc u
lastVertexConstructorDepth u =
  decodedFinConstructorDepthExact (NatP.≤-refl {x = suc u})
