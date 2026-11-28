module DASHI.Moonshine.PrimeRegularHeckeLocalGeometryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "Trees", Springer Monographs in Mathematics, corrected second printing.
-- DOI: 10.1007/978-3-642-61856-7.
--
-- John Voight,
-- "Quaternion Algebras", Graduate Texts in Mathematics 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
--
-- DASHI CONTRIBUTION
--
-- Isolate only the local positive geometry common to an unramified prime
-- Hecke correspondence / Bruhat--Tits tree: at local prime ell every vertex
-- has ell+1 outgoing neighbour slots.  This file does NOT identify an arbitrary
-- such system with a Bruhat--Tits tree or quaternion double-coset quotient;
-- those require an explicit group/arithmetic action map.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin)

import DASHI.Moonshine.PositiveFiniteNeighbourSystemExact as Positive

record PrimeRegularHeckeLocalGeometry (Vertex : Set) (ell : Nat) : Set₁ where
  field
    neighbour : Vertex → Fin (suc ell) → Vertex

open PrimeRegularHeckeLocalGeometry public

asPositiveNeighbourSystem :
  ∀ {Vertex : Set} {ell : Nat} →
  PrimeRegularHeckeLocalGeometry Vertex ell →
  Positive.PositiveFiniteNeighbourSystem Vertex
asPositiveNeighbourSystem {ell = ell} geometry = record
  { Positive.arity = suc ell
  ; Positive.neighbour = neighbour geometry
  }

localArity :
  ∀ {Vertex : Set} {ell : Nat} →
  PrimeRegularHeckeLocalGeometry Vertex ell → Nat
localArity {ell = ell} geometry = suc ell

ell2LocalArityIsThree :
  ∀ {Vertex : Set}
    (geometry : PrimeRegularHeckeLocalGeometry Vertex 2) →
  localArity geometry ≡ 3
ell2LocalArityIsThree geometry = refl

ell3LocalArityIsFour :
  ∀ {Vertex : Set}
    (geometry : PrimeRegularHeckeLocalGeometry Vertex 3) →
  localArity geometry ≡ 4
ell3LocalArityIsFour geometry = refl

ell5LocalArityIsSix :
  ∀ {Vertex : Set}
    (geometry : PrimeRegularHeckeLocalGeometry Vertex 5) →
  localArity geometry ≡ 6
ell5LocalArityIsSix geometry = refl

record PrimeRegularHeckeLocalBoundary : Set where
  field
    ellPlusOnePositiveLocalCarrierConstructed : Bool
    ellPlusOnePositiveLocalCarrierConstructedIsTrue :
      ellPlusOnePositiveLocalCarrierConstructed ≡ true

    ell2TernaryValencyExact : Bool
    ell2TernaryValencyExactIsTrue : ell2TernaryValencyExact ≡ true

    ell3AndEll5NotTernary : Bool
    ell3AndEll5NotTernaryIsTrue : ell3AndEll5NotTernary ≡ true

    arbitraryLocalSystemPromotedToBruhatTitsTree : Bool
    arbitraryLocalSystemPromotedToBruhatTitsTreeIsFalse :
      arbitraryLocalSystemPromotedToBruhatTitsTree ≡ false

canonicalPrimeRegularHeckeLocalBoundary : PrimeRegularHeckeLocalBoundary
canonicalPrimeRegularHeckeLocalBoundary = record
  { ellPlusOnePositiveLocalCarrierConstructed = true
  ; ellPlusOnePositiveLocalCarrierConstructedIsTrue = refl
  ; ell2TernaryValencyExact = true
  ; ell2TernaryValencyExactIsTrue = refl
  ; ell3AndEll5NotTernary = true
  ; ell3AndEll5NotTernaryIsTrue = refl
  ; arbitraryLocalSystemPromotedToBruhatTitsTree = false
  ; arbitraryLocalSystemPromotedToBruhatTitsTreeIsFalse = refl
  }
