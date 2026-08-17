module DASHI.Moonshine.PositiveNeighbourQuotientDescentExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Saunders Mac Lane,
-- "Categories for the Working Mathematician", second edition,
-- Graduate Texts in Mathematics 5, Springer, 1998.
-- DOI: 10.1007/978-1-4757-4721-8.
--
-- Jean-Pierre Serre,
-- "Trees", Springer Monographs in Mathematics.
-- DOI: 10.1007/978-3-642-61856-7.
--
-- DASHI CONTRIBUTION
--
-- Generalize ClassicalHeckeQuotientDescentExact from prime-degree fibres to an
-- arbitrary positive finite neighbour system.  This is the exact theorem shape
-- needed by a finite tree / Schreier / double-coset producer:
--
--   fine positive geometry
--       -> quotient-stable neighbours
--       -> positive quotient geometry
--       -> commuting adjacency/operator square.
--
-- Positivity is preserved definitionally because both fine and coarse systems
-- are lists of actual neighbours; no signed matrix lift occurs anywhere.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin; zero; suc)

import Ontology.Hecke.QuotientRepresentation as Quotient
import DASHI.Moonshine.HeckeCorrespondenceQuotientDescentExact as Existing
import DASHI.Moonshine.ClassicalFiniteHeckeCorrespondenceCore as Classical
import DASHI.Moonshine.PositiveFiniteNeighbourSystemExact as Positive

record QuotientStablePositiveNeighbourSystem
    {Fine Coarse : Set}
    (quotient : Quotient.QuotientInterfaceOn Fine Coarse)
    (fine : Positive.PositiveFiniteNeighbourSystem Fine) : Set₁ where
  field
    exactPresentation : Existing.ExactQuotientPresentation quotient

    neighbourRespectsEquiv :
      ∀ {left right : Fine} →
      Quotient.EquivalenceOn._≈_
        (Quotient.QuotientInterfaceOn.equiv quotient) left right →
      (edge : Fin (Positive.arity fine)) →
      Quotient.QuotientInterfaceOn.proj quotient
        (Positive.neighbour fine left edge)
      ≡
      Quotient.QuotientInterfaceOn.proj quotient
        (Positive.neighbour fine right edge)

open QuotientStablePositiveNeighbourSystem public

inducedPositiveNeighbourSystem :
  ∀ {Fine Coarse : Set}
    {quotient : Quotient.QuotientInterfaceOn Fine Coarse}
    {fine : Positive.PositiveFiniteNeighbourSystem Fine} →
  QuotientStablePositiveNeighbourSystem quotient fine →
  Positive.PositiveFiniteNeighbourSystem Coarse
inducedPositiveNeighbourSystem {quotient = quotient} {fine = fine} descent =
  record
    { Positive.arity = Positive.arity fine
    ; Positive.neighbour = λ coarse edge →
        Quotient.QuotientInterfaceOn.proj quotient
          (Positive.neighbour fine
            (Quotient.QuotientInterfaceOn.representative quotient coarse)
            edge)
    }

projectedPositiveNeighbourCommutes :
  ∀ {Fine Coarse : Set}
    {quotient : Quotient.QuotientInterfaceOn Fine Coarse}
    {fine : Positive.PositiveFiniteNeighbourSystem Fine}
    (descent : QuotientStablePositiveNeighbourSystem quotient fine)
    (state : Fine)
    (edge : Fin (Positive.arity fine)) →
  Quotient.QuotientInterfaceOn.proj quotient
    (Positive.neighbour fine state edge)
  ≡
  Positive.neighbour (inducedPositiveNeighbourSystem descent)
    (Quotient.QuotientInterfaceOn.proj quotient state) edge
projectedPositiveNeighbourCommutes
  {quotient = quotient} descent state edge =
  neighbourRespectsEquiv descent
    (Existing.projectionComplete (exactPresentation descent)
      (sym
        (Quotient.QuotientInterfaceOn.section quotient
          (Quotient.QuotientInterfaceOn.proj quotient state))))
    edge

foldFinPointwise :
  ∀ {n : Nat}
    (left right : Fin n → Nat) →
    ((edge : Fin n) → left edge ≡ right edge) →
  Classical.foldFin _+_ 0 left ≡ Classical.foldFin _+_ 0 right
foldFinPointwise {zero} left right pointwise = refl
foldFinPointwise {suc n} left right pointwise
  rewrite pointwise zero
        | foldFinPointwise
            (λ edge → left (suc edge))
            (λ edge → right (suc edge))
            (λ edge → pointwise (suc edge))
  = refl

projectedPositiveOperatorCommutes :
  ∀ {Fine Coarse : Set}
    {quotient : Quotient.QuotientInterfaceOn Fine Coarse}
    {fine : Positive.PositiveFiniteNeighbourSystem Fine}
    (descent : QuotientStablePositiveNeighbourSystem quotient fine)
    (observable : Coarse → Nat)
    (state : Fine) →
  Positive.positiveOperator fine
    (λ fineState → observable
      (Quotient.QuotientInterfaceOn.proj quotient fineState))
    state
  ≡
  Positive.positiveOperator (inducedPositiveNeighbourSystem descent)
    observable
    (Quotient.QuotientInterfaceOn.proj quotient state)
projectedPositiveOperatorCommutes
  {quotient = quotient} {fine = fine}
  descent observable state =
  foldFinPointwise
    (λ edge → observable
      (Quotient.QuotientInterfaceOn.proj quotient
        (Positive.neighbour fine state edge)))
    (λ edge → observable
      (Positive.neighbour (inducedPositiveNeighbourSystem descent)
        (Quotient.QuotientInterfaceOn.proj quotient state) edge))
    (λ edge → cong observable
      (projectedPositiveNeighbourCommutes descent state edge))

record PositiveNeighbourQuotientBoundary : Set where
  field
    arbitraryArityPositiveQuotientDescentConstructed : Bool
    arbitraryArityPositiveQuotientDescentConstructedIsTrue :
      arbitraryArityPositiveQuotientDescentConstructed ≡ true

    individualNeighbourCommutationConstructed : Bool
    individualNeighbourCommutationConstructedIsTrue :
      individualNeighbourCommutationConstructed ≡ true

    summedPositiveOperatorCommutationConstructed : Bool
    summedPositiveOperatorCommutationConstructedIsTrue :
      summedPositiveOperatorCommutationConstructed ≡ true

    positivityNeedsSeparateMatrixProof : Bool
    positivityNeedsSeparateMatrixProofIsFalse :
      positivityNeedsSeparateMatrixProof ≡ false

    bruHatTitsIdentificationConstructedHere : Bool
    bruHatTitsIdentificationConstructedHereIsFalse :
      bruHatTitsIdentificationConstructedHere ≡ false

canonicalPositiveNeighbourQuotientBoundary : PositiveNeighbourQuotientBoundary
canonicalPositiveNeighbourQuotientBoundary =
  record
    { arbitraryArityPositiveQuotientDescentConstructed = true
    ; arbitraryArityPositiveQuotientDescentConstructedIsTrue = refl
    ; individualNeighbourCommutationConstructed = true
    ; individualNeighbourCommutationConstructedIsTrue = refl
    ; summedPositiveOperatorCommutationConstructed = true
    ; summedPositiveOperatorCommutationConstructedIsTrue = refl
    ; positivityNeedsSeparateMatrixProof = false
    ; positivityNeedsSeparateMatrixProofIsFalse = refl
    ; bruHatTitsIdentificationConstructedHere = false
    ; bruHatTitsIdentificationConstructedHereIsFalse = refl
    }
