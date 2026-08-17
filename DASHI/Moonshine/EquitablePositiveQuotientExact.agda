module DASHI.Moonshine.EquitablePositiveQuotientExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Chris Godsil and Gordon Royle,
-- "Algebraic Graph Theory", Graduate Texts in Mathematics 207,
-- Springer, 2001.
-- DOI: 10.1007/978-1-4613-0163-9.
--
-- Jean-Pierre Serre,
-- "Trees", Springer Monographs in Mathematics.
-- DOI: 10.1007/978-3-642-61856-7.
--
-- DASHI CONTRIBUTION
--
-- Extract the quotient notion appropriate to positive graph/Schreier geometry.
-- The earlier neighbour-by-neighbour quotient theorem is intentionally strong:
-- edge label i must project to edge label i.  A genuine graph quotient usually
-- needs only EQUITABILITY: vertices in one fibre have the same total neighbour
-- counts into every coarse fibre.
--
-- We express that invariant without assuming a particular finite enumeration of
-- coarse classes: every Nat-valued coarse observable has the same pulled-back
-- positive operator value on fine vertices in the same fibre.
--
-- From this one obtains a canonical induced positive OPERATOR on the coarse
-- carrier by evaluating at the quotient representative, together with the exact
-- commuting square
--
--   T_fine (f o proj) = T_coarse f o proj.
--
-- Unlike the labelled-neighbour theorem, this does not claim that individual
-- generator labels descend.  That distinction is essential for Schreier and
-- double-coset quotients.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import Ontology.Hecke.QuotientRepresentation as Quotient
import DASHI.Moonshine.PositiveFiniteNeighbourSystemExact as Positive

record EquitablePositiveQuotient
    {Fine Coarse : Set}
    (quotient : Quotient.QuotientInterfaceOn Fine Coarse)
    (fine : Positive.PositiveFiniteNeighbourSystem Fine) : Set₁ where
  field
    coarseObservableCongruent :
      ∀ {left right : Fine} →
      Quotient.QuotientInterfaceOn.proj quotient left
      ≡ Quotient.QuotientInterfaceOn.proj quotient right →
      (observable : Coarse → Nat) →
      Positive.positiveOperator fine
        (λ state → observable
          (Quotient.QuotientInterfaceOn.proj quotient state)) left
      ≡
      Positive.positiveOperator fine
        (λ state → observable
          (Quotient.QuotientInterfaceOn.proj quotient state)) right

open EquitablePositiveQuotient public

inducedEquitableOperator :
  ∀ {Fine Coarse : Set}
    {quotient : Quotient.QuotientInterfaceOn Fine Coarse}
    {fine : Positive.PositiveFiniteNeighbourSystem Fine} →
  EquitablePositiveQuotient quotient fine →
  (Coarse → Nat) → Coarse → Nat
inducedEquitableOperator {quotient = quotient} {fine = fine} equitable observable coarse =
  Positive.positiveOperator fine
    (λ state → observable
      (Quotient.QuotientInterfaceOn.proj quotient state))
    (Quotient.QuotientInterfaceOn.representative quotient coarse)

projectedEquitableOperatorCommutes :
  ∀ {Fine Coarse : Set}
    {quotient : Quotient.QuotientInterfaceOn Fine Coarse}
    {fine : Positive.PositiveFiniteNeighbourSystem Fine}
    (equitable : EquitablePositiveQuotient quotient fine)
    (observable : Coarse → Nat)
    (state : Fine) →
  Positive.positiveOperator fine
    (λ fineState → observable
      (Quotient.QuotientInterfaceOn.proj quotient fineState)) state
  ≡
  inducedEquitableOperator equitable observable
    (Quotient.QuotientInterfaceOn.proj quotient state)
projectedEquitableOperatorCommutes
  {quotient = quotient} equitable observable state =
  coarseObservableCongruent equitable
    (sym
      (Quotient.QuotientInterfaceOn.section quotient
        (Quotient.QuotientInterfaceOn.proj quotient state)))
    observable

------------------------------------------------------------------------
-- Labelled descent implies equitable descent, but not conversely in general.
-- We keep the strict implication as a boundary statement rather than asserting
-- a false equivalence between the two quotient notions.
------------------------------------------------------------------------

record EquitablePositiveQuotientBoundary : Set where
  field
    aggregateGraphQuotientConstructed : Bool
    aggregateGraphQuotientConstructedIsTrue :
      aggregateGraphQuotientConstructed ≡ true

    inducedCoarseOperatorConstructed : Bool
    inducedCoarseOperatorConstructedIsTrue :
      inducedCoarseOperatorConstructed ≡ true

    exactOperatorCommutingSquareConstructed : Bool
    exactOperatorCommutingSquareConstructedIsTrue :
      exactOperatorCommutingSquareConstructed ≡ true

    individualEdgeLabelsRequiredToDescend : Bool
    individualEdgeLabelsRequiredToDescendIsFalse :
      individualEdgeLabelsRequiredToDescend ≡ false

    equitableQuotientIdentifiedWithBruhatTitsHere : Bool
    equitableQuotientIdentifiedWithBruhatTitsHereIsFalse :
      equitableQuotientIdentifiedWithBruhatTitsHere ≡ false

canonicalEquitablePositiveQuotientBoundary : EquitablePositiveQuotientBoundary
canonicalEquitablePositiveQuotientBoundary =
  record
    { aggregateGraphQuotientConstructed = true
    ; aggregateGraphQuotientConstructedIsTrue = refl
    ; inducedCoarseOperatorConstructed = true
    ; inducedCoarseOperatorConstructedIsTrue = refl
    ; exactOperatorCommutingSquareConstructed = true
    ; exactOperatorCommutingSquareConstructedIsTrue = refl
    ; individualEdgeLabelsRequiredToDescend = false
    ; individualEdgeLabelsRequiredToDescendIsFalse = refl
    ; equitableQuotientIdentifiedWithBruhatTitsHere = false
    ; equitableQuotientIdentifiedWithBruhatTitsHereIsFalse = refl
    }
