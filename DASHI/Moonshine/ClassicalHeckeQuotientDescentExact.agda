module DASHI.Moonshine.ClassicalHeckeQuotientDescentExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Saunders Mac Lane,
-- "Categories for the Working Mathematician", second edition,
-- Graduate Texts in Mathematics 5, Springer, 1998.
-- DOI: 10.1007/978-1-4757-4721-8.
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", Graduate Texts in Mathematics 228,
-- Springer, 2005.
-- DOI: 10.1007/978-0-387-27226-9.
--
-- DASHI CONTRIBUTION
--
-- Give the quotient-natural theorem for the source-faithful variable-degree
-- classical correspondence carrier.  If every one of the ell+1 fine
-- neighbours has quotient class depending only on the quotient class of the
-- source, then the correspondence descends canonically and the finite summed
-- operator commutes with projection.
--
-- This is the classical counterpart of HeckeCorrespondenceQuotientDescentExact
-- and is the theorem intended for a future SO(3)/matched-sector -> Brandt or
-- supersingular-isogeny comparison.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin; zero; suc)

import Ontology.Hecke.QuotientRepresentation as Quotient
import DASHI.Moonshine.HeckeCorrespondenceQuotientDescentExact as ExistingQuotient
import DASHI.Moonshine.ClassicalFiniteHeckeCorrespondenceCore as Classical

record QuotientStableClassicalCorrespondence
    {Fine Coarse : Set}
    (quotient : Quotient.QuotientInterfaceOn Fine Coarse)
    (fine : Classical.ClassicalPrimeDegreeCorrespondence Fine) : Set₁ where
  field
    exactPresentation : ExistingQuotient.ExactQuotientPresentation quotient

    neighbourRespectsEquiv :
      ∀ {left right : Fine} →
      Quotient.EquivalenceOn._≈_
        (Quotient.QuotientInterfaceOn.equiv quotient) left right →
      (edge : Fin (suc (Classical.degreePrime fine))) →
      Quotient.QuotientInterfaceOn.proj quotient
        (Classical.neighbour fine left edge)
      ≡
      Quotient.QuotientInterfaceOn.proj quotient
        (Classical.neighbour fine right edge)

open QuotientStableClassicalCorrespondence public

inducedClassicalCorrespondence :
  ∀ {Fine Coarse : Set}
    {quotient : Quotient.QuotientInterfaceOn Fine Coarse}
    {fine : Classical.ClassicalPrimeDegreeCorrespondence Fine} →
  QuotientStableClassicalCorrespondence quotient fine →
  Classical.ClassicalPrimeDegreeCorrespondence Coarse
inducedClassicalCorrespondence {quotient = quotient} {fine = fine} descent =
  record
    { Classical.degreePrime = Classical.degreePrime fine
    ; Classical.neighbour = λ coarse edge →
        Quotient.QuotientInterfaceOn.proj quotient
          (Classical.neighbour fine
            (Quotient.QuotientInterfaceOn.representative quotient coarse)
            edge)
    }

projectedNeighbourCommutes :
  ∀ {Fine Coarse : Set}
    {quotient : Quotient.QuotientInterfaceOn Fine Coarse}
    {fine : Classical.ClassicalPrimeDegreeCorrespondence Fine}
    (descent : QuotientStableClassicalCorrespondence quotient fine)
    (state : Fine)
    (edge : Fin (suc (Classical.degreePrime fine))) →
  Quotient.QuotientInterfaceOn.proj quotient
    (Classical.neighbour fine state edge)
  ≡
  Classical.neighbour (inducedClassicalCorrespondence descent)
    (Quotient.QuotientInterfaceOn.proj quotient state) edge
projectedNeighbourCommutes
  {quotient = quotient} descent state edge =
  neighbourRespectsEquiv descent
    (ExistingQuotient.projectionComplete (exactPresentation descent)
      (sym
        (Quotient.QuotientInterfaceOn.section quotient
          (Quotient.QuotientInterfaceOn.proj quotient state))))
    edge

------------------------------------------------------------------------
-- Finite fold extensionality.
------------------------------------------------------------------------

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

projectedClassicalOperatorCommutes :
  ∀ {Fine Coarse : Set}
    {quotient : Quotient.QuotientInterfaceOn Fine Coarse}
    {fine : Classical.ClassicalPrimeDegreeCorrespondence Fine}
    (descent : QuotientStableClassicalCorrespondence quotient fine)
    (observable : Coarse → Nat)
    (state : Fine) →
  Classical.classicalOperator fine
    (λ fineState → observable
      (Quotient.QuotientInterfaceOn.proj quotient fineState))
    state
  ≡
  Classical.classicalOperator (inducedClassicalCorrespondence descent)
    observable
    (Quotient.QuotientInterfaceOn.proj quotient state)
projectedClassicalOperatorCommutes
  {quotient = quotient} {fine = fine}
  descent observable state =
  foldFinPointwise
    (λ edge → observable
      (Quotient.QuotientInterfaceOn.proj quotient
        (Classical.neighbour fine state edge)))
    (λ edge → observable
      (Classical.neighbour (inducedClassicalCorrespondence descent)
        (Quotient.QuotientInterfaceOn.proj quotient state) edge))
    (λ edge → cong observable (projectedNeighbourCommutes descent state edge))

record ClassicalHeckeQuotientBoundary : Set where
  field
    classicalVariableDegreeQuotientDescentConstructed : Bool
    classicalVariableDegreeQuotientDescentConstructedIsTrue :
      classicalVariableDegreeQuotientDescentConstructed ≡ true

    operatorCommutationDerivedFromNeighbourCongruence : Bool
    operatorCommutationDerivedFromNeighbourCongruenceIsTrue :
      operatorCommutationDerivedFromNeighbourCongruence ≡ true

    geometricBrandtRealizationConstructedHere : Bool
    geometricBrandtRealizationConstructedHereIsFalse :
      geometricBrandtRealizationConstructedHere ≡ false

canonicalClassicalHeckeQuotientBoundary : ClassicalHeckeQuotientBoundary
canonicalClassicalHeckeQuotientBoundary =
  record
    { classicalVariableDegreeQuotientDescentConstructed = true
    ; classicalVariableDegreeQuotientDescentConstructedIsTrue = refl
    ; operatorCommutationDerivedFromNeighbourCongruence = true
    ; operatorCommutationDerivedFromNeighbourCongruenceIsTrue = refl
    ; geometricBrandtRealizationConstructedHere = false
    ; geometricBrandtRealizationConstructedHereIsFalse = refl
    }
