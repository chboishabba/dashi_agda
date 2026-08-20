module DASHI.Moonshine.HeckeCorrespondenceQuotientDescentExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Saunders Mac Lane,
-- "Categories for the Working Mathematician", second edition,
-- Graduate Texts in Mathematics 5, Springer, 1998.
-- DOI: 10.1007/978-1-4757-4721-8.
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
--
-- DASHI CONTRIBUTION
--
-- Extend the repository's existing Ontology.Hecke.QuotientRepresentation API
-- from deterministic prime transports to the actual finite 15-way
-- PrimeCorrespondenceHeckeOn carrier.
--
-- If an existing QuotientInterfaceOn has projection-complete fibres and the
-- projected correspondence respects its equivalence relation, then the fine
-- correspondence canonically descends to the quotient.  The resulting finite
-- Hecke observable operator obeys
--
--   T_fine (f o proj) = T_quotient f o proj
--
-- exactly for every Nat-valued quotient observable f.
--
-- This turns a large part of the open representation/Hecke intertwiner into a
-- quotient-well-definedness theorem.  A domain-specific proof must still show
-- that its representation reduction really produces the intended arithmetic
-- quotient correspondence; this module does not manufacture that bridge.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Ontology.GodelLattice using (Vec15)
open import Ontology.GodelLattice renaming (v15 to mkVec15)

import MonsterOntos as Monster
import Ontology.Hecke.CorrespondenceRepresentation as Hecke
import Ontology.Hecke.QuotientRepresentation as Quotient

------------------------------------------------------------------------
-- Vec15 functoriality used by the actual finite Hecke operator.
------------------------------------------------------------------------

map15Fusion :
  ∀ {A B C : Set}
    (f : B → C)
    (g : A → B)
    (values : Vec15 A) →
  Hecke.map15 f (Hecke.map15 g values)
  ≡ Hecke.map15 (λ value → f (g value)) values
map15Fusion f g
  (mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71) =
  refl

------------------------------------------------------------------------
-- Exact quotient presentation: the existing quotient projection both respects
-- and reflects the declared equivalence.  This is true for the repository's
-- equality quotient and support-mask quotient instances.
------------------------------------------------------------------------

record ExactQuotientPresentation
    {Fine Coarse : Set}
    (quotient : Quotient.QuotientInterfaceOn Fine Coarse) : Set₁ where
  field
    projectionComplete :
      ∀ {left right : Fine} →
      Quotient.QuotientInterfaceOn.proj quotient left
      ≡ Quotient.QuotientInterfaceOn.proj quotient right →
      Quotient.EquivalenceOn._≈_
        (Quotient.QuotientInterfaceOn.equiv quotient) left right

open ExactQuotientPresentation public

------------------------------------------------------------------------
-- The exact well-definedness condition for quotienting a correspondence.
------------------------------------------------------------------------

record QuotientStablePrimeCorrespondence
    {Fine Coarse : Set}
    (quotient : Quotient.QuotientInterfaceOn Fine Coarse)
    (fineHecke : Hecke.PrimeCorrespondenceHeckeOn Fine) : Set₁ where
  field
    exactPresentation : ExactQuotientPresentation quotient

    correspondenceRespectsEquiv :
      (prime : Monster.SSP) →
      ∀ {left right : Fine} →
      Quotient.EquivalenceOn._≈_
        (Quotient.QuotientInterfaceOn.equiv quotient) left right →
      Hecke.map15 (Quotient.QuotientInterfaceOn.proj quotient)
        (Hecke.PrimeCorrespondenceHeckeOn.correspondence fineHecke prime left)
      ≡
      Hecke.map15 (Quotient.QuotientInterfaceOn.proj quotient)
        (Hecke.PrimeCorrespondenceHeckeOn.correspondence fineHecke prime right)

open QuotientStablePrimeCorrespondence public

inducedCorrespondence :
  ∀ {Fine Coarse : Set}
    {quotient : Quotient.QuotientInterfaceOn Fine Coarse}
    {fineHecke : Hecke.PrimeCorrespondenceHeckeOn Fine} →
  QuotientStablePrimeCorrespondence quotient fineHecke →
  Monster.SSP → Coarse → Vec15 Coarse
inducedCorrespondence
  {quotient = quotient} {fineHecke = fineHecke}
  descent prime coarse =
  Hecke.map15 (Quotient.QuotientInterfaceOn.proj quotient)
    (Hecke.PrimeCorrespondenceHeckeOn.correspondence fineHecke prime
      (Quotient.QuotientInterfaceOn.representative quotient coarse))

inducedHecke :
  ∀ {Fine Coarse : Set}
    {quotient : Quotient.QuotientInterfaceOn Fine Coarse}
    {fineHecke : Hecke.PrimeCorrespondenceHeckeOn Fine} →
  QuotientStablePrimeCorrespondence quotient fineHecke →
  Hecke.PrimeCorrespondenceHeckeOn Coarse
inducedHecke descent =
  record
    { correspondence = inducedCorrespondence descent
    }

------------------------------------------------------------------------
-- The correspondence square commutes exactly.
------------------------------------------------------------------------

projectedCorrespondenceCommutes :
  ∀ {Fine Coarse : Set}
    {quotient : Quotient.QuotientInterfaceOn Fine Coarse}
    {fineHecke : Hecke.PrimeCorrespondenceHeckeOn Fine}
    (descent : QuotientStablePrimeCorrespondence quotient fineHecke)
    (prime : Monster.SSP)
    (fine : Fine) →
  Hecke.map15 (Quotient.QuotientInterfaceOn.proj quotient)
    (Hecke.PrimeCorrespondenceHeckeOn.correspondence fineHecke prime fine)
  ≡
  Hecke.PrimeCorrespondenceHeckeOn.correspondence
    (inducedHecke descent) prime
    (Quotient.QuotientInterfaceOn.proj quotient fine)
projectedCorrespondenceCommutes
  {quotient = quotient} descent prime fine =
  correspondenceRespectsEquiv descent prime
    (projectionComplete (exactPresentation descent)
      (sym
        (Quotient.QuotientInterfaceOn.section quotient
          (Quotient.QuotientInterfaceOn.proj quotient fine))))

------------------------------------------------------------------------
-- Consequently the actual finite Hecke observable operator commutes with proj.
------------------------------------------------------------------------

projectedObservableHeckeCommutes :
  ∀ {Fine Coarse : Set}
    {quotient : Quotient.QuotientInterfaceOn Fine Coarse}
    {fineHecke : Hecke.PrimeCorrespondenceHeckeOn Fine}
    (descent : QuotientStablePrimeCorrespondence quotient fineHecke)
    (observable : Coarse → Nat)
    (prime : Monster.SSP)
    (fine : Fine) →
  Hecke.PrimeCorrespondenceHeckeOn.operator fineHecke
    (λ state → observable
      (Quotient.QuotientInterfaceOn.proj quotient state))
    prime fine
  ≡
  Hecke.PrimeCorrespondenceHeckeOn.operator (inducedHecke descent)
    observable prime (Quotient.QuotientInterfaceOn.proj quotient fine)
projectedObservableHeckeCommutes
  {quotient = quotient} {fineHecke = fineHecke}
  descent observable prime fine =
  trans
    (cong Hecke.sum15
      (sym
        (map15Fusion observable
          (Quotient.QuotientInterfaceOn.proj quotient)
          (Hecke.PrimeCorrespondenceHeckeOn.correspondence
            fineHecke prime fine))))
    (cong
      (λ values → Hecke.sum15 (Hecke.map15 observable values))
      (projectedCorrespondenceCommutes descent prime fine))

------------------------------------------------------------------------
-- Canonicality: any other coarse correspondence commuting with the same
-- quotient agrees pointwise with the induced correspondence.
------------------------------------------------------------------------

inducedCorrespondenceUnique :
  ∀ {Fine Coarse : Set}
    {quotient : Quotient.QuotientInterfaceOn Fine Coarse}
    {fineHecke : Hecke.PrimeCorrespondenceHeckeOn Fine}
    (descent : QuotientStablePrimeCorrespondence quotient fineHecke)
    (candidate : Hecke.PrimeCorrespondenceHeckeOn Coarse)
    (candidateCommutes :
      (prime : Monster.SSP) →
      (fine : Fine) →
      Hecke.map15 (Quotient.QuotientInterfaceOn.proj quotient)
        (Hecke.PrimeCorrespondenceHeckeOn.correspondence fineHecke prime fine)
      ≡
      Hecke.PrimeCorrespondenceHeckeOn.correspondence candidate prime
        (Quotient.QuotientInterfaceOn.proj quotient fine))
    (prime : Monster.SSP)
    (coarse : Coarse) →
  Hecke.PrimeCorrespondenceHeckeOn.correspondence candidate prime coarse
  ≡
  Hecke.PrimeCorrespondenceHeckeOn.correspondence
    (inducedHecke descent) prime coarse
inducedCorrespondenceUnique
  {quotient = quotient}
  descent candidate candidateCommutes prime coarse =
  trans
    (cong
      (Hecke.PrimeCorrespondenceHeckeOn.correspondence candidate prime)
      (sym (Quotient.QuotientInterfaceOn.section quotient coarse)))
    (sym
      (candidateCommutes prime
        (Quotient.QuotientInterfaceOn.representative quotient coarse)))

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

record HeckeCorrespondenceQuotientBoundary : Set where
  field
    existingQuotientRepresentationAPIReused : Bool
    existingQuotientRepresentationAPIReusedIsTrue :
      existingQuotientRepresentationAPIReused ≡ true

    quotientCorrespondenceConstructedFromCongruence : Bool
    quotientCorrespondenceConstructedFromCongruenceIsTrue :
      quotientCorrespondenceConstructedFromCongruence ≡ true

    observableIntertwinerDerivedRatherThanAssumed : Bool
    observableIntertwinerDerivedRatherThanAssumedIsTrue :
      observableIntertwinerDerivedRatherThanAssumed ≡ true

    inducedCorrespondenceCanonicalForChosenExactQuotient : Bool
    inducedCorrespondenceCanonicalForChosenExactQuotientIsTrue :
      inducedCorrespondenceCanonicalForChosenExactQuotient ≡ true

    currentSO3ReductionIdentifiedWithSupportMaskHecke : Bool
    currentSO3ReductionIdentifiedWithSupportMaskHeckeIsFalse :
      currentSO3ReductionIdentifiedWithSupportMaskHecke ≡ false

canonicalHeckeCorrespondenceQuotientBoundary :
  HeckeCorrespondenceQuotientBoundary
canonicalHeckeCorrespondenceQuotientBoundary =
  record
    { existingQuotientRepresentationAPIReused = true
    ; existingQuotientRepresentationAPIReusedIsTrue = refl
    ; quotientCorrespondenceConstructedFromCongruence = true
    ; quotientCorrespondenceConstructedFromCongruenceIsTrue = refl
    ; observableIntertwinerDerivedRatherThanAssumed = true
    ; observableIntertwinerDerivedRatherThanAssumedIsTrue = refl
    ; inducedCorrespondenceCanonicalForChosenExactQuotient = true
    ; inducedCorrespondenceCanonicalForChosenExactQuotientIsTrue = refl
    ; currentSO3ReductionIdentifiedWithSupportMaskHecke = false
    ; currentSO3ReductionIdentifiedWithSupportMaskHeckeIsFalse = refl
    }
