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
-- Give the exact quotient-natural form of the currently open representation /
-- Hecke intertwiner problem on the repository's *actual* finite
-- PrimeCorrespondenceHeckeOn carrier.
--
-- If a projection q : Fine -> Coarse has a section and the projected 15-way
-- correspondence list is constant on q-fibres, then the fine correspondence
-- canonically descends to Coarse.  The resulting finite Hecke operator obeys
--
--   T_fine (f o q) = T_quotient f o q
--
-- exactly, for every Nat-valued coarse observable f.
--
-- Thus a future representation/Hecke proof need not guess an arbitrary Phi
-- and then independently prove Phi R_p = T_p Phi.  Once Phi is a sectioned
-- quotient with correspondence-congruence, the commuting square is derived;
-- the remaining domain-specific obligation is to identify the induced
-- quotient correspondence/operator with the intended arithmetic Hecke one.
--
-- No claim is made here that the current SSP support-mask correspondence is a
-- quotient of the SO(3)/dihedral reduction carrier.  That is the next concrete
-- producer obligation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Ontology.GodelLattice using (Vec15)
open import Ontology.GodelLattice renaming (v15 to mkVec15)

import MonsterOntos as Monster
import Ontology.Hecke.CorrespondenceRepresentation as Hecke

------------------------------------------------------------------------
-- A projection with a chosen representative for every coarse code.
------------------------------------------------------------------------

record SectionedProjection
    {Fine Coarse : Set}
    (project : Fine → Coarse) : Set where
  field
    section : Coarse → Fine
    sectionRightInverse :
      (coarse : Coarse) → project (section coarse) ≡ coarse

open SectionedProjection public

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
-- The exact well-definedness condition for quotienting a correspondence.
------------------------------------------------------------------------

record QuotientStablePrimeCorrespondence
    {Fine Coarse : Set}
    (project : Fine → Coarse)
    (fineHecke : Hecke.PrimeCorrespondenceHeckeOn Fine) : Set₁ where
  field
    sectioned : SectionedProjection project

    correspondenceCongruent :
      (prime : Monster.SSP) →
      (left right : Fine) →
      project left ≡ project right →
      Hecke.map15 project
        (Hecke.PrimeCorrespondenceHeckeOn.correspondence fineHecke prime left)
      ≡
      Hecke.map15 project
        (Hecke.PrimeCorrespondenceHeckeOn.correspondence fineHecke prime right)

open QuotientStablePrimeCorrespondence public

inducedCorrespondence :
  ∀ {Fine Coarse : Set}
    {project : Fine → Coarse}
    {fineHecke : Hecke.PrimeCorrespondenceHeckeOn Fine} →
  QuotientStablePrimeCorrespondence project fineHecke →
  Monster.SSP → Coarse → Vec15 Coarse
inducedCorrespondence descent prime coarse =
  Hecke.map15 _
    (Hecke.PrimeCorrespondenceHeckeOn.correspondence _ prime
      (section (sectioned descent) coarse))

inducedHecke :
  ∀ {Fine Coarse : Set}
    {project : Fine → Coarse}
    {fineHecke : Hecke.PrimeCorrespondenceHeckeOn Fine} →
  QuotientStablePrimeCorrespondence project fineHecke →
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
    {project : Fine → Coarse}
    {fineHecke : Hecke.PrimeCorrespondenceHeckeOn Fine}
    (descent : QuotientStablePrimeCorrespondence project fineHecke)
    (prime : Monster.SSP)
    (fine : Fine) →
  Hecke.map15 project
    (Hecke.PrimeCorrespondenceHeckeOn.correspondence fineHecke prime fine)
  ≡
  Hecke.PrimeCorrespondenceHeckeOn.correspondence
    (inducedHecke descent) prime (project fine)
projectedCorrespondenceCommutes
  {project = project} descent prime fine =
  correspondenceCongruent descent prime fine
    (section (sectioned descent) (project fine))
    (sym (sectionRightInverse (sectioned descent) (project fine)))

------------------------------------------------------------------------
-- Consequently the actual finite Hecke observable operator commutes with q.
------------------------------------------------------------------------

projectedObservableHeckeCommutes :
  ∀ {Fine Coarse : Set}
    {project : Fine → Coarse}
    {fineHecke : Hecke.PrimeCorrespondenceHeckeOn Fine}
    (descent : QuotientStablePrimeCorrespondence project fineHecke)
    (observable : Coarse → Nat)
    (prime : Monster.SSP)
    (fine : Fine) →
  Hecke.PrimeCorrespondenceHeckeOn.operator fineHecke
    (λ state → observable (project state)) prime fine
  ≡
  Hecke.PrimeCorrespondenceHeckeOn.operator (inducedHecke descent)
    observable prime (project fine)
projectedObservableHeckeCommutes
  {project = project} {fineHecke = fineHecke}
  descent observable prime fine =
  trans
    (cong Hecke.sum15
      (sym
        (map15Fusion observable project
          (Hecke.PrimeCorrespondenceHeckeOn.correspondence
            fineHecke prime fine))))
    (cong
      (λ values → Hecke.sum15 (Hecke.map15 observable values))
      (projectedCorrespondenceCommutes descent prime fine))

------------------------------------------------------------------------
-- Canonicality: any other coarse correspondence commuting with the same
-- sectioned projection agrees pointwise with the induced one.
------------------------------------------------------------------------

inducedCorrespondenceUnique :
  ∀ {Fine Coarse : Set}
    {project : Fine → Coarse}
    {fineHecke : Hecke.PrimeCorrespondenceHeckeOn Fine}
    (descent : QuotientStablePrimeCorrespondence project fineHecke)
    (candidate : Hecke.PrimeCorrespondenceHeckeOn Coarse)
    (candidateCommutes :
      (prime : Monster.SSP) →
      (fine : Fine) →
      Hecke.map15 project
        (Hecke.PrimeCorrespondenceHeckeOn.correspondence fineHecke prime fine)
      ≡
      Hecke.PrimeCorrespondenceHeckeOn.correspondence
        candidate prime (project fine))
    (prime : Monster.SSP)
    (coarse : Coarse) →
  Hecke.PrimeCorrespondenceHeckeOn.correspondence candidate prime coarse
  ≡
  Hecke.PrimeCorrespondenceHeckeOn.correspondence
    (inducedHecke descent) prime coarse
inducedCorrespondenceUnique
  {project = project} descent candidate candidateCommutes prime coarse =
  trans
    (cong
      (Hecke.PrimeCorrespondenceHeckeOn.correspondence candidate prime)
      (sym (sectionRightInverse (sectioned descent) coarse)))
    (sym
      (candidateCommutes prime (section (sectioned descent) coarse)))

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

record HeckeCorrespondenceQuotientBoundary : Set where
  field
    quotientCorrespondenceConstructedFromCongruence : Bool
    quotientCorrespondenceConstructedFromCongruenceIsTrue :
      quotientCorrespondenceConstructedFromCongruence ≡ true

    observableIntertwinerDerivedRatherThanAssumed : Bool
    observableIntertwinerDerivedRatherThanAssumedIsTrue :
      observableIntertwinerDerivedRatherThanAssumed ≡ true

    inducedCorrespondenceCanonicalForChosenSectionedProjection : Bool
    inducedCorrespondenceCanonicalForChosenSectionedProjectionIsTrue :
      inducedCorrespondenceCanonicalForChosenSectionedProjection ≡ true

    currentSO3ReductionIdentifiedWithSupportMaskHecke : Bool
    currentSO3ReductionIdentifiedWithSupportMaskHeckeIsFalse :
      currentSO3ReductionIdentifiedWithSupportMaskHecke ≡ false

canonicalHeckeCorrespondenceQuotientBoundary :
  HeckeCorrespondenceQuotientBoundary
canonicalHeckeCorrespondenceQuotientBoundary =
  record
    { quotientCorrespondenceConstructedFromCongruence = true
    ; quotientCorrespondenceConstructedFromCongruenceIsTrue = refl
    ; observableIntertwinerDerivedRatherThanAssumed = true
    ; observableIntertwinerDerivedRatherThanAssumedIsTrue = refl
    ; inducedCorrespondenceCanonicalForChosenSectionedProjection = true
    ; inducedCorrespondenceCanonicalForChosenSectionedProjectionIsTrue = refl
    ; currentSO3ReductionIdentifiedWithSupportMaskHecke = false
    ; currentSO3ReductionIdentifiedWithSupportMaskHeckeIsFalse = refl
    }
