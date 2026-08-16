module DASHI.Moonshine.IndexedLevelHeckeQuotientDescentExact where

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
-- Lift the exact correspondence-quotient theorem to the unbiased natural-level
-- scan while allowing *both* sides to depend on level:
--
--   Fine Coarse : Nat -> Set.
--
-- This is the correct theorem shape for the current representation programme:
-- level 2 is spinorial, while every odd level 2*j+1 has its own SO(3) weight
-- carrier and matched D_(2j+1) sector carrier.  For every level, an existing
-- QuotientInterfaceOn plus projection-completeness and correspondence
-- congruence canonically induces the quotient correspondence and proves the
-- observable commuting square.
--
-- No concrete SO(3) Hecke/Brandt correspondence is created here.  The theorem
-- removes only the generic dependent quotient algebra.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Ontology.GodelLattice using (Vec15)
open import Ontology.GodelLattice renaming (v15 to mkVec15)

import Ontology.Hecke.LevelCorrespondenceRepresentation as Level
import Ontology.Hecke.IndexedLevelCorrespondenceRepresentation as Indexed
import Ontology.Hecke.QuotientRepresentation as Quotient
import DASHI.Moonshine.HeckeCorrespondenceQuotientDescentExact as PrimeDescent

------------------------------------------------------------------------
-- Vec15 functoriality for the natural-level API.
------------------------------------------------------------------------

levelMap15Fusion :
  ∀ {A B C : Set}
    (f : B → C)
    (g : A → B)
    (values : Vec15 A) →
  Level.map15 f (Level.map15 g values)
  ≡ Level.map15 (λ value → f (g value)) values
levelMap15Fusion f g
  (mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71) =
  refl

------------------------------------------------------------------------
-- Level-indexed exact quotient family.
------------------------------------------------------------------------

record IndexedQuotientStableCorrespondence
    (Fine Coarse : Nat → Set)
    (fineHecke : Indexed.IndexedLevelCorrespondenceHeckeOn Fine) : Set₁ where
  field
    quotientAt :
      (level : Nat) →
      Quotient.QuotientInterfaceOn (Fine level) (Coarse level)

    exactAt :
      (level : Nat) → PrimeDescent.ExactQuotientPresentation (quotientAt level)

    correspondenceRespectsEquivAt :
      (level : Nat) →
      ∀ {left right : Fine level} →
      Quotient.EquivalenceOn._≈_
        (Quotient.QuotientInterfaceOn.equiv (quotientAt level)) left right →
      Level.map15 (Quotient.QuotientInterfaceOn.proj (quotientAt level))
        (Indexed.correspondence fineHecke level left)
      ≡
      Level.map15 (Quotient.QuotientInterfaceOn.proj (quotientAt level))
        (Indexed.correspondence fineHecke level right)

open IndexedQuotientStableCorrespondence public

inducedIndexedCorrespondence :
  ∀ {Fine Coarse : Nat → Set}
    {fineHecke : Indexed.IndexedLevelCorrespondenceHeckeOn Fine} →
  IndexedQuotientStableCorrespondence Fine Coarse fineHecke →
  (level : Nat) → Coarse level → Vec15 (Coarse level)
inducedIndexedCorrespondence
  {fineHecke = fineHecke} descent level coarse =
  Level.map15 (Quotient.QuotientInterfaceOn.proj (quotientAt descent level))
    (Indexed.correspondence fineHecke level
      (Quotient.QuotientInterfaceOn.representative
        (quotientAt descent level) coarse))

inducedIndexedHecke :
  ∀ {Fine Coarse : Nat → Set}
    {fineHecke : Indexed.IndexedLevelCorrespondenceHeckeOn Fine} →
  IndexedQuotientStableCorrespondence Fine Coarse fineHecke →
  Indexed.IndexedLevelCorrespondenceHeckeOn Coarse
inducedIndexedHecke descent =
  record
    { correspondence = inducedIndexedCorrespondence descent
    }

------------------------------------------------------------------------
-- Levelwise correspondence commutation.
------------------------------------------------------------------------

indexedProjectedCorrespondenceCommutes :
  ∀ {Fine Coarse : Nat → Set}
    {fineHecke : Indexed.IndexedLevelCorrespondenceHeckeOn Fine}
    (descent : IndexedQuotientStableCorrespondence Fine Coarse fineHecke)
    (level : Nat)
    (fine : Fine level) →
  Level.map15 (Quotient.QuotientInterfaceOn.proj (quotientAt descent level))
    (Indexed.correspondence fineHecke level fine)
  ≡
  Indexed.correspondence (inducedIndexedHecke descent) level
    (Quotient.QuotientInterfaceOn.proj (quotientAt descent level) fine)
indexedProjectedCorrespondenceCommutes descent level fine =
  correspondenceRespectsEquivAt descent level
    (PrimeDescent.projectionComplete (exactAt descent level)
      (sym
        (Quotient.QuotientInterfaceOn.section
          (quotientAt descent level)
          (Quotient.QuotientInterfaceOn.proj
            (quotientAt descent level) fine))))

------------------------------------------------------------------------
-- Levelwise observable Hecke commutation.
------------------------------------------------------------------------

indexedProjectedObservableHeckeCommutes :
  ∀ {Fine Coarse : Nat → Set}
    {fineHecke : Indexed.IndexedLevelCorrespondenceHeckeOn Fine}
    (descent : IndexedQuotientStableCorrespondence Fine Coarse fineHecke)
    (level : Nat)
    (observable : Coarse level → Nat)
    (fine : Fine level) →
  Indexed.operator fineHecke level
    (λ state → observable
      (Quotient.QuotientInterfaceOn.proj (quotientAt descent level) state))
    fine
  ≡
  Indexed.operator (inducedIndexedHecke descent)
    level observable
    (Quotient.QuotientInterfaceOn.proj (quotientAt descent level) fine)
indexedProjectedObservableHeckeCommutes
  {fineHecke = fineHecke} descent level observable fine =
  trans
    (cong Level.sum15
      (sym
        (levelMap15Fusion observable
          (Quotient.QuotientInterfaceOn.proj (quotientAt descent level))
          (Indexed.correspondence fineHecke level fine))))
    (cong
      (λ values → Level.sum15 (Level.map15 observable values))
      (indexedProjectedCorrespondenceCommutes descent level fine))

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

record IndexedLevelHeckeQuotientBoundary : Set where
  field
    levelDependentFineCarrierRepresentable : Bool
    levelDependentFineCarrierRepresentableIsTrue :
      levelDependentFineCarrierRepresentable ≡ true

    levelDependentClassCarrierConstructed : Bool
    levelDependentClassCarrierConstructedIsTrue :
      levelDependentClassCarrierConstructed ≡ true

    levelwiseQuotientIntertwiningDerived : Bool
    levelwiseQuotientIntertwiningDerivedIsTrue :
      levelwiseQuotientIntertwiningDerived ≡ true

    nonOggNaturalLevelsRepresentable : Bool
    nonOggNaturalLevelsRepresentableIsTrue :
      nonOggNaturalLevelsRepresentable ≡ true

    matchedDihedralStateCorrespondenceConstructedHere : Bool
    matchedDihedralStateCorrespondenceConstructedHereIsFalse :
      matchedDihedralStateCorrespondenceConstructedHere ≡ false

    geometricBrandtCorrespondenceConstructedHere : Bool
    geometricBrandtCorrespondenceConstructedHereIsFalse :
      geometricBrandtCorrespondenceConstructedHere ≡ false

canonicalIndexedLevelHeckeQuotientBoundary :
  IndexedLevelHeckeQuotientBoundary
canonicalIndexedLevelHeckeQuotientBoundary =
  record
    { levelDependentFineCarrierRepresentable = true
    ; levelDependentFineCarrierRepresentableIsTrue = refl
    ; levelDependentClassCarrierConstructed = true
    ; levelDependentClassCarrierConstructedIsTrue = refl
    ; levelwiseQuotientIntertwiningDerived = true
    ; levelwiseQuotientIntertwiningDerivedIsTrue = refl
    ; nonOggNaturalLevelsRepresentable = true
    ; nonOggNaturalLevelsRepresentableIsTrue = refl
    ; matchedDihedralStateCorrespondenceConstructedHere = false
    ; matchedDihedralStateCorrespondenceConstructedHereIsFalse = refl
    ; geometricBrandtCorrespondenceConstructedHere = false
    ; geometricBrandtCorrespondenceConstructedHereIsFalse = refl
    }
