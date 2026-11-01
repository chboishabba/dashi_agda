module DASHI.Biology.DNAChemistryFeatureQuotient where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Biology.DNAChemistryCarrier as DNA

record ChemistryFeatures : Set where
  constructor features
  field
    gcCount : Nat
    maxRun : Nat
    forbiddenMotifCount : Nat
    nearestNeighbourScore : Nat
    hairpinScore : Nat
    dimerScore : Nat
open ChemistryFeatures public

FeatureMap : Set
FeatureMap = List DNA.DNABase → ChemistryFeatures

record FeatureFibreQuotient (Φ : FeatureMap) (x y : List DNA.DNABase) : Set where
  constructor sameFeatureFibre
  field
    featureEquality : Φ x ≡ Φ y
open FeatureFibreQuotient public

feature-refl : ∀ Φ x → FeatureFibreQuotient Φ x x
feature-refl Φ x = sameFeatureFibre refl

feature-sym : ∀ {Φ x y} → FeatureFibreQuotient Φ x y → FeatureFibreQuotient Φ y x
feature-sym (sameFeatureFibre p) = sameFeatureFibre (sym p)

feature-trans :
  ∀ {Φ x y z} →
  FeatureFibreQuotient Φ x y →
  FeatureFibreQuotient Φ y z →
  FeatureFibreQuotient Φ x z
feature-trans (sameFeatureFibre p) (sameFeatureFibre q) = sameFeatureFibre (trans p q)

data ChemistryBasin : Set where
  admissibleBasin : ChemistryBasin
  warningBasin : ChemistryBasin
  rejectedBasin : ChemistryBasin

BasinMap : Set
BasinMap = ChemistryFeatures → ChemistryBasin

record BasinQuotient (Φ : FeatureMap) (basin : BasinMap)
  (x y : List DNA.DNABase) : Set where
  constructor sameBasin
  field
    basinEquality : basin (Φ x) ≡ basin (Φ y)
open BasinQuotient public

basin-refl : ∀ Φ basin x → BasinQuotient Φ basin x x
basin-refl Φ basin x = sameBasin refl

basin-sym : ∀ {Φ basin x y} → BasinQuotient Φ basin x y → BasinQuotient Φ basin y x
basin-sym (sameBasin p) = sameBasin (sym p)

basin-trans :
  ∀ {Φ basin x y z} →
  BasinQuotient Φ basin x y →
  BasinQuotient Φ basin y z →
  BasinQuotient Φ basin x z
basin-trans (sameBasin p) (sameBasin q) = sameBasin (trans p q)

-- No epsilon-distance relation is promoted here: without additional hypotheses,
-- threshold proximity need not be transitive and therefore need not be a quotient.
record ChemistryQuotientBoundary : Set₁ where
  constructor quotientBoundary
  field
    featureCarrier : Set
    exactFeatureEqualityDefinesEquivalence : Set
    basinEqualityDefinesEquivalence : Set
    toleranceRelationPromotedWithoutTransitivity : Set
open ChemistryQuotientBoundary public

canonicalChemistryQuotientBoundary : ChemistryQuotientBoundary
canonicalChemistryQuotientBoundary =
  quotientBoundary
    ChemistryFeatures
    (∀ (Φ : FeatureMap) x → FeatureFibreQuotient Φ x x)
    (∀ (Φ : FeatureMap) (b : BasinMap) x → BasinQuotient Φ b x x)
    (∀ {A : Set} → A → A)
