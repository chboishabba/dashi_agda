module Ontology.DNA.ComplementLaws where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Vec using (Vec; map; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

open import Ontology.DNA.Supervoxel4Adic using
  (Base; A; C; G; T; complement; FlatDNA256)
open import Ontology.DNA.ChemistryQuotient using
  (Strength; weak; strong; PurineClass; pyrimidine; purine;
   strength; purineClass; ChemistryFeature; chemistryFeature)
open import Ontology.DNA.ChemistryConcrete using (featureMapConcrete)

------------------------------------------------------------------------
-- Chemistry-visible laws for Watson-Crick complement.
-- Complement preserves the strong/weak channel and flips the
-- purine/pyrimidine channel, so the chemistry quotient records a
-- structured involution rather than an arbitrary rewrite.

flipPurineClass : PurineClass → PurineClass
flipPurineClass purine = pyrimidine
flipPurineClass pyrimidine = purine

flipPurineClass-involutive : ∀ p → flipPurineClass (flipPurineClass p) ≡ p
flipPurineClass-involutive purine = refl
flipPurineClass-involutive pyrimidine = refl

strength-complement : ∀ b → strength (complement b) ≡ strength b
strength-complement A = refl
strength-complement C = refl
strength-complement G = refl
strength-complement T = refl

purineClass-complement :
  ∀ b → purineClass (complement b) ≡ flipPurineClass (purineClass b)
purineClass-complement A = refl
purineClass-complement C = refl
purineClass-complement G = refl
purineClass-complement T = refl

map-strength-complement :
  ∀ {n} →
  (xs : Vec Base n) →
  map strength (map complement xs) ≡ map strength xs
map-strength-complement [] = refl
map-strength-complement (x ∷ xs)
  rewrite strength-complement x
        | map-strength-complement xs = refl

map-purine-complement :
  ∀ {n} →
  (xs : Vec Base n) →
  map purineClass (map complement xs)
    ≡ map flipPurineClass (map purineClass xs)
map-purine-complement [] = refl
map-purine-complement (x ∷ xs)
  rewrite purineClass-complement x
        | map-purine-complement xs = refl

complementFeature : ChemistryFeature → ChemistryFeature
complementFeature (chemistryFeature u v) =
  chemistryFeature u (map flipPurineClass v)

featureMap-complement :
  (xs : FlatDNA256) →
  featureMapConcrete (map complement xs)
    ≡ complementFeature (featureMapConcrete xs)
featureMap-complement xs =
  cong₂ chemistryFeature
    (map-strength-complement xs)
    (map-purine-complement xs)
