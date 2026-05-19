module Ontology.DNA.ChemistryUVCoordinates where

open import Agda.Builtin.Bool     using (Bool)
open import Agda.Builtin.Nat      using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Vec using (Vec; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

open import Ontology.DNA.Supervoxel4Adic using (Base; A; C; G; T; FlatDNA256)
open import Ontology.DNA.ChemistryQuotient using
  (Strength; weak; strong; PurineClass; pyrimidine; purine;
   strength; purineClass; FeatureU; FeatureV; ChemistryFeature;
   chemistryFeature)

------------------------------------------------------------------------
-- UV-style chemistry coordinates:
-- U records weak/strong and V records pyrimidine/purine.
-- Together they still determine the underlying base exactly.

record UVCoordinates (n : Nat) : Set where
  constructor uvCoordinates
  field
    uCoord : Vec Strength n
    vCoord : Vec PurineClass n

mergeBase : Strength → PurineClass → Base
mergeBase weak   purine     = A
mergeBase weak   pyrimidine = T
mergeBase strong purine     = G
mergeBase strong pyrimidine = C

encodeUV : ∀ {n} → Vec Base n → UVCoordinates n
encodeUV xs = uvCoordinates (map strength xs) (map purineClass xs)

decodeUVVec : ∀ {n} → Vec Strength n → Vec PurineClass n → Vec Base n
decodeUVVec [] [] = []
decodeUVVec (u ∷ us) (v ∷ vs) = mergeBase u v ∷ decodeUVVec us vs

decodeUV : ∀ {n} → UVCoordinates n → Vec Base n
decodeUV (uvCoordinates u v) = decodeUVVec u v

merge-strength : ∀ u v → strength (mergeBase u v) ≡ u
merge-strength weak purine = refl
merge-strength weak pyrimidine = refl
merge-strength strong purine = refl
merge-strength strong pyrimidine = refl

merge-purine : ∀ u v → purineClass (mergeBase u v) ≡ v
merge-purine weak purine = refl
merge-purine weak pyrimidine = refl
merge-purine strong purine = refl
merge-purine strong pyrimidine = refl

merge-roundtrip : ∀ b → mergeBase (strength b) (purineClass b) ≡ b
merge-roundtrip A = refl
merge-roundtrip C = refl
merge-roundtrip G = refl
merge-roundtrip T = refl

decodeU-section :
  ∀ {n} (u : Vec Strength n) (v : Vec PurineClass n) →
  map strength (decodeUVVec u v) ≡ u
decodeU-section [] [] = refl
decodeU-section (u ∷ us) (v ∷ vs)
  rewrite merge-strength u v | decodeU-section us vs = refl

decodeV-section :
  ∀ {n} (u : Vec Strength n) (v : Vec PurineClass n) →
  map purineClass (decodeUVVec u v) ≡ v
decodeV-section [] [] = refl
decodeV-section (u ∷ us) (v ∷ vs)
  rewrite merge-purine u v | decodeV-section us vs = refl

decodeEncode :
  ∀ {n} (xs : Vec Base n) →
  decodeUV (encodeUV xs) ≡ xs
decodeEncode [] = refl
decodeEncode (x ∷ xs)
  rewrite merge-roundtrip x | decodeEncode xs = refl

feature256 : UVCoordinates 256 → ChemistryFeature
feature256 uv =
  chemistryFeature (UVCoordinates.uCoord uv) (UVCoordinates.vCoord uv)

encodeFeature256 : FlatDNA256 → ChemistryFeature
encodeFeature256 xs = feature256 (encodeUV xs)

encodeFeature256-def :
  ∀ xs →
  encodeFeature256 xs ≡ chemistryFeature (map strength xs) (map purineClass xs)
encodeFeature256-def xs = refl

featureSection256 :
  ∀ uv →
  encodeFeature256 (decodeUV uv) ≡ feature256 uv
featureSection256 (uvCoordinates u v) =
  cong₂ chemistryFeature (decodeU-section u v) (decodeV-section u v)

pullbackAdmissible :
  ∀ {n} →
  (Vec Base n → Bool) →
  UVCoordinates n →
  Bool
pullbackAdmissible admissible uv = admissible (decodeUV uv)

pullbackAdmissible-section :
  ∀ {n} (admissible : Vec Base n → Bool) (xs : Vec Base n) →
  pullbackAdmissible admissible (encodeUV xs) ≡ admissible xs
pullbackAdmissible-section admissible xs
  rewrite decodeEncode xs = refl

