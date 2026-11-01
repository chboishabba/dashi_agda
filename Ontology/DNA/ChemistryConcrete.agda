module Ontology.DNA.ChemistryConcrete where

open import Agda.Builtin.Bool     using (Bool; true; false)
open import Agda.Builtin.Nat      using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Vec using (Vec; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

open import Ontology.DNA.Supervoxel4Adic using
  (Base; A; C; G; T; complement; FlatDNA256)
open import Ontology.DNA.ChemistryQuotient using
  (Strength; weak; strong; PurineClass; pyrimidine; purine;
   strength; purineClass; FeatureU; FeatureV; ChemistryFeature;
   chemistryFeature; ChemistryQuotient; ChemistryQuotientInterface)

------------------------------------------------------------------------
-- First concrete chemistry quotient on DNA256.

_&&_ : Bool → Bool → Bool
true  && b = b
false && b = false

not : Bool → Bool
not true  = false
not false = true

baseEq : Base → Base → Bool
baseEq A A = true
baseEq C C = true
baseEq G G = true
baseEq T T = true
baseEq _ _ = false

isStrong : Base → Bool
isStrong b with strength b
... | weak   = false
... | strong = true

countStrong : ∀ {n} → Vec Base n → Nat
countStrong [] = zero
countStrong (b ∷ bs) with strength b
... | weak   = countStrong bs
... | strong = suc (countStrong bs)

countComplementSpan2From : ∀ {n} → Base → Base → Vec Base n → Nat
countComplementSpan2From x y [] = zero
countComplementSpan2From x y (z ∷ xs) with baseEq (complement x) z
... | true  = suc (countComplementSpan2From y z xs)
... | false = countComplementSpan2From y z xs

countComplementSpan2 : ∀ {n} → Vec Base n → Nat
countComplementSpan2 [] = zero
countComplementSpan2 (_ ∷ []) = zero
countComplementSpan2 (x ∷ y ∷ xs) = countComplementSpan2From x y xs

noImmediateRepeat : ∀ {n} → Vec Base n → Bool
noImmediateRepeat [] = true
noImmediateRepeat (_ ∷ []) = true
noImmediateRepeat (x ∷ y ∷ xs) = pairOK && noImmediateRepeat (y ∷ xs)
  where
  pairOK : Bool
  pairOK with baseEq x y
  ... | true  = false
  ... | false = true

noImmediateComplement : ∀ {n} → Vec Base n → Bool
noImmediateComplement [] = true
noImmediateComplement (_ ∷ []) = true
noImmediateComplement (x ∷ y ∷ xs) = pairOK && noImmediateComplement (y ∷ xs)
  where
  pairOK : Bool
  pairOK with baseEq (complement x) y
  ... | true  = false
  ... | false = true

noComplementSpan2From : ∀ {n} → Base → Base → Vec Base n → Bool
noComplementSpan2From x y [] = true
noComplementSpan2From x y (z ∷ xs) with baseEq (complement x) z
... | true  = false
... | false = noComplementSpan2From y z xs

noComplementSpan2 : ∀ {n} → Vec Base n → Bool
noComplementSpan2 [] = true
noComplementSpan2 (_ ∷ []) = true
noComplementSpan2 (x ∷ y ∷ xs) = noComplementSpan2From x y xs

allStrong4 : Base → Base → Base → Base → Bool
allStrong4 a b c d = isStrong a && (isStrong b && (isStrong c && isStrong d))

allWeak4 : Base → Base → Base → Base → Bool
allWeak4 a b c d =
  not (isStrong a) && (not (isStrong b) && (not (isStrong c) && not (isStrong d)))

noExtremeGC4From : ∀ {n} → Base → Base → Base → Vec Base n → Bool
noExtremeGC4From a b c [] = true
noExtremeGC4From a b c (d ∷ ds) = windowOK && noExtremeGC4From b c d ds
  where
  windowOK : Bool
  windowOK = not (allStrong4 a b c d) && not (allWeak4 a b c d)

noExtremeGC4 : ∀ {n} → Vec Base n → Bool
noExtremeGC4 [] = true
noExtremeGC4 (_ ∷ []) = true
noExtremeGC4 (_ ∷ _ ∷ []) = true
noExtremeGC4 (_ ∷ _ ∷ _ ∷ []) = true
noExtremeGC4 (a ∷ b ∷ c ∷ ds) = noExtremeGC4From a b c ds

rcPalindrome4 : Base → Base → Base → Base → Bool
rcPalindrome4 a b c d =
  baseEq (complement a) d && baseEq (complement b) c

countRCPal4From : ∀ {n} → Base → Base → Base → Vec Base n → Nat
countRCPal4From a b c [] = zero
countRCPal4From a b c (d ∷ ds) with rcPalindrome4 a b c d
... | true  = suc (countRCPal4From b c d ds)
... | false = countRCPal4From b c d ds

countRCPal4 : ∀ {n} → Vec Base n → Nat
countRCPal4 [] = zero
countRCPal4 (_ ∷ []) = zero
countRCPal4 (_ ∷ _ ∷ []) = zero
countRCPal4 (a ∷ b ∷ c ∷ ds) = countRCPal4From a b c ds

noRCPal4From : ∀ {n} → Base → Base → Base → Vec Base n → Bool
noRCPal4From a b c [] = true
noRCPal4From a b c (d ∷ ds) with rcPalindrome4 a b c d
... | true  = false
... | false = noRCPal4From b c d ds

noRCPal4 : ∀ {n} → Vec Base n → Bool
noRCPal4 [] = true
noRCPal4 (_ ∷ []) = true
noRCPal4 (_ ∷ _ ∷ []) = true
noRCPal4 (a ∷ b ∷ c ∷ ds) = noRCPal4From a b c ds

hairpin6 : Base → Base → Base → Base → Base → Base → Bool
hairpin6 a b c d e f =
  baseEq (complement a) f
    && (baseEq (complement b) e && baseEq (complement c) d)

countHairpin6From : ∀ {n} → Base → Base → Base → Base → Base → Vec Base n → Nat
countHairpin6From a b c d e [] = zero
countHairpin6From a b c d e (f ∷ xs) with hairpin6 a b c d e f
... | true  = suc (countHairpin6From b c d e f xs)
... | false = countHairpin6From b c d e f xs

countHairpin6 : ∀ {n} → Vec Base n → Nat
countHairpin6 [] = zero
countHairpin6 (_ ∷ []) = zero
countHairpin6 (_ ∷ _ ∷ []) = zero
countHairpin6 (_ ∷ _ ∷ _ ∷ []) = zero
countHairpin6 (_ ∷ _ ∷ _ ∷ _ ∷ []) = zero
countHairpin6 (a ∷ b ∷ c ∷ d ∷ e ∷ xs) = countHairpin6From a b c d e xs

noHairpin6From : ∀ {n} → Base → Base → Base → Base → Base → Vec Base n → Bool
noHairpin6From a b c d e [] = true
noHairpin6From a b c d e (f ∷ xs) with hairpin6 a b c d e f
... | true  = false
... | false = noHairpin6From b c d e f xs

noHairpin6 : ∀ {n} → Vec Base n → Bool
noHairpin6 [] = true
noHairpin6 (_ ∷ []) = true
noHairpin6 (_ ∷ _ ∷ []) = true
noHairpin6 (_ ∷ _ ∷ _ ∷ []) = true
noHairpin6 (_ ∷ _ ∷ _ ∷ _ ∷ []) = true
noHairpin6 (a ∷ b ∷ c ∷ d ∷ e ∷ xs) = noHairpin6From a b c d e xs

isGC : Base → Bool
isGC C = true
isGC G = true
isGC _ = false

countGCWindow : Base → Base → Base → Nat
countGCWindow a b c =
  countGC a + countGC b + countGC c
  where
  countGC : Base → Nat
  countGC x with isGC x
  ... | true  = suc zero
  ... | false = zero

countGC3From : ∀ {n} → Base → Base → Base → Vec Base n → Nat
countGC3From a b c [] = countWindow
  where
  countWindow : Nat
  countWindow = countGCWindow a b c
countGC3From a b c (d ∷ ds) =
  countWindow + countGC3From b c d ds
  where
  countWindow : Nat
  countWindow = countGCWindow a b c

gcStress3 : ∀ {n} → Vec Base n → Bool
gcStress3 [] = true
gcStress3 (_ ∷ []) = true
gcStress3 (_ ∷ _ ∷ []) = true
gcStress3 (a ∷ b ∷ c ∷ ds) = windowOK && gcStress3 (b ∷ c ∷ ds)
  where
  windowOK : Bool
  windowOK with countGCWindow a b c
  ... | zero = true
  ... | suc zero = true
  ... | suc (suc zero) = true
  ... | suc (suc (suc zero)) = false
  ... | _ = false

featureMapConcrete : FlatDNA256 → ChemistryFeature
featureMapConcrete xs = chemistryFeature (map strength xs) (map purineClass xs)

thermoKernelConcrete : FlatDNA256 → Nat
thermoKernelConcrete xs =
  countStrong xs + countComplementSpan2 xs + countRCPal4 xs + countHairpin6 xs

admissibleConcrete : FlatDNA256 → Bool
admissibleConcrete xs =
  ((noImmediateRepeat xs && noImmediateComplement xs) && noComplementSpan2 xs)
    && ((noExtremeGC4 xs && noRCPal4 xs) && (noHairpin6 xs && gcStress3 xs))

mergeBase : Strength → PurineClass → Base
mergeBase weak   purine     = A
mergeBase weak   pyrimidine = T
mergeBase strong purine     = G
mergeBase strong pyrimidine = C

representativeUV : ∀ {n} → Vec Strength n → Vec PurineClass n → Vec Base n
representativeUV [] [] = []
representativeUV (u ∷ us) (v ∷ vs) = mergeBase u v ∷ representativeUV us vs

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

sectionU :
  ∀ {n} (u : Vec Strength n) (v : Vec PurineClass n) →
  map strength (representativeUV u v) ≡ u
sectionU [] [] = refl
sectionU (u ∷ us) (v ∷ vs) rewrite merge-strength u v | sectionU us vs = refl

sectionV :
  ∀ {n} (u : Vec Strength n) (v : Vec PurineClass n) →
  map purineClass (representativeUV u v) ≡ v
sectionV [] [] = refl
sectionV (u ∷ us) (v ∷ vs) rewrite merge-purine u v | sectionV us vs = refl

sectionUV :
  (u : FeatureU) (v : FeatureV) →
  featureMapConcrete (representativeUV u v) ≡ chemistryFeature u v
sectionUV u v = cong₂ chemistryFeature (sectionU u v) (sectionV u v)

chemistryQuotientConcrete : ChemistryQuotient
chemistryQuotientConcrete = record
  { featureMap    = featureMapConcrete
  ; thermoKernel  = thermoKernelConcrete
  ; admissible    = admissibleConcrete
  }

chemistryQuotientInterfaceConcrete : ChemistryQuotientInterface
chemistryQuotientInterfaceConcrete = record
  { quotient       = chemistryQuotientConcrete
  ; representative = λ f → representativeUV (ChemistryFeature.u f) (ChemistryFeature.v f)
  ; section        = λ f → sectionUV (ChemistryFeature.u f) (ChemistryFeature.v f)
  }
