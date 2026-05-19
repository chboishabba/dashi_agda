module Ontology.DNA.ChemistryUVConcrete where

open import Agda.Builtin.Bool     using (Bool; true; false)
open import Agda.Builtin.Nat      using (Nat; zero; suc; _+_)
open import Data.Vec using (Vec; []; _∷_)

open import Ontology.DNA.Supervoxel4Adic using (Base; FlatDNA256)
open import Ontology.DNA.ChemistryQuotient using
  (pyrimidine; purineClass; ChemistryFeature; ChemistryQuotient;
   ChemistryQuotientInterface)
open import Ontology.DNA.ChemistryConcrete using
  (_&&_; featureMapConcrete; thermoKernelConcrete; admissibleConcrete;
   representativeUV; sectionUV)

------------------------------------------------------------------------
-- UV-aware refinement of the first concrete chemistry quotient.
-- Adjacent pyrimidines are a local UV-sensitive dimer surface, while
-- longer pyrimidine runs are screened as an additional admissibility law.

isPyrimidine : Base → Bool
isPyrimidine b with purineClass b
... | pyrimidine = true
... | _          = false

uvDimer2 : Base → Base → Bool
uvDimer2 x y = isPyrimidine x && isPyrimidine y

countUVDimer2From : ∀ {n} → Base → Vec Base n → Nat
countUVDimer2From x [] = zero
countUVDimer2From x (y ∷ ys) with uvDimer2 x y
... | true  = suc (countUVDimer2From y ys)
... | false = countUVDimer2From y ys

countUVDimer2 : ∀ {n} → Vec Base n → Nat
countUVDimer2 [] = zero
countUVDimer2 (x ∷ xs) = countUVDimer2From x xs

allPyrimidine3 : Base → Base → Base → Bool
allPyrimidine3 a b c = isPyrimidine a && (isPyrimidine b && isPyrimidine c)

countPyrimidineTriple3From : ∀ {n} → Base → Base → Vec Base n → Nat
countPyrimidineTriple3From a b [] = zero
countPyrimidineTriple3From a b (c ∷ cs) with allPyrimidine3 a b c
... | true  = suc (countPyrimidineTriple3From b c cs)
... | false = countPyrimidineTriple3From b c cs

countPyrimidineTriple3 : ∀ {n} → Vec Base n → Nat
countPyrimidineTriple3 [] = zero
countPyrimidineTriple3 (_ ∷ []) = zero
countPyrimidineTriple3 (a ∷ b ∷ cs) = countPyrimidineTriple3From a b cs

noPyrimidineTriple3From : ∀ {n} → Base → Base → Vec Base n → Bool
noPyrimidineTriple3From a b [] = true
noPyrimidineTriple3From a b (c ∷ cs) with allPyrimidine3 a b c
... | true  = false
... | false = noPyrimidineTriple3From b c cs

noPyrimidineTriple3 : ∀ {n} → Vec Base n → Bool
noPyrimidineTriple3 [] = true
noPyrimidineTriple3 (_ ∷ []) = true
noPyrimidineTriple3 (a ∷ b ∷ cs) = noPyrimidineTriple3From a b cs

uvKernelConcrete : FlatDNA256 → Nat
uvKernelConcrete xs = countUVDimer2 xs + countPyrimidineTriple3 xs

thermoKernelUVConcrete : FlatDNA256 → Nat
thermoKernelUVConcrete xs = thermoKernelConcrete xs + uvKernelConcrete xs

admissibleUVConcrete : FlatDNA256 → Bool
admissibleUVConcrete xs = admissibleConcrete xs && noPyrimidineTriple3 xs

chemistryQuotientUVConcrete : ChemistryQuotient
chemistryQuotientUVConcrete = record
  { featureMap   = featureMapConcrete
  ; thermoKernel = thermoKernelUVConcrete
  ; admissible   = admissibleUVConcrete
  }

chemistryQuotientInterfaceUVConcrete : ChemistryQuotientInterface
chemistryQuotientInterfaceUVConcrete = record
  { quotient       = chemistryQuotientUVConcrete
  ; representative =
      λ f → representativeUV (ChemistryFeature.u f) (ChemistryFeature.v f)
  ; section        = λ f → sectionUV (ChemistryFeature.u f) (ChemistryFeature.v f)
  }
