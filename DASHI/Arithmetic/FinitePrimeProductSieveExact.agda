module DASHI.Arithmetic.FinitePrimeProductSieveExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- G. H. Hardy and E. M. Wright, revised by D. R. Heath-Brown and J. H.
-- Silverman,
-- "An Introduction to the Theory of Numbers", sixth edition,
-- Oxford University Press, 2008.
-- DOI: 10.1093/oso/9780199219858.001.0001.
--
-- DASHI CONTRIBUTION
--
-- Exact product-coordinate theorem behind a finite-prime sieve.  Each entry c
-- represents a local modulus p=c+1 with c nonzero residues.  For a finite list
-- the total and survivor carriers have exact sizes
--
--   product p       and       product (p-1),
--
-- witnessed by recursive two-sided Fin codecs.  Survivor coordinates embed
-- into total coordinates by shifting every local residue away from zero.
--
-- This is deliberately not mislabeled as arithmetic CRT: a canonical
-- residue-mod-product identification still needs a coherent CRT inverse.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _∸_)
open import Data.Fin.Base as Fin using (Fin)
open import Data.Fin.Properties using (remQuot-combine; combine-remQuot)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong)

localModulus : Nat → Nat
localModulus c = suc c

totalProduct : List Nat → Nat
totalProduct [] = 1
totalProduct (c ∷ rest) = localModulus c * totalProduct rest

survivorProduct : List Nat → Nat
survivorProduct [] = 1
survivorProduct (c ∷ rest) = c * survivorProduct rest

excludedCount : List Nat → Nat
excludedCount factors = totalProduct factors ∸ survivorProduct factors

data ResidueCoordinates : List Nat → Set where
  resNil : ResidueCoordinates []
  _∷ʳ_ : ∀ {c rest} →
    Fin (localModulus c) → ResidueCoordinates rest →
    ResidueCoordinates (c ∷ rest)

infixr 5 _∷ʳ_

data SurvivorCoordinates : List Nat → Set where
  survNil : SurvivorCoordinates []
  _∷ˢ_ : ∀ {c rest} →
    Fin c → SurvivorCoordinates rest →
    SurvivorCoordinates (c ∷ rest)

infixr 5 _∷ˢ_

encodeResidues : ∀ {factors} →
  ResidueCoordinates factors → Fin (totalProduct factors)
encodeResidues {[]} resNil = Fin.zero
encodeResidues {c ∷ rest} (head ∷ʳ tail) =
  Fin.combine head (encodeResidues tail)

decodeResidues : ∀ {factors} →
  Fin (totalProduct factors) → ResidueCoordinates factors
decodeResidues {[]} Fin.zero = resNil
decodeResidues {c ∷ rest} code =
  proj₁ split ∷ʳ decodeResidues (proj₂ split)
  where
  split = Fin.remQuot {m = localModulus c} (totalProduct rest) code

residueDecodeEncode : ∀ {factors} →
  (coordinates : ResidueCoordinates factors) →
  decodeResidues (encodeResidues coordinates) ≡ coordinates
residueDecodeEncode {[]} resNil = refl
residueDecodeEncode {c ∷ rest} (head ∷ʳ tail)
  rewrite
    cong proj₁
      (remQuot-combine {n = localModulus c} {k = totalProduct rest}
        head (encodeResidues tail))
  | cong proj₂
      (remQuot-combine {n = localModulus c} {k = totalProduct rest}
        head (encodeResidues tail))
  | residueDecodeEncode tail = refl

residueEncodeDecode : ∀ {factors} →
  (code : Fin (totalProduct factors)) →
  encodeResidues (decodeResidues code) ≡ code
residueEncodeDecode {[]} Fin.zero = refl
residueEncodeDecode {c ∷ rest} code
  rewrite residueEncodeDecode
    (proj₂ (Fin.remQuot {m = localModulus c} (totalProduct rest) code)) =
  combine-remQuot {n = localModulus c} (totalProduct rest) code

encodeSurvivors : ∀ {factors} →
  SurvivorCoordinates factors → Fin (survivorProduct factors)
encodeSurvivors {[]} survNil = Fin.zero
encodeSurvivors {c ∷ rest} (head ∷ˢ tail) =
  Fin.combine head (encodeSurvivors tail)

decodeSurvivors : ∀ {factors} →
  Fin (survivorProduct factors) → SurvivorCoordinates factors
decodeSurvivors {[]} Fin.zero = survNil
decodeSurvivors {c ∷ rest} code =
  proj₁ split ∷ˢ decodeSurvivors (proj₂ split)
  where
  split = Fin.remQuot {m = c} (survivorProduct rest) code

survivorDecodeEncode : ∀ {factors} →
  (coordinates : SurvivorCoordinates factors) →
  decodeSurvivors (encodeSurvivors coordinates) ≡ coordinates
survivorDecodeEncode {[]} survNil = refl
survivorDecodeEncode {c ∷ rest} (head ∷ˢ tail)
  rewrite
    cong proj₁
      (remQuot-combine {n = c} {k = survivorProduct rest}
        head (encodeSurvivors tail))
  | cong proj₂
      (remQuot-combine {n = c} {k = survivorProduct rest}
        head (encodeSurvivors tail))
  | survivorDecodeEncode tail = refl

survivorEncodeDecode : ∀ {factors} →
  (code : Fin (survivorProduct factors)) →
  encodeSurvivors (decodeSurvivors code) ≡ code
survivorEncodeDecode {[]} Fin.zero = refl
survivorEncodeDecode {c ∷ rest} code
  rewrite survivorEncodeDecode
    (proj₂ (Fin.remQuot {m = c} (survivorProduct rest) code)) =
  combine-remQuot {n = c} (survivorProduct rest) code

embedSurvivors : ∀ {factors} →
  SurvivorCoordinates factors → ResidueCoordinates factors
embedSurvivors {[]} survNil = resNil
embedSurvivors {c ∷ rest} (head ∷ˢ tail) =
  Fin.suc head ∷ʳ embedSurvivors tail

twoThreeFactors : List Nat
twoThreeFactors = 1 ∷ 2 ∷ []

twoThreeTotalIsSix : totalProduct twoThreeFactors ≡ 6
twoThreeTotalIsSix = refl

twoThreeSurvivorsIsTwo : survivorProduct twoThreeFactors ≡ 2
twoThreeSurvivorsIsTwo = refl

twoThreeExcludedIsFour : excludedCount twoThreeFactors ≡ 4
twoThreeExcludedIsFour = refl

record ProductSieveDensity (factors : List Nat) : Set where
  field
    survivorNumerator totalDenominator excludedNumerator : Nat
    survivorNumeratorExact : survivorNumerator ≡ survivorProduct factors
    totalDenominatorExact : totalDenominator ≡ totalProduct factors
    excludedNumeratorExact :
      excludedNumerator ≡ totalProduct factors ∸ survivorProduct factors

canonicalProductSieveDensity :
  (factors : List Nat) → ProductSieveDensity factors
canonicalProductSieveDensity factors = record
  { survivorNumerator = survivorProduct factors
  ; totalDenominator = totalProduct factors
  ; excludedNumerator = excludedCount factors
  ; survivorNumeratorExact = refl
  ; totalDenominatorExact = refl
  ; excludedNumeratorExact = refl
  }
