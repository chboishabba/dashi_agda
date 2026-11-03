module DASHI.Biology.GenBankCanonicalDNAFibreIndexExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)

import DASHI.Codec.DNAFirstFormalism as DNA
import DASHI.Codec.DNACarrierFibre as Fibre

-- The existing DNA.Base is authoritative. We do not define a new base
-- alphabet. This same-object adapter formalises index-preserving transport
-- from the canonical DNA carrier to its pre-existing quotient/fibre encoding.
-- It does NOT claim that arbitrary GenBank raw bytes were parsed correctly.

data Vec (A : Set) : Nat → Set where
  []  : Vec A zero
  _∷_ : {n : Nat} → A → Vec A n → Vec A (suc n)
infixr 5 _∷_

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc : {n : Nat} → Fin n → Fin (suc n)

lookup : {A : Set} {n : Nat} → Vec A n → Fin n → A
lookup (x ∷ xs) fzero = x
lookup (x ∷ xs) (fsuc i) = lookup xs i

mapVec : {A B : Set} {n : Nat} →
         (A → B) → Vec A n → Vec B n
mapVec f [] = []
mapVec f (x ∷ xs) = f x ∷ mapVec f xs

encode : {n : Nat} → Vec DNA.Base n → Vec Fibre.BaseFibre n
encode = mapVec Fibre.encodeBaseFibre

decode : {n : Nat} → Vec Fibre.BaseFibre n → Vec DNA.Base n
decode = mapVec Fibre.decodeBaseFibre

-- Indexing commutes with both encoders, for every finite list length and
-- every actual finite index, rather than only for a selected example.
lookupMap : {A B : Set} {n : Nat} (f : A → B) →
            (xs : Vec A n) (i : Fin n) →
            lookup (mapVec f xs) i ≡ f (lookup xs i)
lookupMap f (x ∷ xs) fzero = refl
lookupMap f (x ∷ xs) (fsuc i) = lookupMap f xs i

encodePreservesIndex : {n : Nat} (xs : Vec DNA.Base n) →
                       (i : Fin n) →
                       lookup (encode xs) i ≡
                       Fibre.encodeBaseFibre (lookup xs i)
encodePreservesIndex = lookupMap Fibre.encodeBaseFibre

decodePreservesIndex : {n : Nat} (fs : Vec Fibre.BaseFibre n) →
                       (i : Fin n) →
                       lookup (decode fs) i ≡
                       Fibre.decodeBaseFibre (lookup fs i)
decodePreservesIndex = lookupMap Fibre.decodeBaseFibre

decodeEncode : {n : Nat} (xs : Vec DNA.Base n) →
               decode (encode xs) ≡ xs
decodeEncode [] = refl
decodeEncode (x ∷ xs)
  rewrite Fibre.decode-encode-base x | decodeEncode xs = refl

-- The original raw file SHA-256 and the normalized semantic SHA-256 are
-- NOT inputs to this theorem. They need an external source/replay receipt
-- and a checked generated finite witness before same-object promotion.
