module DASHI.Arithmetic.SixWheelSieveCountExact where

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
-- Give the {2,3}-sieve an exact finite carrier rather than only the familiar
-- sentence "primes > 3 are +/-1 mod 6".  A six-cell block splits bijectively
-- into four excluded residue species {0,2,3,4} and two survivor species {1,5}.
-- For k blocks this yields two-sided encodings
--
--   Excluded(k)  <-> Fin (k*4)
--   Survivor(k)  <-> Fin (k*2)
--
-- and the exact density identities (by cross multiplication)
--
--   excluded : (4k)/(6k) = 2/3,
--   survivor : (2k)/(6k) = 1/3.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Empty using (⊥)
open import Data.Fin.Base as Fin using (Fin)
open import Data.Fin.Properties using (remQuot-combine; combine-remQuot)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:*_; _:+_; con; _:=_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong)

data Residue6 : Set where
  r0 r1 r2 r3 r4 r5 : Residue6

data ExcludedResidue6 : Set where
  e0 e2 e3 e4 : ExcludedResidue6

data SurvivorResidue6 : Set where
  s1 s5 : SurvivorResidue6

classifyResidue6 : Residue6 → ExcludedResidue6 ⊎ SurvivorResidue6
classifyResidue6 r0 = inj₁ e0
classifyResidue6 r1 = inj₂ s1
classifyResidue6 r2 = inj₁ e2
classifyResidue6 r3 = inj₁ e3
classifyResidue6 r4 = inj₁ e4
classifyResidue6 r5 = inj₂ s5

forgetResidueClass : ExcludedResidue6 ⊎ SurvivorResidue6 → Residue6
forgetResidueClass (inj₁ e0) = r0
forgetResidueClass (inj₁ e2) = r2
forgetResidueClass (inj₁ e3) = r3
forgetResidueClass (inj₁ e4) = r4
forgetResidueClass (inj₂ s1) = r1
forgetResidueClass (inj₂ s5) = r5

forgetAfterClassify :
  (r : Residue6) →
  forgetResidueClass (classifyResidue6 r) ≡ r
forgetAfterClassify r0 = refl
forgetAfterClassify r1 = refl
forgetAfterClassify r2 = refl
forgetAfterClassify r3 = refl
forgetAfterClassify r4 = refl
forgetAfterClassify r5 = refl

classifyAfterForget :
  (r : ExcludedResidue6 ⊎ SurvivorResidue6) →
  classifyResidue6 (forgetResidueClass r) ≡ r
classifyAfterForget (inj₁ e0) = refl
classifyAfterForget (inj₁ e2) = refl
classifyAfterForget (inj₁ e3) = refl
classifyAfterForget (inj₁ e4) = refl
classifyAfterForget (inj₂ s1) = refl
classifyAfterForget (inj₂ s5) = refl

excludedToFin4 : ExcludedResidue6 → Fin 4
excludedToFin4 e0 = Fin.zero
excludedToFin4 e2 = Fin.suc Fin.zero
excludedToFin4 e3 = Fin.suc (Fin.suc Fin.zero)
excludedToFin4 e4 = Fin.suc (Fin.suc (Fin.suc Fin.zero))

fin4ToExcluded : Fin 4 → ExcludedResidue6
fin4ToExcluded Fin.zero = e0
fin4ToExcluded (Fin.suc Fin.zero) = e2
fin4ToExcluded (Fin.suc (Fin.suc Fin.zero)) = e3
fin4ToExcluded (Fin.suc (Fin.suc (Fin.suc Fin.zero))) = e4

excludedRoundTrip :
  (r : ExcludedResidue6) →
  fin4ToExcluded (excludedToFin4 r) ≡ r
excludedRoundTrip e0 = refl
excludedRoundTrip e2 = refl
excludedRoundTrip e3 = refl
excludedRoundTrip e4 = refl

fin4RoundTrip :
  (i : Fin 4) →
  excludedToFin4 (fin4ToExcluded i) ≡ i
fin4RoundTrip Fin.zero = refl
fin4RoundTrip (Fin.suc Fin.zero) = refl
fin4RoundTrip (Fin.suc (Fin.suc Fin.zero)) = refl
fin4RoundTrip (Fin.suc (Fin.suc (Fin.suc Fin.zero))) = refl

survivorToFin2 : SurvivorResidue6 → Fin 2
survivorToFin2 s1 = Fin.zero
survivorToFin2 s5 = Fin.suc Fin.zero

fin2ToSurvivor : Fin 2 → SurvivorResidue6
fin2ToSurvivor Fin.zero = s1
fin2ToSurvivor (Fin.suc Fin.zero) = s5

survivorRoundTrip :
  (r : SurvivorResidue6) →
  fin2ToSurvivor (survivorToFin2 r) ≡ r
survivorRoundTrip s1 = refl
survivorRoundTrip s5 = refl

fin2RoundTrip :
  (i : Fin 2) →
  survivorToFin2 (fin2ToSurvivor i) ≡ i
fin2RoundTrip Fin.zero = refl
fin2RoundTrip (Fin.suc Fin.zero) = refl

ExcludedCell : Nat → Set
ExcludedCell k = Fin k × ExcludedResidue6

SurvivorCell : Nat → Set
SurvivorCell k = Fin k × SurvivorResidue6

encodeExcludedCell :
  ∀ {k} → ExcludedCell k → Fin (k * 4)
encodeExcludedCell (block , residue) =
  Fin.combine block (excludedToFin4 residue)

decodeExcludedCell :
  ∀ {k} → Fin (k * 4) → ExcludedCell k
decodeExcludedCell {k} code =
  proj₁ split , fin4ToExcluded (proj₂ split)
  where
  split = Fin.remQuot {m = k} 4 code

excludedDecodeEncode :
  ∀ {k} →
  (cell : ExcludedCell k) →
  decodeExcludedCell (encodeExcludedCell cell) ≡ cell
excludedDecodeEncode {k} (block , residue)
  rewrite
    cong proj₁
      (remQuot-combine
        {n = k} {k = 4}
        block (excludedToFin4 residue))
  | cong proj₂
      (remQuot-combine
        {n = k} {k = 4}
        block (excludedToFin4 residue))
  | excludedRoundTrip residue = refl

excludedEncodeDecode :
  ∀ {k} →
  (code : Fin (k * 4)) →
  encodeExcludedCell (decodeExcludedCell code) ≡ code
excludedEncodeDecode {k} code
  rewrite
    fin4RoundTrip
      (proj₂ (Fin.remQuot {m = k} 4 code)) =
  combine-remQuot {n = k} 4 code

encodeSurvivorCell :
  ∀ {k} → SurvivorCell k → Fin (k * 2)
encodeSurvivorCell (block , residue) =
  Fin.combine block (survivorToFin2 residue)

decodeSurvivorCell :
  ∀ {k} → Fin (k * 2) → SurvivorCell k
decodeSurvivorCell {k} code =
  proj₁ split , fin2ToSurvivor (proj₂ split)
  where
  split = Fin.remQuot {m = k} 2 code

survivorDecodeEncode :
  ∀ {k} →
  (cell : SurvivorCell k) →
  decodeSurvivorCell (encodeSurvivorCell cell) ≡ cell
survivorDecodeEncode {k} (block , residue)
  rewrite
    cong proj₁
      (remQuot-combine
        {n = k} {k = 2}
        block (survivorToFin2 residue))
  | cong proj₂
      (remQuot-combine
        {n = k} {k = 2}
        block (survivorToFin2 residue))
  | survivorRoundTrip residue = refl

survivorEncodeDecode :
  ∀ {k} →
  (code : Fin (k * 2)) →
  encodeSurvivorCell (decodeSurvivorCell code) ≡ code
survivorEncodeDecode {k} code
  rewrite
    fin2RoundTrip
      (proj₂ (Fin.remQuot {m = k} 2 code)) =
  combine-remQuot {n = k} 2 code

sixBlockCountSplitsFourPlusTwo :
  (k : Nat) →
  k * 6 ≡ k * 4 + k * 2
sixBlockCountSplitsFourPlusTwo =
  solve 1
    (λ k →
      k :* con 6 :=
      (k :* con 4) :+ (k :* con 2))
    refl

excludedDensityTwoThirdsCrossMultiplied :
  (k : Nat) →
  3 * (k * 4) ≡ 2 * (k * 6)
excludedDensityTwoThirdsCrossMultiplied =
  solve 1
    (λ k →
      con 3 :* (k :* con 4)
      :=
      con 2 :* (k :* con 6))
    refl

survivorDensityOneThirdCrossMultiplied :
  (k : Nat) →
  3 * (k * 2) ≡ k * 6
survivorDensityOneThirdCrossMultiplied =
  solve 1
    (λ k →
      con 3 :* (k :* con 2)
      :=
      k :* con 6)
    refl
