module DASHI.Biology.JFinePhaseQuotientFieldExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Ingrid Daubechies,
-- "Ten Lectures on Wavelets", SIAM, 1992.
-- DOI: 10.1137/1.9781611970104.
--
-- Audrey Terras,
-- "Fourier Analysis on Finite Groups and Applications",
-- Cambridge University Press, 1999.
-- DOI: 10.1017/CBO9780511626265.
--
-- DASHI CONTRIBUTION
--
-- Replace the opaque cardinal reading
--
--   jFine = Fin 19683
--
-- by an exact structured presentation as a ternary field on the nine
-- C3-phase quotient classes of T^T:
--
--   FineFrequency  <->  (PhaseQuotient9 -> TriTruth).
--
-- The codec is not postulated.  It is assembled recursively from the standard
-- finite product equivalence Fin m x Fin n <-> Fin (m*n), using
-- Data.Fin.combine/remQuot and their two round-trip laws.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong)

import Base369 as Base
import Data.Fin.Base as Fin
open import Data.Fin.Properties using
  ( remQuot-combine
  ; combine-remQuot
  )

import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Biology.JFineCoarseRelativeScaleExact as Scale
import DASHI.Foundations.TernaryEndomorphismPhaseQuotientExact as Phase

pow3 : Nat → Nat
pow3 zero = 1
pow3 (suc n) = 3 * pow3 n

data TritDigits : Nat → Set where
  [] : TritDigits zero
  _∷_ : ∀ {n} → Base.TriTruth → TritDigits n → TritDigits (suc n)

infixr 5 _∷_

triToFin3 : Base.TriTruth → Fin.Fin 3
triToFin3 Base.tri-low = Fin.zero
triToFin3 Base.tri-mid = Fin.suc Fin.zero
triToFin3 Base.tri-high = Fin.suc (Fin.suc Fin.zero)

fin3ToTri : Fin.Fin 3 → Base.TriTruth
fin3ToTri Fin.zero = Base.tri-low
fin3ToTri (Fin.suc Fin.zero) = Base.tri-mid
fin3ToTri (Fin.suc (Fin.suc Fin.zero)) = Base.tri-high

finAfterTri :
  (value : Base.TriTruth) →
  fin3ToTri (triToFin3 value) ≡ value
finAfterTri Base.tri-low = refl
finAfterTri Base.tri-mid = refl
finAfterTri Base.tri-high = refl

triAfterFin :
  (value : Fin.Fin 3) →
  triToFin3 (fin3ToTri value) ≡ value
triAfterFin Fin.zero = refl
triAfterFin (Fin.suc Fin.zero) = refl
triAfterFin (Fin.suc (Fin.suc Fin.zero)) = refl

encodeTritDigits :
  ∀ {n} → TritDigits n → Fin.Fin (pow3 n)
encodeTritDigits {zero} [] = Fin.zero
encodeTritDigits {suc n} (head ∷ tail) =
  Fin.combine (triToFin3 head) (encodeTritDigits tail)

decodeTritDigits :
  ∀ {n} → Fin.Fin (pow3 n) → TritDigits n
decodeTritDigits {zero} code = []
decodeTritDigits {suc n} code =
  fin3ToTri (proj₁ split) ∷
  decodeTritDigits (proj₂ split)
  where
  split = Fin.remQuot {m = 3} (pow3 n) code

decodeAfterEncodeTritDigits :
  ∀ {n} →
  (digits : TritDigits n) →
  decodeTritDigits (encodeTritDigits digits) ≡ digits
decodeAfterEncodeTritDigits {zero} [] = refl
decodeAfterEncodeTritDigits {suc n} (head ∷ tail)
  rewrite
    cong proj₁
      (remQuot-combine
        {n = 3} {k = pow3 n}
        (triToFin3 head) (encodeTritDigits tail))
  | cong proj₂
      (remQuot-combine
        {n = 3} {k = pow3 n}
        (triToFin3 head) (encodeTritDigits tail))
  | finAfterTri head
  | decodeAfterEncodeTritDigits tail = refl

encodeAfterDecodeTritDigits :
  ∀ {n} →
  (code : Fin.Fin (pow3 n)) →
  encodeTritDigits (decodeTritDigits code) ≡ code
encodeAfterDecodeTritDigits {zero} Fin.zero = refl
encodeAfterDecodeTritDigits {suc n} code
  rewrite
    triAfterFin
      (proj₁ (Fin.remQuot {m = 3} (pow3 n) code))
  | encodeAfterDecodeTritDigits
      (proj₂ (Fin.remQuot {m = 3} (pow3 n) code))
  = combine-remQuot {n = 3} (pow3 n) code

PhaseFineField : Set
PhaseFineField = Phase.PhaseQuotient9 → Base.TriTruth

record PhaseFineTable9 : Set where
  constructor phaseFineTable9
  field
    q00 q01 q02
      q10 q11 q12
      q20 q21 q22 : Base.TriTruth

open PhaseFineTable9 public

tabulatePhaseFine : PhaseFineField → PhaseFineTable9
tabulatePhaseFine field =
  phaseFineTable9
    (field (Base.tri-low , Base.tri-low))
    (field (Base.tri-low , Base.tri-mid))
    (field (Base.tri-low , Base.tri-high))
    (field (Base.tri-mid , Base.tri-low))
    (field (Base.tri-mid , Base.tri-mid))
    (field (Base.tri-mid , Base.tri-high))
    (field (Base.tri-high , Base.tri-low))
    (field (Base.tri-high , Base.tri-mid))
    (field (Base.tri-high , Base.tri-high))

lookupPhaseFine : PhaseFineTable9 → PhaseFineField
lookupPhaseFine table (Base.tri-low , Base.tri-low) = q00 table
lookupPhaseFine table (Base.tri-low , Base.tri-mid) = q01 table
lookupPhaseFine table (Base.tri-low , Base.tri-high) = q02 table
lookupPhaseFine table (Base.tri-mid , Base.tri-low) = q10 table
lookupPhaseFine table (Base.tri-mid , Base.tri-mid) = q11 table
lookupPhaseFine table (Base.tri-mid , Base.tri-high) = q12 table
lookupPhaseFine table (Base.tri-high , Base.tri-low) = q20 table
lookupPhaseFine table (Base.tri-high , Base.tri-mid) = q21 table
lookupPhaseFine table (Base.tri-high , Base.tri-high) = q22 table

lookupAfterTabulate :
  (field : PhaseFineField) →
  (pair : Phase.PhaseQuotient9) →
  lookupPhaseFine (tabulatePhaseFine field) pair ≡ field pair
lookupAfterTabulate field (Base.tri-low , Base.tri-low) = refl
lookupAfterTabulate field (Base.tri-low , Base.tri-mid) = refl
lookupAfterTabulate field (Base.tri-low , Base.tri-high) = refl
lookupAfterTabulate field (Base.tri-mid , Base.tri-low) = refl
lookupAfterTabulate field (Base.tri-mid , Base.tri-mid) = refl
lookupAfterTabulate field (Base.tri-mid , Base.tri-high) = refl
lookupAfterTabulate field (Base.tri-high , Base.tri-low) = refl
lookupAfterTabulate field (Base.tri-high , Base.tri-mid) = refl
lookupAfterTabulate field (Base.tri-high , Base.tri-high) = refl

tabulateAfterLookup :
  (table : PhaseFineTable9) →
  tabulatePhaseFine (lookupPhaseFine table) ≡ table
tabulateAfterLookup
  (phaseFineTable9 a b c d e f g h i) = refl

TritDigits9 : Set
TritDigits9 = TritDigits 9

digitsFromTable : PhaseFineTable9 → TritDigits9
digitsFromTable table =
  q00 table ∷ q01 table ∷ q02 table ∷
  q10 table ∷ q11 table ∷ q12 table ∷
  q20 table ∷ q21 table ∷ q22 table ∷ []

tableFromDigits : TritDigits9 → PhaseFineTable9
tableFromDigits
  (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ []) =
  phaseFineTable9 a b c d e f g h i

tableAfterDigits :
  (table : PhaseFineTable9) →
  tableFromDigits (digitsFromTable table) ≡ table
tableAfterDigits
  (phaseFineTable9 a b c d e f g h i) = refl

digitsAfterTable :
  (digits : TritDigits9) →
  digitsFromTable (tableFromDigits digits) ≡ digits
digitsAfterTable
  (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ []) = refl

fieldToDigits : PhaseFineField → TritDigits9
fieldToDigits field = digitsFromTable (tabulatePhaseFine field)

digitsToField : TritDigits9 → PhaseFineField
digitsToField digits = lookupPhaseFine (tableFromDigits digits)

digitsAfterField :
  (digits : TritDigits9) →
  fieldToDigits (digitsToField digits) ≡ digits
digitsAfterField
  (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ []) = refl

fieldAfterDigitsPointwise :
  (field : PhaseFineField) →
  (pair : Phase.PhaseQuotient9) →
  digitsToField (fieldToDigits field) pair ≡ field pair
fieldAfterDigitsPointwise field pair
  rewrite tableAfterDigits (tabulatePhaseFine field) =
  lookupAfterTabulate field pair

phaseFineCardinality : Nat
phaseFineCardinality = pow3 9

phaseFineCardinalityIs19683 : phaseFineCardinality ≡ 19683
phaseFineCardinalityIs19683 = refl

encodePhaseFineField :
  PhaseFineField → Harmonic.FineFrequency
encodePhaseFineField field =
  encodeTritDigits (fieldToDigits field)

decodePhaseFineField :
  Harmonic.FineFrequency → PhaseFineField
decodePhaseFineField fine =
  digitsToField (decodeTritDigits fine)

encodeAfterDecodePhaseFine :
  (fine : Harmonic.FineFrequency) →
  encodePhaseFineField (decodePhaseFineField fine) ≡ fine
encodeAfterDecodePhaseFine fine
  rewrite digitsAfterField (decodeTritDigits fine) =
  encodeAfterDecodeTritDigits fine

decodeAfterEncodePhaseFinePointwise :
  (field : PhaseFineField) →
  (pair : Phase.PhaseQuotient9) →
  decodePhaseFineField (encodePhaseFineField field) pair ≡ field pair
decodeAfterEncodePhaseFinePointwise field pair
  rewrite decodeAfterEncodeTritDigits (fieldToDigits field) =
  fieldAfterDigitsPointwise field pair

PhaseAbsoluteField : Set
PhaseAbsoluteField = Phase.PhaseQuotient9 × PhaseFineField

phaseCoarseCardinality : Nat
phaseCoarseCardinality = 9

phaseAbsoluteCardinality : Nat
phaseAbsoluteCardinality =
  phaseCoarseCardinality * phaseFineCardinality

phaseAbsoluteCardinalityIsThreePowerEleven :
  phaseAbsoluteCardinality ≡ 177147
phaseAbsoluteCardinalityIsThreePowerEleven = refl

phaseAbsoluteMatchesExistingJScale :
  phaseAbsoluteCardinality ≡ Scale.jAbsoluteFineFrequency
phaseAbsoluteMatchesExistingJScale = refl

existingJFineMatchesStructuredFieldCount :
  Scale.jFineFrequency ≡ phaseFineCardinality
existingJFineMatchesStructuredFieldCount = refl

record JFinePhaseQuotientFieldEquivalence : Set₁ where
  field
    encode : PhaseFineField → Harmonic.FineFrequency
    decode : Harmonic.FineFrequency → PhaseFineField
    encodeDecode :
      (fine : Harmonic.FineFrequency) →
      encode (decode fine) ≡ fine
    decodeEncodePointwise :
      (field : PhaseFineField) →
      (pair : Phase.PhaseQuotient9) →
      decode (encode field) pair ≡ field pair

canonicalJFinePhaseQuotientFieldEquivalence :
  JFinePhaseQuotientFieldEquivalence
canonicalJFinePhaseQuotientFieldEquivalence =
  record
    { encode = encodePhaseFineField
    ; decode = decodePhaseFineField
    ; encodeDecode = encodeAfterDecodePhaseFine
    ; decodeEncodePointwise = decodeAfterEncodePhaseFinePointwise
    }

record JFinePhaseQuotientBoundary : Set where
  field
    structuredFineFieldCodecConstructed : Bool
    structuredFineFieldCodecConstructedIsTrue :
      structuredFineFieldCodecConstructed ≡ true
    absoluteThreePowerElevenDerivedFromNineTimesThreePowerNine : Bool
    absoluteThreePowerElevenDerivedFromNineTimesThreePowerNineIsTrue :
      absoluteThreePowerElevenDerivedFromNineTimesThreePowerNine ≡ true
    functionExtensionalityPostulated : Bool
    functionExtensionalityPostulatedIsFalse :
      functionExtensionalityPostulated ≡ false

canonicalJFinePhaseQuotientBoundary : JFinePhaseQuotientBoundary
canonicalJFinePhaseQuotientBoundary =
  record
    { structuredFineFieldCodecConstructed = true
    ; structuredFineFieldCodecConstructedIsTrue = refl
    ; absoluteThreePowerElevenDerivedFromNineTimesThreePowerNine = true
    ; absoluteThreePowerElevenDerivedFromNineTimesThreePowerNineIsTrue = refl
    ; functionExtensionalityPostulated = false
    ; functionExtensionalityPostulatedIsFalse = refl
    }
