{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedTraceFactorExact where

------------------------------------------------------------------------
-- K05 N21: REPLAYABLE SIGNED BINARY WEIGHT TRACE FACTORISATION.
--
-- Original sparse cut selects a sequence of signed gamma edge weights.
-- Classify identical original sign/magnitude bitwords. Store multiplicity
-- in BINARY and replay each class once using the certified-by-source
-- shift/add scaler, instead of repeating each large signed addition.
--
-- This is the precise operation-reuse idea from signed SSP/FRACTRAN:
-- weight class = operation, count = valuation, two output score lanes.
-- It does not assert Monster actions or general FRACTRAN simulation.
--
-- All class keys are the actual original SignedMagnitudeBits; canonical
-- numeric key equality follows only after the original signed gamma
-- value/suffix weld is kernel-certified.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; length; reverse)
open import Relation.Binary.PropositionalEquality using (cong; trans)
import Data.Nat.Properties as NatP
open import Data.Product using (_×_; _,_)
import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedExact as Signed
import DASHI.Mathematics.Complexity.Karp21BinaryWordEqualityPrimitiveExact as Eq
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderExact as Add
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedLedgerExact as Ledger
import DASHI.Mathematics.Complexity.Karp21BinaryNativeMultiplicityScaleExact as Scale
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderValueExact as Value

sameSignedToken :
  Signed.SignedMagnitudeBits → Signed.SignedMagnitudeBits → Bool
sameSignedToken (Signed.positive x) (Signed.positive y) =
  Eq.equalBitWords x y
sameSignedToken (Signed.negative x) (Signed.negative y) =
  Eq.equalBitWords x y
sameSignedToken (Signed.positive x) (Signed.negative y) = false
sameSignedToken (Signed.negative x) (Signed.positive y) = false

-- Each multiplicity is little endian, just like the arithmetic lanes.
SignedWeightClass : Set
SignedWeightClass = Signed.SignedMagnitudeBits × Word.BitWord

SignedTraceFactors : Set
SignedTraceFactors = List SignedWeightClass

binaryOne : Word.BitWord
binaryOne = true ∷ []

addOccurrence :
  Signed.SignedMagnitudeBits → SignedTraceFactors → SignedTraceFactors
addOccurrence weight [] = (weight , binaryOne) ∷ []
addOccurrence weight ((candidate , count) ∷ classes)
  with sameSignedToken weight candidate
... | true =
  (candidate , Add.addBits count binaryOne) ∷ classes
... | false =
  (candidate , count) ∷ addOccurrence weight classes

factorSignedTrace :
  List Signed.SignedMagnitudeBits → SignedTraceFactors
factorSignedTrace [] = []
factorSignedTrace (weight ∷ rest) =
  addOccurrence weight (factorSignedTrace rest)

insertFactor :
  SignedWeightClass → Ledger.SignedLedger → Ledger.SignedLedger
insertFactor (Signed.positive magnitude , count) (positive , negative) =
  Add.addBits positive (Scale.scaleBits
    (Data.List.Base.reverse magnitude) count) , negative
insertFactor (Signed.negative magnitude , count) (positive , negative) =
  positive , Add.addBits negative (Scale.scaleBits
    (Data.List.Base.reverse magnitude) count)

replayFactors :
  SignedTraceFactors → Ledger.SignedLedger → Ledger.SignedLedger
replayFactors [] ledger = ledger
replayFactors (factor ∷ factors) ledger =
  replayFactors factors (insertFactor factor ledger)

replaySignedTrace :
  List Signed.SignedMagnitudeBits → Ledger.SignedLedger
replaySignedTrace trace =
  replayFactors (factorSignedTrace trace) Ledger.emptyLedger

-- Literal checks on actual signed token representation.
positiveOneEqual :
  sameSignedToken (Signed.positive (true ∷ []))
    (Signed.positive (true ∷ [])) ≡ true
positiveOneEqual = refl

differentSignNeverMerged :
  sameSignedToken (Signed.positive (true ∷ []))
    (Signed.negative (true ∷ [])) ≡ false
differentSignNeverMerged = refl

twoIdenticalWeightsOneClass :
  length (factorSignedTrace
    (Signed.positive (true ∷ []) ∷
     Signed.positive (true ∷ []) ∷ []))
  ≡ suc zero
twoIdenticalWeightsOneClass = refl

-- Numeric replay equivalence to the original rawSparseScore, and the
-- actual resource/description trade-off, remain exact P0 proof gates.

------------------------------------------------------------------------
-- Non-oracle whole-word equal-key proof: distinct weight classes are
-- only merged when the SAME original binary sign/magnitude token
-- has been proved equal, not merely on a hash collision.
------------------------------------------------------------------------

sameSignedTokenSound :
  (left right : Signed.SignedMagnitudeBits) →
  sameSignedToken left right ≡ true →
  left ≡ right
sameSignedTokenSound (Signed.positive x) (Signed.positive y) eq =
  cong Signed.positive (Eq.bitWordEqualitySound x y eq)
sameSignedTokenSound (Signed.negative x) (Signed.negative y) eq =
  cong Signed.negative (Eq.bitWordEqualitySound x y eq)
sameSignedTokenSound (Signed.positive x) (Signed.negative y) ()
sameSignedTokenSound (Signed.negative x) (Signed.positive y) ()

-- The binary counter's +1 is correct for arbitrarily many
-- repetitions and all noncanonical counter bitwords.
binaryCounterIncrementValue :
  (count : Word.BitWord) →
  Value.valueLE (Add.addBits count binaryOne)
    ≡ suc (Value.valueLE count)
binaryCounterIncrementValue count =
  trans
    (Value.addBitsValue count binaryOne)
    (NatP.+-comm (Value.valueLE count) (suc zero))

-- Semantic contribution of each stored factor, observed only in
-- proofs; executable replay uses the actual SCALE/ADD primitives.
positiveClassTotal : SignedWeightClass → Nat
positiveClassTotal (Signed.positive magnitude , count) =
  Value.valueLE (reverse magnitude) * Value.valueLE count
positiveClassTotal (Signed.negative magnitude , count) = zero

negativeClassTotal : SignedWeightClass → Nat
negativeClassTotal (Signed.positive magnitude , count) = zero
negativeClassTotal (Signed.negative magnitude , count) =
  Value.valueLE (reverse magnitude) * Value.valueLE count

positiveFactorTotal : SignedTraceFactors → Nat
positiveFactorTotal [] = zero
positiveFactorTotal (factor ∷ rest) =
  positiveClassTotal factor + positiveFactorTotal rest

negativeFactorTotal : SignedTraceFactors → Nat
negativeFactorTotal [] = zero
negativeFactorTotal (factor ∷ rest) =
  negativeClassTotal factor + negativeFactorTotal rest

insertFactorPositiveValue :
  (factor : SignedWeightClass) (ledger : Ledger.SignedLedger) →
  Ledger.positiveValue (insertFactor factor ledger) ≡
    Ledger.positiveValue ledger + positiveClassTotal factor
insertFactorPositiveValue (Signed.positive magnitude , count)
  (positive , negative) =
  trans
    (Value.addBitsValue positive
      (Scale.scaleBits (reverse magnitude) count))
    (cong (λ x → Value.valueLE positive + x)
      (Scale.scaleBitsValue (reverse magnitude) count))
insertFactorPositiveValue (Signed.negative magnitude , count)
  (positive , negative) =
  NatP.+-identityʳ (Value.valueLE positive)

insertFactorNegativeValue :
  (factor : SignedWeightClass) (ledger : Ledger.SignedLedger) →
  Ledger.negativeValue (insertFactor factor ledger) ≡
    Ledger.negativeValue ledger + negativeClassTotal factor
insertFactorNegativeValue (Signed.positive magnitude , count)
  (positive , negative) =
  NatP.+-identityʳ (Value.valueLE negative)
insertFactorNegativeValue (Signed.negative magnitude , count)
  (positive , negative) =
  trans
    (Value.addBitsValue negative
      (Scale.scaleBits (reverse magnitude) count))
    (cong (λ x → Value.valueLE negative + x)
      (Scale.scaleBitsValue (reverse magnitude) count))

replayFactorsPositiveValue :
  (factors : SignedTraceFactors) (ledger : Ledger.SignedLedger) →
  Ledger.positiveValue (replayFactors factors ledger) ≡
    Ledger.positiveValue ledger + positiveFactorTotal factors
replayFactorsPositiveValue [] ledger =
  NatP.+-identityʳ (Ledger.positiveValue ledger)
replayFactorsPositiveValue (factor ∷ rest) ledger =
  trans
    (replayFactorsPositiveValue rest (insertFactor factor ledger))
    (trans
      (cong (λ x → x + positiveFactorTotal rest)
        (insertFactorPositiveValue factor ledger))
      (NatP.+-assoc
        (Ledger.positiveValue ledger)
        (positiveClassTotal factor)
        (positiveFactorTotal rest)))

replayFactorsNegativeValue :
  (factors : SignedTraceFactors) (ledger : Ledger.SignedLedger) →
  Ledger.negativeValue (replayFactors factors ledger) ≡
    Ledger.negativeValue ledger + negativeFactorTotal factors
replayFactorsNegativeValue [] ledger =
  NatP.+-identityʳ (Ledger.negativeValue ledger)
replayFactorsNegativeValue (factor ∷ rest) ledger =
  trans
    (replayFactorsNegativeValue rest (insertFactor factor ledger))
    (trans
      (cong (λ x → x + negativeFactorTotal rest)
        (insertFactorNegativeValue factor ledger))
      (NatP.+-assoc
        (Ledger.negativeValue ledger)
        (negativeClassTotal factor)
        (negativeFactorTotal rest)))
