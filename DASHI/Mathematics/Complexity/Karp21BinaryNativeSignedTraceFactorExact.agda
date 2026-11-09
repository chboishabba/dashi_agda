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
open import Data.List.Base using (List; length)
open import Data.Product using (_×_; _,_)
import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedExact as Signed
import DASHI.Mathematics.Complexity.Karp21BinaryWordEqualityPrimitiveExact as Eq
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderExact as Add
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedLedgerExact as Ledger
import DASHI.Mathematics.Complexity.Karp21BinaryNativeMultiplicityScaleExact as Scale

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
