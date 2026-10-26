module DASHI.Moonshine.Generated.OggSSPKernelFieldRecognitionGenerated where

-- GENERATED FROM scripts/j369_kernel_field_recognition.py.
-- Runtime finite-field certificates only; no intrinsic field recognition.

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

k4FieldOrder : Nat
k4FieldOrder = 81
k5FieldOrder : Nat
k5FieldOrder = 243
k6FieldOrder : Nat
k6FieldOrder = 729

k4PrimitiveOrder : Nat
k4PrimitiveOrder = 80
k5PrimitiveOrder : Nat
k5PrimitiveOrder = 242
k6PrimitiveOrder : Nat
k6PrimitiveOrder = 728

k4NegationNonzeroOrbitCount : Nat
k4NegationNonzeroOrbitCount = 40
k5NegationNonzeroOrbitCount : Nat
k5NegationNonzeroOrbitCount = 121
k6NegationNonzeroOrbitCount : Nat
k6NegationNonzeroOrbitCount = 364

k4FrobeniusFixedCount : Nat
k4FrobeniusFixedCount = 3
k4FrobeniusTwoCycleCount : Nat
k4FrobeniusTwoCycleCount = 3
k4FrobeniusFourCycleCount : Nat
k4FrobeniusFourCycleCount = 18

k5FrobeniusFixedCount : Nat
k5FrobeniusFixedCount = 3
k5FrobeniusFiveCycleCount : Nat
k5FrobeniusFiveCycleCount = 48

k6FrobeniusFixedCount : Nat
k6FrobeniusFixedCount = 3
k6FrobeniusTwoCycleCount : Nat
k6FrobeniusTwoCycleCount = 3
k6FrobeniusThreeCycleCount : Nat
k6FrobeniusThreeCycleCount = 8
k6FrobeniusSixCycleCount : Nat
k6FrobeniusSixCycleCount = 116

k4GF9SubfieldLinearImageSize : Nat
k4GF9SubfieldLinearImageSize = 9
k4GF9SubfieldEqualsFrobenius2FixedSet : Bool
k4GF9SubfieldEqualsFrobenius2FixedSet = true
k4GF9SubfieldIsNaivePrefixK2 : Bool
k4GF9SubfieldIsNaivePrefixK2 = false
k4T5ChosenSubfieldObjectMapPaid : Bool
k4T5ChosenSubfieldObjectMapPaid = true

rowMajor12VectorEmbeddingFound : Bool
rowMajor12VectorEmbeddingFound = false
rowMajorMinimumVectorCount : Nat
rowMajorMinimumVectorCount = 196

fullSignedCanonicalTotalStepFound : Bool
fullSignedCanonicalTotalStepFound = false
chosenFieldMultiplicationRuntimeVerified : Bool
chosenFieldMultiplicationRuntimeVerified = true
fullFieldRecognitionPaid : Bool
fullFieldRecognitionPaid = false

k4PunctureCountExact : 80 + 1 ≡ 81
k4PunctureCountExact = refl
k5PunctureCountExact : 242 + 1 ≡ 243
k5PunctureCountExact = refl
k6PunctureCountExact : 728 + 1 ≡ 729
k6PunctureCountExact = refl

k4NegationOrbitChecksum : 2 * 40 ≡ 80
k4NegationOrbitChecksum = refl
k5NegationOrbitChecksum : 2 * 121 ≡ 242
k5NegationOrbitChecksum = refl
k6NegationOrbitChecksum : 2 * 364 ≡ 728
k6NegationOrbitChecksum = refl

k4FrobeniusOrbitChecksum : 3 + 2 * 3 + 4 * 18 ≡ 81
k4FrobeniusOrbitChecksum = refl
k5FrobeniusOrbitChecksum : 3 + 5 * 48 ≡ 243
k5FrobeniusOrbitChecksum = refl
k6FrobeniusOrbitChecksum : 3 + 2 * 3 + 3 * 8 + 6 * 116 ≡ 729
k6FrobeniusOrbitChecksum = refl

k4GF9SubfieldCountExact : k4GF9SubfieldLinearImageSize ≡ 9
k4GF9SubfieldCountExact = refl
