module DASHI.Moonshine.OggSSPTriadicKernelFieldRecognitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Algebra.Trit as Trit
import DASHI.Codec.TriadicPAdicCodec as Codec
import DASHI.Moonshine.OggSSPTriadicKernelF3LinearExact as Linear
import DASHI.Moonshine.Generated.OggSSPKernelFieldRecognitionGenerated as Generated

Kernel4 Kernel5 Kernel6 : Set
Kernel4 = Linear.Kernel4
Kernel5 = Linear.Kernel5
Kernel6 = Linear.Kernel6

k4ChosenFieldOrderExact : Generated.k4FieldOrder ≡ 81
k4ChosenFieldOrderExact = refl
k5ChosenFieldOrderExact : Generated.k5FieldOrder ≡ 243
k5ChosenFieldOrderExact = refl
k6ChosenFieldOrderExact : Generated.k6FieldOrder ≡ 729
k6ChosenFieldOrderExact = refl

k4ChosenMultiplicativeGroupOrderExact : Generated.k4PrimitiveOrder ≡ 80
k4ChosenMultiplicativeGroupOrderExact = refl
k5ChosenMultiplicativeGroupOrderExact : Generated.k5PrimitiveOrder ≡ 242
k5ChosenMultiplicativeGroupOrderExact = refl
k6ChosenMultiplicativeGroupOrderExact : Generated.k6PrimitiveOrder ≡ 728
k6ChosenMultiplicativeGroupOrderExact = refl

k4PunctureChecksum : 80 + 1 ≡ 81
k4PunctureChecksum = Generated.k4PunctureCountExact
k5PunctureChecksum : 242 + 1 ≡ 243
k5PunctureChecksum = Generated.k5PunctureCountExact
k6PunctureChecksum : 728 + 1 ≡ 729
k6PunctureChecksum = Generated.k6PunctureCountExact

k4NegationOrbitChecksum : 2 * 40 ≡ 80
k4NegationOrbitChecksum = Generated.k4NegationOrbitChecksum
k5NegationOrbitChecksum : 2 * 121 ≡ 242
k5NegationOrbitChecksum = Generated.k5NegationOrbitChecksum
k6NegationOrbitChecksum : 2 * 364 ≡ 728
k6NegationOrbitChecksum = Generated.k6NegationOrbitChecksum

k4FrobeniusOrbitChecksum : 3 + 2 * 3 + 4 * 18 ≡ 81
k4FrobeniusOrbitChecksum = Generated.k4FrobeniusOrbitChecksum
k5FrobeniusOrbitChecksum : 3 + 5 * 48 ≡ 243
k5FrobeniusOrbitChecksum = Generated.k5FrobeniusOrbitChecksum
k6FrobeniusOrbitChecksum : 3 + 2 * 3 + 3 * 8 + 6 * 116 ≡ 729
k6FrobeniusOrbitChecksum = Generated.k6FrobeniusOrbitChecksum

-- Source-level action weld: the pre-existing codec inversion is exactly the
-- scalar -1 action for the explicit F3 coordinate operations.
k4MinusOneActionIsExistingInversion :
  (x : Kernel4) → Linear.scaleKernel Trit.neg x ≡ Codec.invertKernel x
k4MinusOneActionIsExistingInversion = Linear.scaleMinusOneIsCodecInversion

k5MinusOneActionIsExistingInversion :
  (x : Kernel5) → Linear.scaleKernel Trit.neg x ≡ Codec.invertKernel x
k5MinusOneActionIsExistingInversion = Linear.scaleMinusOneIsCodecInversion

k6MinusOneActionIsExistingInversion :
  (x : Kernel6) → Linear.scaleKernel Trit.neg x ≡ Codec.invertKernel x
k6MinusOneActionIsExistingInversion = Linear.scaleMinusOneIsCodecInversion

record PartialRecognitionPayment : Set where
  constructor partial-recognition-payment
  field
    coordinateObjectMapPaid : Bool
    additiveF3StructurePaid : Bool
    c2ArrowMapPaid : Bool
    c2ActionIntertwiningPaid : Bool
    c2OrbitProfileRuntimePaid : Bool
    chosenFieldMultiplicationRuntimePaid : Bool
    chosenFieldMultiplicationCanonical : Bool
    fullActionGroupoidRecognitionPaid : Bool

open PartialRecognitionPayment public

k4FieldRecognitionPayment : PartialRecognitionPayment
k4FieldRecognitionPayment =
  partial-recognition-payment true true true true true true false false
k5FieldRecognitionPayment : PartialRecognitionPayment
k5FieldRecognitionPayment =
  partial-recognition-payment true true true true true true false false
k6FieldRecognitionPayment : PartialRecognitionPayment
k6FieldRecognitionPayment =
  partial-recognition-payment true true true true true true false false

data ChosenPolynomialImpliesCanonicalFieldStructure : Set where
data C2NegationIntertwiningImpliesFullMultiplicativeRecognition : Set where

chosenPolynomialDoesNotBecomeCanonical :
  ChosenPolynomialImpliesCanonicalFieldStructure → ⊥
chosenPolynomialDoesNotBecomeCanonical ()

c2SeamDoesNotPayFullRecognition :
  C2NegationIntertwiningImpliesFullMultiplicativeRecognition → ⊥
c2SeamDoesNotPayFullRecognition ()

record TriadicKernelFieldRecognitionBoundary : Set where
  constructor triadic-kernel-field-recognition-boundary
  field
    k4CoordinateFieldModelRuntimeVerified : Bool
    k5CoordinateFieldModelRuntimeVerified : Bool
    k6CoordinateFieldModelRuntimeVerified : Bool
    existingNegationWeldedToMinusOneScalar : Bool
    k4PunctureCyclic80RuntimeVerified : Bool
    rowMajor12VectorHypothesisSurvives : Bool
    canonicalFieldMultiplicationRecoveredFromPriorRepo : Bool
    fullFiniteFieldRecognitionClosed : Bool

canonicalTriadicKernelFieldRecognitionBoundary :
  TriadicKernelFieldRecognitionBoundary
canonicalTriadicKernelFieldRecognitionBoundary =
  triadic-kernel-field-recognition-boundary
    true true true true true
    false false false
