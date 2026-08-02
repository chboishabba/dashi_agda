module DASHI.Foundations.TernaryGolay.TernaryGolayWeightEnumerator where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base using (_+_)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.TernaryGolay.ExplicitCode729 as Explicit
import DASHI.Foundations.TernaryGolay.SourceAtlas as Sources

------------------------------------------------------------------------
-- Exact Hamming weight enumerator of the constructed [12,6,6]_3 code.
--
-- The coefficients below are not merely copied from the literature: they are
-- re-exported from the exhaustive 729-word computation in ExplicitCode729.
-- The Gleason/MacWilliams sources explain why the same polynomial is forced for
-- an extremal Type III code; that theorem route remains separately attributed.
------------------------------------------------------------------------

record WeightEnumerator12 : Set where
  constructor weightEnumerator12
  field
    coefficient0 : Nat
    coefficient1 : Nat
    coefficient2 : Nat
    coefficient3 : Nat
    coefficient4 : Nat
    coefficient5 : Nat
    coefficient6 : Nat
    coefficient7 : Nat
    coefficient8 : Nat
    coefficient9 : Nat
    coefficient10 : Nat
    coefficient11 : Nat
    coefficient12 : Nat

open WeightEnumerator12 public

ternaryGolayWeightEnumerator : WeightEnumerator12
ternaryGolayWeightEnumerator =
  weightEnumerator12
    1 0 0 0 0 0 264 0 0 440 0 0 24

coefficient0Computed :
  Explicit.countWeight 0 Explicit.allCodewords
  ≡ coefficient0 ternaryGolayWeightEnumerator
coefficient0Computed = Explicit.weight0Count

coefficient1Computed :
  Explicit.countWeight 1 Explicit.allCodewords
  ≡ coefficient1 ternaryGolayWeightEnumerator
coefficient1Computed = Explicit.weight1Count

coefficient2Computed :
  Explicit.countWeight 2 Explicit.allCodewords
  ≡ coefficient2 ternaryGolayWeightEnumerator
coefficient2Computed = Explicit.weight2Count

coefficient3Computed :
  Explicit.countWeight 3 Explicit.allCodewords
  ≡ coefficient3 ternaryGolayWeightEnumerator
coefficient3Computed = Explicit.weight3Count

coefficient4Computed :
  Explicit.countWeight 4 Explicit.allCodewords
  ≡ coefficient4 ternaryGolayWeightEnumerator
coefficient4Computed = Explicit.weight4Count

coefficient5Computed :
  Explicit.countWeight 5 Explicit.allCodewords
  ≡ coefficient5 ternaryGolayWeightEnumerator
coefficient5Computed = Explicit.weight5Count

coefficient6Computed :
  Explicit.countWeight 6 Explicit.allCodewords
  ≡ coefficient6 ternaryGolayWeightEnumerator
coefficient6Computed = Explicit.weight6Count

coefficient7Computed :
  Explicit.countWeight 7 Explicit.allCodewords
  ≡ coefficient7 ternaryGolayWeightEnumerator
coefficient7Computed = Explicit.weight7Count

coefficient8Computed :
  Explicit.countWeight 8 Explicit.allCodewords
  ≡ coefficient8 ternaryGolayWeightEnumerator
coefficient8Computed = Explicit.weight8Count

coefficient9Computed :
  Explicit.countWeight 9 Explicit.allCodewords
  ≡ coefficient9 ternaryGolayWeightEnumerator
coefficient9Computed = Explicit.weight9Count

coefficient10Computed :
  Explicit.countWeight 10 Explicit.allCodewords
  ≡ coefficient10 ternaryGolayWeightEnumerator
coefficient10Computed = Explicit.weight10Count

coefficient11Computed :
  Explicit.countWeight 11 Explicit.allCodewords
  ≡ coefficient11 ternaryGolayWeightEnumerator
coefficient11Computed = Explicit.weight11Count

coefficient12Computed :
  Explicit.countWeight 12 Explicit.allCodewords
  ≡ coefficient12 ternaryGolayWeightEnumerator
coefficient12Computed = Explicit.weight12Count

enumeratorCoefficientSum :
  coefficient0 ternaryGolayWeightEnumerator +
  coefficient6 ternaryGolayWeightEnumerator +
  coefficient9 ternaryGolayWeightEnumerator +
  coefficient12 ternaryGolayWeightEnumerator
  ≡ 729
enumeratorCoefficientSum = refl

data Monomial12 : Set where
  X12 : Monomial12
  X6Y6 : Monomial12
  X3Y9 : Monomial12
  Y12 : Monomial12

record SparseWeightTerm : Set where
  constructor sparseWeightTerm
  field
    monomial : Monomial12
    termCoefficient : Nat

open SparseWeightTerm public

sparseWeightPolynomial : List SparseWeightTerm
sparseWeightPolynomial =
  sparseWeightTerm X12 1
  ∷ sparseWeightTerm X6Y6 264
  ∷ sparseWeightTerm X3Y9 440
  ∷ sparseWeightTerm Y12 24
  ∷ []

record TypeIIIGleasonCalibration : Set where
  constructor typeIIIGleasonCalibration
  field
    author : String
    title : String
    doi : String
    sourceURL : String
    theoremImportedAsKernelProofHere : Bool
    theoremImportedAsKernelProofHereIsFalse :
      theoremImportedAsKernelProofHere ≡ false
    localEnumeratorObtainedByExhaustion : Bool
    localEnumeratorObtainedByExhaustionIsTrue :
      localEnumeratorObtainedByExhaustion ≡ true
    reading : String

canonicalTypeIIIGleasonCalibration : TypeIIIGleasonCalibration
canonicalTypeIIIGleasonCalibration =
  typeIIIGleasonCalibration
    (Sources.author Sources.macWilliamsMallowsSloaneGleasonEntry)
    (Sources.title Sources.macWilliamsMallowsSloaneGleasonEntry)
    "10.1109/TIT.1972.1054898"
    (Sources.canonicalURL Sources.macWilliamsMallowsSloaneGleasonEntry)
    false refl
    true refl
    "Gleason invariant theory explains why an extremal Type III length-12 self-dual code has this enumerator; this module independently computes every coefficient from all 729 messages"

weightEnumeratorGenericReceipt : GenericReceipt.GenericReceipt
weightEnumeratorGenericReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "ternary Golay exact weight enumerator"
    "DASHI.Foundations.TernaryGolay.TernaryGolayWeightEnumerator"
    "ternaryGolayWeightEnumerator"
    "the exact polynomial X^12 + 264 X^6Y^6 + 440 X^3Y^9 + 24 Y^12 is backed by the exhaustive explicit-code computation and cross-calibrated against the attributed Type III Gleason theorem"
    "the citation explains uniqueness of the invariant polynomial but is not substituted for the local finite calculation"
    "agda -i . DASHI/Foundations/TernaryGolay/TernaryGolayWeightEnumerator.agda"

weightEnumeratorGenericReceiptNonPromoting :
  GenericReceipt.promotesClaim weightEnumeratorGenericReceipt ≡ false
weightEnumeratorGenericReceiptNonPromoting =
  GenericReceipt.promotesClaimIsFalse weightEnumeratorGenericReceipt
