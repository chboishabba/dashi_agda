module DASHI.Foundations.TernaryGolay.MathieuExceptionalBridgeBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.TernaryGolay.SourceAtlas as Sources

------------------------------------------------------------------------
-- Correct binary/ternary exceptional bridges.
--
-- 1. A trio is a partition of the 24 coordinates into three disjoint octads.
--    The single-orbit and stabilizer theorem is exposed through an explicit
--    M24 action receipt; arbitrary 8+8+8 partitions are not promoted to trios.
-- 2. A dodecad and its complement supply the 12-point Mathieu lane through a
--    stabilizer interface.
-- 3. Weight-six ternary Golay supports supply the small-Witt hexad lane through
--    an explicit support-identification receipt.
------------------------------------------------------------------------

m24Order : Nat
m24Order = 244823040

m12Order : Nat
m12Order = 95040

trioStabilizerOrder : Nat
trioStabilizerOrder = 64512

trioCount : Nat
trioCount = 3795

trioOrbitArithmetic : trioStabilizerOrder * trioCount ≡ m24Order
trioOrbitArithmetic = refl

hexadCount : Nat
hexadCount = 132

dodecadCount : Nat
dodecadCount = 2576

data EightEightEightStatus : Set where
  arbitraryEqualPartition : EightEightEightStatus
  golayOctadTrio : EightEightEightStatus

record GolayTrioOrbitTheorem
    (M24 Coordinate Octad Trio : Set) : Set₁ where
  field
    actsOnCoordinate : M24 → Coordinate → Coordinate
    trioBlocks : Trio → Octad → Set
    trioIsThreeDisjointOctads : Set
    actionOnTrios : M24 → Trio → Trio
    transitiveOnTrios : Set
    transitivityWitness : transitiveOnTrios
    stabilizerHasOrder64512 : Set
    stabilizerOrderWitness : stabilizerHasOrder64512
    stabilizerContainsS3BlockPermutation : Set
    s3FactorWitness : stabilizerContainsS3BlockPermutation
    orbitHas3795Trios : Set
    orbitCountWitness : orbitHas3795Trios
    sourceAuthor : String
    sourceTitle : String
    sourceDOI : String

open GolayTrioOrbitTheorem public

record EquivariantTrioObservable
    (M24 Trio Value : Set) : Set₁ where
  field
    actionOnTrios : M24 → Trio → Trio
    actionOnValues : M24 → Value → Value
    observable : Trio → Value
    equivariant :
      (g : M24) →
      (trio : Trio) →
      observable (actionOnTrios g trio)
      ≡ actionOnValues g (observable trio)

open EquivariantTrioObservable public

record DodecadM12EmbeddingTheorem
    (M24 M12 Octad Dodecad : Set) : Set₁ where
  field
    firstOctad : Octad
    secondOctad : Octad
    intersectionHasSizeTwo : Set
    symmetricDifference : Octad → Octad → Dodecad
    selectedDodecad : Dodecad
    selectedDodecadIsSymmetricDifference :
      selectedDodecad ≡ symmetricDifference firstOctad secondOctad
    complementDodecad : Dodecad
    pairStabilizer : Set
    pairStabilizerIsM12Dot2 : Set
    pointwiseDodecadStabilizerIsM12 : Set
    outerAutomorphismSwapsComplementPair : Set
    embeddingReceipt : M12 → M24
    sourceAuthor : String
    sourceTitle : String
    sourceDOI : String

open DodecadM12EmbeddingTheorem public

record HexadTernaryGolaySupportTheorem
    (Codeword Hexad M12 : Set) : Set₁ where
  field
    weight : Codeword → Nat
    support : Codeword → Hexad
    weightSix : Codeword → Set
    supportOfWeightSixIsHexad :
      (word : Codeword) → weightSix word → Set
    everyHexadIsWeightSixSupport : Set
    hexadCountIs132 : Set
    m12ActsOnHexads : M12 → Hexad → Hexad
    m12PreservesHexads : Set
    theoremReceipt :
      everyHexadIsWeightSixSupport →
      hexadCountIs132 →
      m12PreservesHexads →
      Set
    sourceAuthor : String
    sourceTitle : String
    sourceDOI : String

open HexadTernaryGolaySupportTheorem public

record MonomialAutomorphismExtensionTheorem
    (MonomialAut M12 Kernel : Set) : Set₁ where
  field
    projection : MonomialAut → M12
    kernel : Kernel
    kernelOrder : Nat
    kernelOrderIsTwo : kernelOrder ≡ 2
    projectionSurjective : Set
    exactSequenceReceipt : Set

open MonomialAutomorphismExtensionTheorem public

record MathieuBridgeStatus : Set where
  constructor mathieuBridgeStatus
  field
    arbitraryPartitionIsTrio : Bool
    arbitraryPartitionIsTrioIsFalse : arbitraryPartitionIsTrio ≡ false
    trioOrbitTheoremImportedHere : Bool
    trioOrbitTheoremImportedHereIsFalse : trioOrbitTheoremImportedHere ≡ false
    dodecadEmbeddingTheoremImportedHere : Bool
    dodecadEmbeddingTheoremImportedHereIsFalse :
      dodecadEmbeddingTheoremImportedHere ≡ false
    hexadSupportTheoremImportedHere : Bool
    hexadSupportTheoremImportedHereIsFalse :
      hexadSupportTheoremImportedHere ≡ false
    numericOrbitArithmeticChecked : Bool
    numericOrbitArithmeticCheckedIsTrue : numericOrbitArithmeticChecked ≡ true
    reading : String

canonicalMathieuBridgeStatus : MathieuBridgeStatus
canonicalMathieuBridgeStatus =
  mathieuBridgeStatus
    false refl
    false refl
    false refl
    false refl
    true refl
    "trio, dodecad-stabilizer, and ternary-hexad theorems are named interfaces; only the finite order/index arithmetic is closed locally"

mathieuExceptionalBridgeReceipt : GenericReceipt.GenericReceipt
mathieuExceptionalBridgeReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "Mathieu binary/ternary exceptional bridge"
    "DASHI.Foundations.TernaryGolay.MathieuExceptionalBridgeBoundary"
    "canonicalMathieuBridgeStatus"
    "trio orbit, equivariant observable, dodecad M12 embedding, hexad support, and 2.M12 monomial-extension interfaces are attached with finite order arithmetic"
    "external action, stabilizer, support-design, and exact-sequence theorems require explicit imports from the named sources"
    "agda -i . DASHI/Foundations/TernaryGolay/MathieuExceptionalBridgeBoundary.agda"

mathieuExceptionalBridgeReceiptNonPromoting :
  GenericReceipt.promotesClaim mathieuExceptionalBridgeReceipt ≡ false
mathieuExceptionalBridgeReceiptNonPromoting =
  GenericReceipt.promotesClaimIsFalse mathieuExceptionalBridgeReceipt
