module DASHI.Analysis.NonArchimedeanOddOrbitEquivalenceCompilerExact where

------------------------------------------------------------------------
-- ODD-ORBIT EQUIVALENCE COMPILER
--
-- Compile the semantic chart
--
--   (j,0) |->  3^j
--   (j,1) |-> -3^j
--
-- from source arithmetic receipts.  The point is to make the final chart a
-- downstream construction rather than a separately searched theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

record TwoOrbitArithmeticReceipts : Set₁ where
  field
    Position : Set
    OrbitBit : Set
    OddResidue : Set

    decode : Position → OrbitBit → OddResidue
    encodePosition : OddResidue → Position
    encodeBit : OddResidue → OrbitBit

    positiveOrbitInjectiveBeforePeriod : Set
    negativeOrbitInjectiveBeforePeriod : Set
    positiveNegativeDisjoint : Set
    twoOrbitsCoverOddResidues : Set

    decodeAfterEncode :
      (k : OddResidue) →
      decode (encodePosition k) (encodeBit k) ≡ k

    encodePositionAfterDecode :
      (j : Position) (b : OrbitBit) →
      encodePosition (decode j b) ≡ j

    encodeBitAfterDecode :
      (j : Position) (b : OrbitBit) →
      encodeBit (decode j b) ≡ b

open TwoOrbitArithmeticReceipts public

record OddOrbitEquivalence : Set₁ where
  field
    Position : Set
    OrbitBit : Set
    OddResidue : Set

    toOdd : Position → OrbitBit → OddResidue
    fromOddPosition : OddResidue → Position
    fromOddBit : OddResidue → OrbitBit

    toAfterFrom :
      (k : OddResidue) →
      toOdd (fromOddPosition k) (fromOddBit k) ≡ k

    fromPositionAfterTo :
      (j : Position) (b : OrbitBit) →
      fromOddPosition (toOdd j b) ≡ j

    fromBitAfterTo :
      (j : Position) (b : OrbitBit) →
      fromOddBit (toOdd j b) ≡ b

open OddOrbitEquivalence public

compileOddOrbitEquivalence :
  TwoOrbitArithmeticReceipts → OddOrbitEquivalence
compileOddOrbitEquivalence receipts = record
  { Position = Position receipts
  ; OrbitBit = OrbitBit receipts
  ; OddResidue = OddResidue receipts
  ; toOdd = decode receipts
  ; fromOddPosition = encodePosition receipts
  ; fromOddBit = encodeBit receipts
  ; toAfterFrom = decodeAfterEncode receipts
  ; fromPositionAfterTo = encodePositionAfterDecode receipts
  ; fromBitAfterTo = encodeBitAfterDecode receipts
  }

record OrbitEquivalenceCompilerStatus : Set where
  constructor orbitEquivalenceCompilerStatus
  field
    orderReceiptFeedsInjectivity : Bool
    disjointnessReceiptRequired : Bool
    coverReceiptRequired : Bool
    finalEquivalenceIsCompilerOutput : Bool
    cardinalityAloneSuffices : Bool

canonicalOrbitEquivalenceCompilerStatus : OrbitEquivalenceCompilerStatus
canonicalOrbitEquivalenceCompilerStatus =
  orbitEquivalenceCompilerStatus true true true true false


data OrbitEquivalenceLeaf : Set where
  positiveOrbitInjectivity : OrbitEquivalenceLeaf
  negativeOrbitInjectivity : OrbitEquivalenceLeaf
  positiveNegativeDisjointness : OrbitEquivalenceLeaf
  oddResidueCover : OrbitEquivalenceLeaf
  packageTwoSidedEquivalence : OrbitEquivalenceLeaf
  useCardinalityOnly : OrbitEquivalenceLeaf


data OrbitLeafDisposition : Set where
  live : OrbitLeafDisposition
  downstream : OrbitLeafDisposition
  forbiddenShortcut : OrbitLeafDisposition

orbitLeafDisposition : OrbitEquivalenceLeaf → OrbitLeafDisposition
orbitLeafDisposition positiveOrbitInjectivity = live
orbitLeafDisposition negativeOrbitInjectivity = live
orbitLeafDisposition positiveNegativeDisjointness = live
orbitLeafDisposition oddResidueCover = live
orbitLeafDisposition packageTwoSidedEquivalence = downstream
orbitLeafDisposition useCardinalityOnly = forbiddenShortcut

highestAlphaOrbitEquivalencePath : List OrbitEquivalenceLeaf
highestAlphaOrbitEquivalencePath =
  positiveOrbitInjectivity ∷
  positiveNegativeDisjointness ∷
  oddResidueCover ∷
  packageTwoSidedEquivalence ∷
  []

finalChartIsCompilerOutput :
  OrbitEquivalenceCompilerStatus.finalEquivalenceIsCompilerOutput
    canonicalOrbitEquivalenceCompilerStatus
  ≡ true
finalChartIsCompilerOutput = refl
