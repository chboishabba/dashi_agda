module DASHI.ComputerScience.BinaryThreeBitTwoTritAntipodalCodecExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.BalancedTernaryAntipodalOrbitExact as Orbit

data Bit3 : Set where
  bits3 : Bool → Bool → Bool → Bit3

data Trit2 : Set where
  trits2 : SSP.SSPTrit → SSP.SSPTrit → Trit2

boolComplement : Bool → Bool
boolComplement false = true
boolComplement true = false

complementBit3 : Bit3 → Bit3
complementBit3 (bits3 a b c) = bits3 (boolComplement a) (boolComplement b) (boolComplement c)

antipodeTrit2 : Trit2 → Trit2
antipodeTrit2 (trits2 a b) = trits2 (Orbit.strictAntipode a) (Orbit.strictAntipode b)

encode3to2 : Bit3 → Trit2
encode3to2 (bits3 false false false) = trits2 SSP.sspNegOne SSP.sspNegOne
encode3to2 (bits3 false false true) = trits2 SSP.sspNegOne SSP.sspZero
encode3to2 (bits3 false true false) = trits2 SSP.sspNegOne SSP.sspPosOne
encode3to2 (bits3 false true true) = trits2 SSP.sspZero SSP.sspNegOne
encode3to2 (bits3 true false false) = trits2 SSP.sspZero SSP.sspPosOne
encode3to2 (bits3 true false true) = trits2 SSP.sspPosOne SSP.sspNegOne
encode3to2 (bits3 true true false) = trits2 SSP.sspPosOne SSP.sspZero
encode3to2 (bits3 true true true) = trits2 SSP.sspPosOne SSP.sspPosOne

decode2to3 : Trit2 → Bit3
decode2to3 (trits2 SSP.sspNegOne SSP.sspNegOne) = bits3 false false false
decode2to3 (trits2 SSP.sspNegOne SSP.sspZero) = bits3 false false true
decode2to3 (trits2 SSP.sspNegOne SSP.sspPosOne) = bits3 false true false
decode2to3 (trits2 SSP.sspZero SSP.sspNegOne) = bits3 false true true
decode2to3 (trits2 SSP.sspZero SSP.sspZero) = bits3 false false false
decode2to3 (trits2 SSP.sspZero SSP.sspPosOne) = bits3 true false false
decode2to3 (trits2 SSP.sspPosOne SSP.sspNegOne) = bits3 true false true
decode2to3 (trits2 SSP.sspPosOne SSP.sspZero) = bits3 true true false
decode2to3 (trits2 SSP.sspPosOne SSP.sspPosOne) = bits3 true true true

blockRoundTrip : (block : Bit3) → decode2to3 (encode3to2 block) ≡ block
blockRoundTrip (bits3 false false false) = refl
blockRoundTrip (bits3 false false true) = refl
blockRoundTrip (bits3 false true false) = refl
blockRoundTrip (bits3 false true true) = refl
blockRoundTrip (bits3 true false false) = refl
blockRoundTrip (bits3 true false true) = refl
blockRoundTrip (bits3 true true false) = refl
blockRoundTrip (bits3 true true true) = refl

centre2 : Trit2
centre2 = trits2 SSP.sspZero SSP.sspZero

centreUnused : (block : Bit3) → encode3to2 block ≡ centre2 → ⊥
centreUnused (bits3 false false false) ()
centreUnused (bits3 false false true) ()
centreUnused (bits3 false true false) ()
centreUnused (bits3 false true true) ()
centreUnused (bits3 true false false) ()
centreUnused (bits3 true false true) ()
centreUnused (bits3 true true false) ()
centreUnused (bits3 true true true) ()

complementAntipodeEquivariant :
  (block : Bit3) → encode3to2 (complementBit3 block) ≡ antipodeTrit2 (encode3to2 block)
complementAntipodeEquivariant (bits3 false false false) = refl
complementAntipodeEquivariant (bits3 false false true) = refl
complementAntipodeEquivariant (bits3 false true false) = refl
complementAntipodeEquivariant (bits3 false true true) = refl
complementAntipodeEquivariant (bits3 true false false) = refl
complementAntipodeEquivariant (bits3 true false true) = refl
complementAntipodeEquivariant (bits3 true true false) = refl
complementAntipodeEquivariant (bits3 true true true) = refl

encodeBlockStream : List Bit3 → List Trit2
encodeBlockStream [] = []
encodeBlockStream (block ∷ blocks) = encode3to2 block ∷ encodeBlockStream blocks

decodeBlockStream : List Trit2 → List Bit3
decodeBlockStream [] = []
decodeBlockStream (block ∷ blocks) = decode2to3 block ∷ decodeBlockStream blocks

blockStreamRoundTrip : (blocks : List Bit3) → decodeBlockStream (encodeBlockStream blocks) ≡ blocks
blockStreamRoundTrip [] = refl
blockStreamRoundTrip (block ∷ blocks)
  rewrite blockRoundTrip block | blockStreamRoundTrip blocks = refl

complementBlockStream : List Bit3 → List Bit3
complementBlockStream [] = []
complementBlockStream (block ∷ blocks) = complementBit3 block ∷ complementBlockStream blocks

antipodeTritStream : List Trit2 → List Trit2
antipodeTritStream [] = []
antipodeTritStream (block ∷ blocks) = antipodeTrit2 block ∷ antipodeTritStream blocks

blockStreamComplementAntipodeEquivariant :
  (blocks : List Bit3) → encodeBlockStream (complementBlockStream blocks) ≡ antipodeTritStream (encodeBlockStream blocks)
blockStreamComplementAntipodeEquivariant [] = refl
blockStreamComplementAntipodeEquivariant (block ∷ blocks)
  rewrite complementAntipodeEquivariant block | blockStreamComplementAntipodeEquivariant blocks = refl

ternaryPairOrbitDecomposition : 9 ≡ 1 + 4 * 2
ternaryPairOrbitDecomposition = Orbit.nineDecomposesAsCentrePlusFourPairs

record BinaryThreeBitTwoTritBoundary : Set where
  constructor binaryThreeBitTwoTritBoundary
  field
    allEightBinaryBlocksRecoverExactly : Bool
    ternaryCentreUnused : Bool
    complementAndAntipodeCommute : Bool
    blockStreamsRecoverExactly : Bool
    wordFramingIsSeparateCoordinate : Bool
    codeIsIntegerBaseConversion : Bool
    binaryAndTernaryCarriersIdentified : Bool

canonicalBinaryThreeBitTwoTritBoundary : BinaryThreeBitTwoTritBoundary
canonicalBinaryThreeBitTwoTritBoundary =
  binaryThreeBitTwoTritBoundary true true true true true false false
