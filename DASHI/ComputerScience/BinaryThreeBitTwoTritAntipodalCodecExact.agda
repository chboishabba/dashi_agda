module DASHI.ComputerScience.BinaryThreeBitTwoTritAntipodalCodecExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.BalancedTernaryAntipodalOrbitExact as Orbit

------------------------------------------------------------------------
-- 3 BITS <-> 2 BALANCED TRITS ON THE NON-CENTRE FIBRE
--
-- 2^3 = 8 and 3^2 = 9 = 1 + 4*2.
--
-- The eight binary blocks split into four Boolean-complement pairs.  The nine
-- balanced-ternary pairs split into one fixed centre plus four strict-antipodal
-- pairs.  We therefore identify those pair structures exactly, leaving only
-- the ternary centre unused.
------------------------------------------------------------------------

data Bit3 : Set where
  bits3 : Bool → Bool → Bool → Bit3

data Trit2 : Set where
  trits2 : SSP.SSPTrit → SSP.SSPTrit → Trit2

boolComplement : Bool → Bool
boolComplement false = true
boolComplement true = false

complementBit3 : Bit3 → Bit3
complementBit3 (bits3 a b c) =
  bits3 (boolComplement a) (boolComplement b) (boolComplement c)

antipodeTrit2 : Trit2 → Trit2
antipodeTrit2 (trits2 a b) =
  trits2 (Orbit.strictAntipode a) (Orbit.strictAntipode b)

------------------------------------------------------------------------
-- One representative from each complement pair is sent to one representative
-- from each non-centre antipodal pair; its complement is sent to the antipode.
------------------------------------------------------------------------

encode3to2 : Bit3 → Trit2
encode3to2 (bits3 false false false) =
  trits2 SSP.sspNegOne SSP.sspNegOne
encode3to2 (bits3 false false true) =
  trits2 SSP.sspNegOne SSP.sspZero
encode3to2 (bits3 false true false) =
  trits2 SSP.sspNegOne SSP.sspPosOne
encode3to2 (bits3 false true true) =
  trits2 SSP.sspZero SSP.sspNegOne
encode3to2 (bits3 true false false) =
  trits2 SSP.sspZero SSP.sspPosOne
encode3to2 (bits3 true false true) =
  trits2 SSP.sspPosOne SSP.sspNegOne
encode3to2 (bits3 true true false) =
  trits2 SSP.sspPosOne SSP.sspZero
encode3to2 (bits3 true true true) =
  trits2 SSP.sspPosOne SSP.sspPosOne

-- Total decoder.  The unused centre is assigned a default block; the theorem
-- below proves it is never reached by encode3to2.
decode2to3 : Trit2 → Bit3
decode2to3 (trits2 SSP.sspNegOne SSP.sspNegOne) =
  bits3 false false false
decode2to3 (trits2 SSP.sspNegOne SSP.sspZero) =
  bits3 false false true
decode2to3 (trits2 SSP.sspNegOne SSP.sspPosOne) =
  bits3 false true false
decode2to3 (trits2 SSP.sspZero SSP.sspNegOne) =
  bits3 false true true
decode2to3 (trits2 SSP.sspZero SSP.sspZero) =
  bits3 false false false
decode2to3 (trits2 SSP.sspZero SSP.sspPosOne) =
  bits3 true false false
decode2to3 (trits2 SSP.sspPosOne SSP.sspNegOne) =
  bits3 true false true
decode2to3 (trits2 SSP.sspPosOne SSP.sspZero) =
  bits3 true true false
decode2to3 (trits2 SSP.sspPosOne SSP.sspPosOne) =
  bits3 true true true

blockRoundTrip :
  (block : Bit3) →
  decode2to3 (encode3to2 block) ≡ block
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

centreUnused :
  (block : Bit3) →
  encode3to2 block ≡ centre2 →
  ⊥
centreUnused (bits3 false false false) ()
centreUnused (bits3 false false true) ()
centreUnused (bits3 false true false) ()
centreUnused (bits3 false true true) ()
centreUnused (bits3 true false false) ()
centreUnused (bits3 true false true) ()
centreUnused (bits3 true true false) ()
centreUnused (bits3 true true true) ()

complementAntipodeEquivariant :
  (block : Bit3) →
  encode3to2 (complementBit3 block)
  ≡ antipodeTrit2 (encode3to2 block)
complementAntipodeEquivariant (bits3 false false false) = refl
complementAntipodeEquivariant (bits3 false false true) = refl
complementAntipodeEquivariant (bits3 false true false) = refl
complementAntipodeEquivariant (bits3 false true true) = refl
complementAntipodeEquivariant (bits3 true false false) = refl
complementAntipodeEquivariant (bits3 true false true) = refl
complementAntipodeEquivariant (bits3 true true false) = refl
complementAntipodeEquivariant (bits3 true true true) = refl

------------------------------------------------------------------------
-- Exact cardinal/orbit receipt from the canonical 369 owner.
------------------------------------------------------------------------

ternaryPairOrbitDecomposition : 9 ≡ 1 + 4 * 2
ternaryPairOrbitDecomposition =
  Orbit.nineDecomposesAsCentrePlusFourPairs

record BinaryThreeBitTwoTritBoundary : Set where
  constructor binaryThreeBitTwoTritBoundary
  field
    allEightBinaryBlocksRecoverExactly : Bool
    ternaryCentreUnused : Bool
    complementAndAntipodeCommute : Bool
    codeIsIntegerBaseConversion : Bool
    binaryAndTernaryCarriersIdentified : Bool

canonicalBinaryThreeBitTwoTritBoundary :
  BinaryThreeBitTwoTritBoundary
canonicalBinaryThreeBitTwoTritBoundary =
  binaryThreeBitTwoTritBoundary true true true false false
