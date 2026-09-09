module DASHI.ComputerScience.BinaryBalancedTernarySubcarrierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.BalancedTernaryAntipodalOrbitExact as Orbit
import DASHI.ComputerScience.TemporalStorageFibreExact as Storage

------------------------------------------------------------------------
-- BINARY AS AN EXACT SUBCARRIER OF BALANCED TERNARY
--
-- This is not base conversion and does not claim binary and ternary carriers
-- are identical.  A bit is embedded into the strict non-zero antipodal fibre:
--
--   false -> -1
--   true  -> +1
--
-- The balanced centre 0 remains outside the image.  A total decoder chooses a
-- value on the unused centre, while decode(embed(bit)) is exact.
------------------------------------------------------------------------

embedBit : Bool → SSP.SSPTrit
embedBit false = SSP.sspNegOne
embedBit true = SSP.sspPosOne

decodeEmbeddedBit : SSP.SSPTrit → Bool
decodeEmbeddedBit SSP.sspNegOne = false
decodeEmbeddedBit SSP.sspZero = false
decodeEmbeddedBit SSP.sspPosOne = true

binaryTernaryRoundTrip :
  (bit : Bool) →
  decodeEmbeddedBit (embedBit bit) ≡ bit
binaryTernaryRoundTrip false = refl
binaryTernaryRoundTrip true = refl

centreIsUnusedByBinaryEmbedding :
  (bit : Bool) →
  embedBit bit ≡ SSP.sspZero →
  ⊥
centreIsUnusedByBinaryEmbedding false ()
centreIsUnusedByBinaryEmbedding true ()

binaryEmbeddingPreservesBooleanComplementAsAntipode :
  (bit : Bool) →
  embedBit (not bit) ≡ Orbit.strictAntipode (embedBit bit)
binaryEmbeddingPreservesBooleanComplementAsAntipode false = refl
binaryEmbeddingPreservesBooleanComplementAsAntipode true = refl

------------------------------------------------------------------------
-- Exact stream embedding.  Leading zeros are preserved because this is a
-- structural digit embedding rather than integer-value base conversion.
------------------------------------------------------------------------

embedBits : List Bool → List SSP.SSPTrit
embedBits [] = []
embedBits (bit ∷ bits) = embedBit bit ∷ embedBits bits

decodeEmbeddedBits : List SSP.SSPTrit → List Bool
decodeEmbeddedBits [] = []
decodeEmbeddedBits (trit ∷ trits) =
  decodeEmbeddedBit trit ∷ decodeEmbeddedBits trits

binaryTernaryStreamRoundTrip :
  (bits : List Bool) →
  decodeEmbeddedBits (embedBits bits) ≡ bits
binaryTernaryStreamRoundTrip [] = refl
binaryTernaryStreamRoundTrip (false ∷ bits)
  rewrite binaryTernaryStreamRoundTrip bits = refl
binaryTernaryStreamRoundTrip (true ∷ bits)
  rewrite binaryTernaryStreamRoundTrip bits = refl

------------------------------------------------------------------------
-- Same bridge as a storage representation fibre.
------------------------------------------------------------------------

binaryInBalancedTernaryRepresentation :
  Storage.CellRepresentationFibre Bool
binaryInBalancedTernaryRepresentation =
  Storage.cellRepresentationFibre
    SSP.SSPTrit
    embedBit
    decodeEmbeddedBit
    binaryTernaryRoundTrip

------------------------------------------------------------------------
-- Reuse the repository's exact antipodal orbit counts rather than introducing
-- another signed decomposition.
------------------------------------------------------------------------

nineCarrierSignedOrbitCount : 9 ≡ 1 + 4 * 2
nineCarrierSignedOrbitCount =
  Orbit.nineDecomposesAsCentrePlusFourPairs

twentySevenCarrierSignedOrbitCount : 27 ≡ 1 + 13 * 2
twentySevenCarrierSignedOrbitCount =
  Orbit.ternaryCubeCountDecomposesAsCentrePlusThirteenPairs

record BinaryBalancedTernarySubcarrierBoundary : Set where
  constructor binaryBalancedTernarySubcarrierBoundary
  field
    binaryEmbedsInjectivelyIntoNonzeroTernaryFibre : Bool
    centreUsedByBinaryImage : Bool
    leadingZerosPreservedByStreamEmbedding : Bool
    binaryCarrierEqualsBalancedTernaryCarrier : Bool
    complementMatchesStrictAntipodeOnImage : Bool

canonicalBinaryBalancedTernarySubcarrierBoundary :
  BinaryBalancedTernarySubcarrierBoundary
canonicalBinaryBalancedTernarySubcarrierBoundary =
  binaryBalancedTernarySubcarrierBoundary true false true false true
