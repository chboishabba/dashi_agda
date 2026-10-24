module DASHI.Mathematics.Topology.ExoticBinaryTernaryPantsCodecExact where

------------------------------------------------------------------------
-- MAXIMAL PRIOR-ART REUSE: classical prefix-free variable-length code
--  3 ↦ 0, 6 ↦ 10, 9 ↦ 11.
--
-- Imports actual DASHI ternary-pants frontier, its 369 address carrier,
-- and the original exact Cantor-cylinder representation. The codec
-- identifies finite ternary address WORDS with uniquely decodable binary
-- words, NOT their literal cylinder depths or equal cylinder masses.
--
-- Source: classical prefix-free instantaneous coding / Kraft theory.
-- Infinite-stream product-topology homeomorphism and any 2D pants
-- embedding require additional continuity / realisation theorems.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Data.Vec.Base using (toList)

import DASHI.Geometry.SSP369Ultrametric as U369
import DASHI.Topology.TernaryPantsFrontierExact as Pants
import DASHI.Foundations.CantorProjectiveCylinderMeasureExact as Cantor

encode : List U369.Digit369 → List Bool
encode [] = []
encode (U369.digit3 ∷ xs) = false ∷ encode xs
encode (U369.digit6 ∷ xs) = true ∷ false ∷ encode xs
encode (U369.digit9 ∷ xs) = true ∷ true ∷ encode xs

prependDecoded :
  U369.Digit369 → Maybe (List U369.Digit369) →
  Maybe (List U369.Digit369)
prependDecoded _ nothing = nothing
prependDecoded digit (just xs) = just (digit ∷ xs)

decode : List Bool → Maybe (List U369.Digit369)
decode [] = just []
decode (false ∷ xs) = prependDecoded U369.digit3 (decode xs)
decode (true ∷ []) = nothing
decode (true ∷ false ∷ xs) =
  prependDecoded U369.digit6 (decode xs)
decode (true ∷ true ∷ xs) =
  prependDecoded U369.digit9 (decode xs)

decodeEncode :
  (digits : List U369.Digit369) →
  decode (encode digits) ≡ just digits
decodeEncode [] = refl
decodeEncode (U369.digit3 ∷ xs)
  rewrite decodeEncode xs = refl
decodeEncode (U369.digit6 ∷ xs)
  rewrite decodeEncode xs = refl
decodeEncode (U369.digit9 ∷ xs)
  rewrite decodeEncode xs = refl

-- The unfinished binary suffix is NOT silently a completed address.
unfinishedPrefixRejected : decode (true ∷ []) ≡ nothing
unfinishedPrefixRejected = refl

-- Reuse the existing PANTS path-to-address theorem as source, not a
-- duplicate ternary path representation.
pantsPathToBinaryWord :
  ∀ {n} → Pants.PantsPath n → List Bool
pantsPathToBinaryWord path =
  encode (toList (Pants.pantsPathToAddress path))

pantsPathBinaryDecodes :
  ∀ {n} (path : Pants.PantsPath n) →
  decode (pantsPathToBinaryWord path)
  ≡ just (toList (Pants.pantsPathToAddress path))
pantsPathBinaryDecodes path =
  decodeEncode (toList (Pants.pantsPathToAddress path))

-- These words inhabit the ORIGINAL Cantor cylinder carrier;
-- no false claim that n ternary symbols always become n binary bits.
pantsPathCylinder :
  ∀ {n} → Pants.PantsPath n → Cantor.Cylinder
pantsPathCylinder path =
  Cantor.cylinder (pantsPathToBinaryWord path)

sampleThree : List U369.Digit369
sampleThree =
  U369.digit3 ∷ U369.digit6 ∷ U369.digit9 ∷ []

sampleExactCode :
  encode sampleThree ≡
    false ∷ true ∷ false ∷ true ∷ true ∷ []
sampleExactCode = refl

sampleDecoded : decode (encode sampleThree) ≡ just sampleThree
sampleDecoded = decodeEncode sampleThree
