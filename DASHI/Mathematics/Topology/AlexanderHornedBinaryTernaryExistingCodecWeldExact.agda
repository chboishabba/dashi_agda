module DASHI.Mathematics.Topology.AlexanderHornedBinaryTernaryExistingCodecWeldExact where

------------------------------------------------------------------------
-- THE EXISTING BINARY-IN-TERNARY AND TERNARY-IN-BINARY CODECS,
-- USED ON THE LITERAL HATCHER HORN CHILD ALPHABET.
--
-- SOURCE OWNERS:
--   ComputerScience.BinaryBalancedTernarySubcarrierExact
--   Codec.VerifiedFiniteTritCoder
--   Foundations.Base369BinaryTernaryRefinement
--   ComputerScience.BalancedTernaryC2C3DihedralCodecBridgeExact
--
-- No new numeric radix converter or identification Z2=Z3.
-- First map a horn Bit to a Boolean bit, then reuse the EXISTING
-- strict nonzero trit subcarrier; conversely use the existing
-- two-bit lossless code for ALL THREE trit symbols.
--
-- Different object types:
--  (a) injective symbolic alphabet codes,
--  (b) common 2^a*3^b finite refinement,
--  (c) additive topological group Z2 versus Z3.
-- (a),(b) do NOT imply a continuous group isomorphism (c).
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Maybe using (Maybe; just)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Mathematics.Topology.AlexanderHornedC3FiniteStageExact as H
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Algebra.Trit as Trit
import DASHI.ComputerScience.BinaryBalancedTernarySubcarrierExact as Binary
import DASHI.Codec.VerifiedFiniteTritCoder as Codes
import DASHI.Foundations.Base369BinaryTernaryRefinement as Refine
import DASHI.ComputerScience.BalancedTernaryC2C3DihedralCodecBridgeExact as Dihedral

asBool : H.Bit → Bool
asBool H.left = false
asBool H.right = true

asHornBit : Bool → H.Bit
asHornBit false = H.left
asHornBit true = H.right

hornBoolRoundTrip : ∀ b → asHornBit (asBool b) ≡ b
hornBoolRoundTrip H.left = refl
hornBoolRoundTrip H.right = refl

hornBitAsTrit : H.Bit → SSP.SSPTrit
hornBitAsTrit b = Binary.embedBit (asBool b)

tritAsHornBit : SSP.SSPTrit → H.Bit
tritAsHornBit t = asHornBit (Binary.decodeEmbeddedBit t)

hornBinaryInExistingBalancedTernaryRoundTrip :
  ∀ b → tritAsHornBit (hornBitAsTrit b) ≡ b
hornBinaryInExistingBalancedTernaryRoundTrip H.left = refl
hornBinaryInExistingBalancedTernaryRoundTrip H.right = refl

hornTritCentreExcluded :
  ∀ b → hornBitAsTrit b ≡ SSP.sspZero →
  ⊥
hornTritCentreExcluded H.left ()
hornTritCentreExcluded H.right ()

-- The inverse direction is not a bijection between single digits:
-- ALL THREE trits are losslessly encoded by TWO binary digits,
-- with the unused 11 codeword explicitly rejected in the owner.
allTritsViaExistingTwoBitCodec :
  ∀ t → Codes.decodeWord (Codes.encodeTrit t) ≡ just t
allTritsViaExistingTwoBitCodec = Codes.decode-encode

hornBitToExistingTwoBitTritCode :
  H.Bit → Codes.Word2
hornBitToExistingTwoBitTritCode b =
  Codes.encodeTrit (SSP.toTrit (hornBitAsTrit b))

hornCodeIsExact :
  ∀ b →
  Codes.decodeWord (hornBitToExistingTwoBitTritCode b)
    ≡ just (SSP.toTrit (hornBitAsTrit b))
hornCodeIsExact b =
  Codes.decode-encode (SSP.toTrit (hornBitAsTrit b))

-- The existing commuting refinement square is valid on resolution
-- counts 2^a*3^b, independent of the chosen binary/ternary codecs.
initialThreeSectorResolution : Refine.Resolution23
initialThreeSectorResolution = Refine.phase3Resolution

oneHornBinaryRefinementIsSix :
  Refine.binaryRefine initialThreeSectorResolution
    ≡ Refine.phase6Resolution
oneHornBinaryRefinementIsSix =
  Refine.phase3-binary-refines-to-phase6

binaryThenTernaryAndTernaryThenBinaryAgree :
  Refine.binaryRefine
    (Refine.ternaryRefine initialThreeSectorResolution)
  ≡ Refine.ternaryRefine
    (Refine.binaryRefine initialThreeSectorResolution)
binaryThenTernaryAndTernaryThenBinaryAgree =
  Refine.binary-ternary-refinement-commutes
    initialThreeSectorResolution

-- The dihedral C2/C3 action belongs to the ambient ternary
-- carrier; the embedded two-point horn bit fibre is not closed
-- under the full C3 cycle. Do not promote its Weyl qutrit C3
-- to a horn-subdivision operation or Z2 group automorphism.
ternaryAntipodeSquare :
  ∀ t → Dihedral.antipode (Dihedral.antipode t) ≡ t
ternaryAntipodeSquare = Dihedral.antipodeOrderTwo


------------------------------------------------------------------------
-- ADDITIVE GROUP OBSTRUCTION: REUSE REAL EXISTING C2/C3 CARRIERS.
-- A lossless digit codec does not preserve addition across 2-adic
-- and 3-adic groups. The finite generator-order obstruction is
-- literal, not a mere interpreted Boolean receipt.
------------------------------------------------------------------------

import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Algebra.FiniteQuaternionDoubleCover as FiniteQ8

c3HasNoNontrivialElementOfOrderTwo :
  ∀ x → C3._∙_ x x ≡ C3.c0 → x ≡ C3.c0
c3HasNoNontrivialElementOfOrderTwo C3.c0 proof = refl
c3HasNoNontrivialElementOfOrderTwo C3.c1 ()
c3HasNoNontrivialElementOfOrderTwo C3.c2 ()

c2HasNoNontrivialElementOfOrderThree :
  ∀ s →
  FiniteQ8.signMultiply
    (FiniteQ8.signMultiply s s) s
    ≡ FiniteQ8.positiveSign →
  s ≡ FiniteQ8.positiveSign
c2HasNoNontrivialElementOfOrderThree FiniteQ8.positiveSign p = refl
c2HasNoNontrivialElementOfOrderThree FiniteQ8.negativeSign ()

-- Infinite version (classical topological group fact):
-- Hom_cont(Z_2, Z_3) = 0 = Hom_cont(Z_3,Z_2), because every
-- finite quotient of a pro-2 group is a 2-group and of a
-- pro-3 group a 3-group. Not proven in this finite Agda file.
