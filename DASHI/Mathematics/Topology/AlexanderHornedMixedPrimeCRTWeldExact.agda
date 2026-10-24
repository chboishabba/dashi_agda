module DASHI.Mathematics.Topology.AlexanderHornedMixedPrimeCRTWeldExact where

------------------------------------------------------------------------
-- REAL PRIOR ART, NOT ANOTHER RADIX ONTOLOGY
--
-- Base369BinaryTernaryRefinement: the independent 2^a*3^b chart.
-- BinaryBalancedTernarySubcarrierExact: lossless Boolean -> +/- trit.
-- SixWheelCRTExact: actual finite ring residue modulo 6 CRT.
-- AlexanderHornedBinaryPadicCylinderExact: true binary horn ends.
--
-- NEW POINT: the sector x horn-depth-n address system is
--   C3 x (bit-prefix length n),
-- with successive forgetful maps dropping the newest binary digit.
-- It is an inverse system of finite SETS isomorphic to the finite
-- CRT residues (Z/3)x(Z/2^n). The CRT RING structure for all n
-- needs an additional explicit residue-transport construction.
--
-- NO: this is not Z3, nor exterior pi1, nor an identification of
-- balanced ternary digit inclusion with an additive group map.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool; false; true)
import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Foundations.Base369BinaryTernaryRefinement as R23
import DASHI.ComputerScience.BinaryBalancedTernarySubcarrierExact as BTT
import DASHI.Foundations.SSPTritCarrier as Trit
import DASHI.Arithmetic.SixWheelCRTExact as CRT
import DASHI.Arithmetic.SixWheelSieveCountExact as Wheel
import DASHI.Mathematics.Topology.AlexanderHornedC3FiniteStageExact as Horn
import DASHI.Mathematics.Topology.AlexanderHornedBinaryPadicCylinderExact as Bin

record HornCRTStage (n : Nat) : Set where
  constructor horn-crt-stage
  field
    sector : C3.C3
    binary : Bin.BitPrefix n

open HornCRTStage public

forgetNewest : ∀ n → HornCRTStage (suc n) → HornCRTStage n
forgetNewest n (horn-crt-stage c bits) =
  horn-crt-stage c (Bin.dropNewest n bits)

rotateStage : ∀ {n} → HornCRTStage n → HornCRTStage n
rotateStage (horn-crt-stage c bits) =
  horn-crt-stage (Horn.rotateSector c) bits

rotationCommutesWithForgetting : ∀ n (stage : HornCRTStage (suc n)) →
  forgetNewest n (rotateStage stage) ≡
  rotateStage (forgetNewest n stage)
rotationCommutesWithForgetting n (horn-crt-stage c bits) = refl

rotateStageTriple : ∀ {n} (stage : HornCRTStage n) →
  rotateStage (rotateStage (rotateStage stage)) ≡ stage
rotateStageTriple (horn-crt-stage C3.c0 bits) = refl
rotateStageTriple (horn-crt-stage C3.c1 bits) = refl
rotateStageTriple (horn-crt-stage C3.c2 bits) = refl

-- Exact reuse of the pre-existing mixed radix resolution, not a
-- newly defined 'binary-in-ternary' phase chart.
hornCRTResolution : Nat → R23.Resolution23
hornCRTResolution n = R23.resolution23 n 1

hornCRTBinaryRefinement : ∀ n →
  R23.binaryRefine (hornCRTResolution n) ≡
    hornCRTResolution (suc n)
hornCRTBinaryRefinement n = refl

hornCRTCommutesWithOneTernaryRefinement : ∀ n →
  R23.ternaryRefine (R23.binaryRefine (hornCRTResolution n))
  ≡
  R23.binaryRefine (R23.ternaryRefine (hornCRTResolution n))
hornCRTCommutesWithOneTernaryRefinement n =
  R23.binary-ternary-refinement-commutes (hornCRTResolution n)

-- The actual residue-6 CRT is inherited from the existing kernel
-- theorem, not inferred from equality of sector counts.
crtSixRetraction : ∀ r →
  CRT.crt23ToR6 (CRT.r6ToCRT23 r) ≡ r
crtSixRetraction = CRT.r6CRT23RoundTrip

-- Older bit-to-trit embedding, transported from Horn.Bit to Bool:
-- gives a literal injective CODEC on marked horn digits.
hornBitAsBool : Horn.Bit → Bool
hornBitAsBool Horn.left = false
hornBitAsBool Horn.right = true

boolAsHornBit : Bool → Horn.Bit
boolAsHornBit false = Horn.left
boolAsHornBit true = Horn.right

hornBitBooleanRoundTrip : ∀ b →
  boolAsHornBit (hornBitAsBool b) ≡ b
hornBitBooleanRoundTrip Horn.left = refl
hornBitBooleanRoundTrip Horn.right = refl

hornBitToBalancedTernary : Horn.Bit → Trit.SSPTrit
hornBitToBalancedTernary b = BTT.embedBit (hornBitAsBool b)

balancedTernaryOnHornImageToBit : Trit.SSPTrit → Horn.Bit
balancedTernaryOnHornImageToBit t =
  boolAsHornBit (BTT.decodeEmbeddedBit t)

hornBinaryTernaryCodeRoundTrip : ∀ b →
  balancedTernaryOnHornImageToBit (hornBitToBalancedTernary b) ≡ b
hornBinaryTernaryCodeRoundTrip b
  rewrite BTT.binaryTernaryRoundTrip (hornBitAsBool b)
        | hornBitBooleanRoundTrip b = refl

-- The 2^n*3 address stage is an actual finite set. Do NOT
-- derive any addition/multiplication from this codec alone.


------------------------------------------------------------------------
-- REVERSE LOSSLESS FINITE CODE: one balanced trit -> two horn bits.
-- 00, 01, 10 encode {-1, 0, +1}; 11 is deliberately UNUSED.
-- This is a codec inverse ON ITS IMAGE, not a (Z3,+) -> (Z2,+)
-- group homomorphism and not a base-conversion theorem.
------------------------------------------------------------------------

open import Data.Product using (_×_; _,_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)

ternaryAsBinaryPair : Trit.SSPTrit → Horn.Bit × Horn.Bit
ternaryAsBinaryPair Trit.sspNegOne = Horn.left , Horn.left
ternaryAsBinaryPair Trit.sspZero   = Horn.left , Horn.right
ternaryAsBinaryPair Trit.sspPosOne = Horn.right , Horn.left

binaryPairAsTernary : Horn.Bit × Horn.Bit → Maybe Trit.SSPTrit
binaryPairAsTernary (Horn.left , Horn.left) = just Trit.sspNegOne
binaryPairAsTernary (Horn.left , Horn.right) = just Trit.sspZero
binaryPairAsTernary (Horn.right , Horn.left) = just Trit.sspPosOne
binaryPairAsTernary (Horn.right , Horn.right) = nothing

ternaryBinaryTwoBitRoundTrip :
  ∀ t → binaryPairAsTernary (ternaryAsBinaryPair t) ≡ just t
ternaryBinaryTwoBitRoundTrip Trit.sspNegOne = refl
ternaryBinaryTwoBitRoundTrip Trit.sspZero = refl
ternaryBinaryTwoBitRoundTrip Trit.sspPosOne = refl

binaryPairUnusedCode :
  binaryPairAsTernary (Horn.right , Horn.right) ≡ nothing
binaryPairUnusedCode = refl
