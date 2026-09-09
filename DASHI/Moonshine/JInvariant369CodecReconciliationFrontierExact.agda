module DASHI.Moonshine.JInvariant369CodecReconciliationFrontierExact where

------------------------------------------------------------------------
-- J-INVARIANT 369 CODEC RECONCILIATION
--
-- Exact total presentation of one nine-sheet as
--
--     centre escape  +  3-bit antipodal payload.
--
-- The eight non-centre states reuse the existing exact 3-bit <-> 2-trit
-- antipodal codec.  The ninth state, (0,0), is retained explicitly rather than
-- silently aliased to a binary word.  This is the codec form of the DASHI
-- rule that the balanced-ternary centre is semantic information.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.ComputerScience.BinaryThreeBitTwoTritAntipodalCodecExact as Block
import DASHI.ComputerScience.BinaryThreeBitTrit27FibreLiftExact as Lift27
import DASHI.Foundations.BalancedTernaryAntipodalOrbitExact as Orbit
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Moonshine.JInvariant369CodecBidiExact as Total

------------------------------------------------------------------------
-- 1. Canonical carrier conversions.
------------------------------------------------------------------------

kernelToSSP : Triadic.KernelTrit → SSP.SSPTrit
kernelToSSP Triadic.negativeTrit = SSP.sspNegOne
kernelToSSP Triadic.zeroTrit = SSP.sspZero
kernelToSSP Triadic.positiveTrit = SSP.sspPosOne

sspToKernel : SSP.SSPTrit → Triadic.KernelTrit
sspToKernel SSP.sspNegOne = Triadic.negativeTrit
sspToKernel SSP.sspZero = Triadic.zeroTrit
sspToKernel SSP.sspPosOne = Triadic.positiveTrit

kernelSSPRoundTrip : (t : Triadic.KernelTrit) → sspToKernel (kernelToSSP t) ≡ t
kernelSSPRoundTrip Triadic.negativeTrit = refl
kernelSSPRoundTrip Triadic.zeroTrit = refl
kernelSSPRoundTrip Triadic.positiveTrit = refl

sspKernelRoundTrip : (t : SSP.SSPTrit) → kernelToSSP (sspToKernel t) ≡ t
sspKernelRoundTrip SSP.sspNegOne = refl
sspKernelRoundTrip SSP.sspZero = refl
sspKernelRoundTrip SSP.sspPosOne = refl

nineToTrit2 : Triadic.NineSheet → Block.Trit2
nineToTrit2 (a , b) = Block.trits2 (kernelToSSP a) (kernelToSSP b)

trit2ToNine : Block.Trit2 → Triadic.NineSheet
trit2ToNine (Block.trits2 a b) = sspToKernel a , sspToKernel b

nineTrit2RoundTrip : (s : Triadic.NineSheet) → trit2ToNine (nineToTrit2 s) ≡ s
nineTrit2RoundTrip (Triadic.negativeTrit , Triadic.negativeTrit) = refl
nineTrit2RoundTrip (Triadic.negativeTrit , Triadic.zeroTrit) = refl
nineTrit2RoundTrip (Triadic.negativeTrit , Triadic.positiveTrit) = refl
nineTrit2RoundTrip (Triadic.zeroTrit , Triadic.negativeTrit) = refl
nineTrit2RoundTrip (Triadic.zeroTrit , Triadic.zeroTrit) = refl
nineTrit2RoundTrip (Triadic.zeroTrit , Triadic.positiveTrit) = refl
nineTrit2RoundTrip (Triadic.positiveTrit , Triadic.negativeTrit) = refl
nineTrit2RoundTrip (Triadic.positiveTrit , Triadic.zeroTrit) = refl
nineTrit2RoundTrip (Triadic.positiveTrit , Triadic.positiveTrit) = refl

trit2NineRoundTrip : (p : Block.Trit2) → nineToTrit2 (trit2ToNine p) ≡ p
trit2NineRoundTrip (Block.trits2 SSP.sspNegOne SSP.sspNegOne) = refl
trit2NineRoundTrip (Block.trits2 SSP.sspNegOne SSP.sspZero) = refl
trit2NineRoundTrip (Block.trits2 SSP.sspNegOne SSP.sspPosOne) = refl
trit2NineRoundTrip (Block.trits2 SSP.sspZero SSP.sspNegOne) = refl
trit2NineRoundTrip (Block.trits2 SSP.sspZero SSP.sspZero) = refl
trit2NineRoundTrip (Block.trits2 SSP.sspZero SSP.sspPosOne) = refl
trit2NineRoundTrip (Block.trits2 SSP.sspPosOne SSP.sspNegOne) = refl
trit2NineRoundTrip (Block.trits2 SSP.sspPosOne SSP.sspZero) = refl
trit2NineRoundTrip (Block.trits2 SSP.sspPosOne SSP.sspPosOne) = refl

------------------------------------------------------------------------
-- 2. Total compact nine-sheet code: one centre escape plus eight 3-bit words.
------------------------------------------------------------------------

centreNine : Triadic.NineSheet
centreNine = Triadic.zeroTrit , Triadic.zeroTrit

data NineCompactCode : Set where
  centreEscape : NineCompactCode
  packed3 : Block.Bit3 → NineCompactCode

encodeCompactNine : Triadic.NineSheet → NineCompactCode
encodeCompactNine (Triadic.zeroTrit , Triadic.zeroTrit) = centreEscape
encodeCompactNine s = packed3 (Block.decode2to3 (nineToTrit2 s))

decodeCompactNine : NineCompactCode → Triadic.NineSheet
decodeCompactNine centreEscape = centreNine
decodeCompactNine (packed3 bits) = trit2ToNine (Block.encode3to2 bits)

decodeEncodeCompactNine :
  (s : Triadic.NineSheet) → decodeCompactNine (encodeCompactNine s) ≡ s
decodeEncodeCompactNine (Triadic.negativeTrit , Triadic.negativeTrit) = refl
decodeEncodeCompactNine (Triadic.negativeTrit , Triadic.zeroTrit) = refl
decodeEncodeCompactNine (Triadic.negativeTrit , Triadic.positiveTrit) = refl
decodeEncodeCompactNine (Triadic.zeroTrit , Triadic.negativeTrit) = refl
decodeEncodeCompactNine (Triadic.zeroTrit , Triadic.zeroTrit) = refl
decodeEncodeCompactNine (Triadic.zeroTrit , Triadic.positiveTrit) = refl
decodeEncodeCompactNine (Triadic.positiveTrit , Triadic.negativeTrit) = refl
decodeEncodeCompactNine (Triadic.positiveTrit , Triadic.zeroTrit) = refl
decodeEncodeCompactNine (Triadic.positiveTrit , Triadic.positiveTrit) = refl

encodeDecodeCompactNine :
  (c : NineCompactCode) → encodeCompactNine (decodeCompactNine c) ≡ c
encodeDecodeCompactNine centreEscape = refl
encodeDecodeCompactNine (packed3 (Block.bits3 false false false)) = refl
encodeDecodeCompactNine (packed3 (Block.bits3 false false true)) = refl
encodeDecodeCompactNine (packed3 (Block.bits3 false true false)) = refl
encodeDecodeCompactNine (packed3 (Block.bits3 false true true)) = refl
encodeDecodeCompactNine (packed3 (Block.bits3 true false false)) = refl
encodeDecodeCompactNine (packed3 (Block.bits3 true false true)) = refl
encodeDecodeCompactNine (packed3 (Block.bits3 true true false)) = refl
encodeDecodeCompactNine (packed3 (Block.bits3 true true true)) = refl

------------------------------------------------------------------------
-- 3. Antipode/complement BIDI, with centre fixed.
------------------------------------------------------------------------

antipodeNine : Triadic.NineSheet → Triadic.NineSheet
antipodeNine (a , b) = Triadic.negateTrit a , Triadic.negateTrit b

compactAntipode : NineCompactCode → NineCompactCode
compactAntipode centreEscape = centreEscape
compactAntipode (packed3 bits) = packed3 (Block.complementBit3 bits)

compactAntipodeIntertwinesNine :
  (s : Triadic.NineSheet) →
  encodeCompactNine (antipodeNine s) ≡ compactAntipode (encodeCompactNine s)
compactAntipodeIntertwinesNine (Triadic.negativeTrit , Triadic.negativeTrit) = refl
compactAntipodeIntertwinesNine (Triadic.negativeTrit , Triadic.zeroTrit) = refl
compactAntipodeIntertwinesNine (Triadic.negativeTrit , Triadic.positiveTrit) = refl
compactAntipodeIntertwinesNine (Triadic.zeroTrit , Triadic.negativeTrit) = refl
compactAntipodeIntertwinesNine (Triadic.zeroTrit , Triadic.zeroTrit) = refl
compactAntipodeIntertwinesNine (Triadic.zeroTrit , Triadic.positiveTrit) = refl
compactAntipodeIntertwinesNine (Triadic.positiveTrit , Triadic.negativeTrit) = refl
compactAntipodeIntertwinesNine (Triadic.positiveTrit , Triadic.zeroTrit) = refl
compactAntipodeIntertwinesNine (Triadic.positiveTrit , Triadic.positiveTrit) = refl

------------------------------------------------------------------------
-- 4. Lift the total nine-sheet codec to the 27 observer with explicit frame.
------------------------------------------------------------------------

record Compact27 : Set where
  constructor compact27
  field
    payload9 : NineCompactCode
    frame3 : SSP.SSPTrit
open Compact27 public

observer27ToNine : Fabric.Ternary27Point → Triadic.NineSheet
observer27ToNine (Fabric.ternary27Point x y z) = sspToKernel x , sspToKernel y

encodeCompact27 : Fabric.Ternary27Point → Compact27
encodeCompact27 p = compact27 (encodeCompactNine (observer27ToNine p)) (Fabric.z p)

decodeCompact27 : Compact27 → Fabric.Ternary27Point
decodeCompact27 (compact27 code frame) with decodeCompactNine code
... | a , b = Fabric.ternary27Point (kernelToSSP a) (kernelToSSP b) frame

decodeEncodeCompact27 :
  (p : Fabric.Ternary27Point) → decodeCompact27 (encodeCompact27 p) ≡ p
decodeEncodeCompact27 (Fabric.ternary27Point x y z)
  rewrite decodeEncodeCompactNine (sspToKernel x , sspToKernel y)
        | sspKernelRoundTrip x
        | sspKernelRoundTrip y = refl

------------------------------------------------------------------------
-- 5. The existing CS 27 lift supplies the same *shape*, not automatic meaning.
------------------------------------------------------------------------

csLiftShape : Block.Trit2 → SSP.SSPTrit → Orbit.TritTriple
csLiftShape pair frame = Lift27.liftTo27 (Lift27.framedTrit2 pair frame)

record J27FrameSemanticBridge : Set₁ where
  field
    FrameMeaning : Set
    jFrameMeaning : SSP.SSPTrit → FrameMeaning
    csFrameMeaning : SSP.SSPTrit → FrameMeaning
    sameFrameMeaning : (t : SSP.SSPTrit) → jFrameMeaning t ≡ csFrameMeaning t

------------------------------------------------------------------------
-- 6. Boundary.
------------------------------------------------------------------------

record JInvariant369CodecReconciliationBoundary : Set where
  constructor j-invariant-369-codec-reconciliation-boundary
  field
    totalNineCodecRoundTrips : Bool
    nonCentreNineUsesExistingThreeBitCodec : Bool
    centreIsExplicitEscape : Bool
    complementIntertwinesAntipode : Bool
    totalTwentySevenCodecRoundTrips : Bool
    twentySevenFrameRemainsExplicit : Bool
    csFrameAutomaticallyEqualsJSeamMeaning : Bool
    analyticJPayloadStillOutsideFiniteCodec : Bool
    entropyOptimalityProvedHere : Bool

canonicalJInvariant369CodecReconciliationBoundary :
  JInvariant369CodecReconciliationBoundary
canonicalJInvariant369CodecReconciliationBoundary =
  j-invariant-369-codec-reconciliation-boundary
    true true true true true true false true false
