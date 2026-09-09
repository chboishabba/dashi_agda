module DASHI.Moonshine.JInvariant369CodecBidiExact where

------------------------------------------------------------------------
-- J-INVARIANT 369 OBSERVER <-> EXISTING VERIFIED CODEC BIDI
--
-- The formulaic renderer retains the analytic J/phase payload and exposes
-- finite same-point observers at 9 and 27 states.  This module does not invent
-- a new codec.  It reuses the repo's verified two-bit balanced-trit coder and
-- proves lossless finite roundtrips for those observer coordinates.
--
-- Important boundary:
--   finite observer codec roundtrip
--   != lossless encoding of the continuous analytic J(tau) payload.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Codec.BalancedTritBitFibre as Fibre
import DASHI.Codec.VerifiedFiniteTritCoder as Coder
import DASHI.Codec.TriadicPAdicCodec369Bridge as Codec369
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric
import DASHI.Moonshine.JInvariantKleinConstructionGluingBidiExact as Klein
import DASHI.Moonshine.JInvariantFormulaic369RendererExact as Render
import DASHI.Moonshine.JInvariantFormulaic369FibreObserverRepairExact as Repair

------------------------------------------------------------------------
-- 1. Exact carrier adapters.  These are representation bridges only.
------------------------------------------------------------------------

kernelTritToTrit : Triadic.KernelTrit → Trit
kernelTritToTrit Triadic.negativeTrit = neg
kernelTritToTrit Triadic.zeroTrit = zer
kernelTritToTrit Triadic.positiveTrit = pos

tritToKernelTrit : Trit → Triadic.KernelTrit
tritToKernelTrit neg = Triadic.negativeTrit
tritToKernelTrit zer = Triadic.zeroTrit
tritToKernelTrit pos = Triadic.positiveTrit

kernelTritRoundtrip :
  (t : Triadic.KernelTrit) →
  tritToKernelTrit (kernelTritToTrit t) ≡ t
kernelTritRoundtrip Triadic.negativeTrit = refl
kernelTritRoundtrip Triadic.zeroTrit = refl
kernelTritRoundtrip Triadic.positiveTrit = refl

tritKernelRoundtrip :
  (t : Trit) →
  kernelTritToTrit (tritToKernelTrit t) ≡ t
tritKernelRoundtrip neg = refl
tritKernelRoundtrip zer = refl
tritKernelRoundtrip pos = refl

------------------------------------------------------------------------
-- 2. One kernel trit uses the existing verified finite machine coder.
------------------------------------------------------------------------

encodeKernelTrit : Triadic.KernelTrit → Coder.Word2
encodeKernelTrit t = Coder.encodeTrit (kernelTritToTrit t)

decodeKernelWord : Coder.Word2 → Maybe Triadic.KernelTrit
decodeKernelWord Coder.word00 = just Triadic.negativeTrit
decodeKernelWord Coder.word01 = just Triadic.zeroTrit
decodeKernelWord Coder.word10 = just Triadic.positiveTrit
decodeKernelWord Coder.word11 = nothing

decodeEncodeKernelTrit :
  (t : Triadic.KernelTrit) →
  decodeKernelWord (encodeKernelTrit t) ≡ just t
decodeEncodeKernelTrit Triadic.negativeTrit = refl
decodeEncodeKernelTrit Triadic.zeroTrit = refl
decodeEncodeKernelTrit Triadic.positiveTrit = refl

kernelReservedWordRejected :
  decodeKernelWord Coder.word11 ≡ nothing
kernelReservedWordRejected = refl

------------------------------------------------------------------------
-- 3. Nine-sheet observer = two balanced trits = four-bit baseline code.
------------------------------------------------------------------------

NineCode : Set
NineCode = Coder.Word2 × Coder.Word2

encodeNine : Triadic.NineSheet → NineCode
encodeNine (a , b) = encodeKernelTrit a , encodeKernelTrit b

decodeNine : NineCode → Maybe Triadic.NineSheet
decodeNine (wa , wb) with decodeKernelWord wa | decodeKernelWord wb
... | just a | just b = just (a , b)
... | nothing | _ = nothing
... | _ | nothing = nothing

decodeEncodeNine :
  (s : Triadic.NineSheet) →
  decodeNine (encodeNine s) ≡ just s
decodeEncodeNine (Triadic.negativeTrit , Triadic.negativeTrit) = refl
decodeEncodeNine (Triadic.negativeTrit , Triadic.zeroTrit) = refl
decodeEncodeNine (Triadic.negativeTrit , Triadic.positiveTrit) = refl
decodeEncodeNine (Triadic.zeroTrit , Triadic.negativeTrit) = refl
decodeEncodeNine (Triadic.zeroTrit , Triadic.zeroTrit) = refl
decodeEncodeNine (Triadic.zeroTrit , Triadic.positiveTrit) = refl
decodeEncodeNine (Triadic.positiveTrit , Triadic.negativeTrit) = refl
decodeEncodeNine (Triadic.positiveTrit , Triadic.zeroTrit) = refl
decodeEncodeNine (Triadic.positiveTrit , Triadic.positiveTrit) = refl

------------------------------------------------------------------------
-- 4. Ternary-27 observer = three SSP trits = existing six-bit triple code.
------------------------------------------------------------------------

encodeSSPTrit : SSP.SSPTrit → Coder.Word2
encodeSSPTrit t = Coder.encodeTrit (SSP.toTrit t)

decodeSSPWord : Coder.Word2 → Maybe SSP.SSPTrit
decodeSSPWord Coder.word00 = just SSP.sspNegOne
decodeSSPWord Coder.word01 = just SSP.sspZero
decodeSSPWord Coder.word10 = just SSP.sspPosOne
decodeSSPWord Coder.word11 = nothing

decodeEncodeSSPTrit :
  (t : SSP.SSPTrit) →
  decodeSSPWord (encodeSSPTrit t) ≡ just t
decodeEncodeSSPTrit SSP.sspNegOne = refl
decodeEncodeSSPTrit SSP.sspZero = refl
decodeEncodeSSPTrit SSP.sspPosOne = refl

Code27 : Set
Code27 = Coder.WordTriple

encode27 : Fabric.Ternary27Point → Code27
encode27 (Fabric.ternary27Point x y z) =
  encodeSSPTrit x , (encodeSSPTrit y , encodeSSPTrit z)

decode27 : Code27 → Maybe Fabric.Ternary27Point
decode27 (wx , (wy , wz))
  with decodeSSPWord wx | decodeSSPWord wy | decodeSSPWord wz
... | just x | just y | just z = just (Fabric.ternary27Point x y z)
... | nothing | _ | _ = nothing
... | _ | nothing | _ = nothing
... | _ | _ | nothing = nothing

decodeEncode27 :
  (p : Fabric.Ternary27Point) →
  decode27 (encode27 p) ≡ just p
decodeEncode27 (Fabric.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne) = refl
decodeEncode27 (Fabric.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspZero) = refl
decodeEncode27 (Fabric.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne) = refl
decodeEncode27 (Fabric.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspNegOne) = refl
decodeEncode27 (Fabric.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspZero) = refl
decodeEncode27 (Fabric.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspPosOne) = refl
decodeEncode27 (Fabric.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspNegOne) = refl
decodeEncode27 (Fabric.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspZero) = refl
decodeEncode27 (Fabric.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspPosOne) = refl
decodeEncode27 (Fabric.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspNegOne) = refl
decodeEncode27 (Fabric.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspZero) = refl
decodeEncode27 (Fabric.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspPosOne) = refl
decodeEncode27 (Fabric.ternary27Point SSP.sspZero SSP.sspZero SSP.sspNegOne) = refl
decodeEncode27 (Fabric.ternary27Point SSP.sspZero SSP.sspZero SSP.sspZero) = refl
decodeEncode27 (Fabric.ternary27Point SSP.sspZero SSP.sspZero SSP.sspPosOne) = refl
decodeEncode27 (Fabric.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspNegOne) = refl
decodeEncode27 (Fabric.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspZero) = refl
decodeEncode27 (Fabric.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspPosOne) = refl
decodeEncode27 (Fabric.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspNegOne) = refl
decodeEncode27 (Fabric.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspZero) = refl
decodeEncode27 (Fabric.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne) = refl
decodeEncode27 (Fabric.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspNegOne) = refl
decodeEncode27 (Fabric.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero) = refl
decodeEncode27 (Fabric.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspPosOne) = refl
decodeEncode27 (Fabric.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne) = refl
decodeEncode27 (Fabric.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspZero) = refl
decodeEncode27 (Fabric.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne) = refl

------------------------------------------------------------------------
-- 5. Same-point renderer observer payload can be encoded without quotienting J.
------------------------------------------------------------------------

record Encoded369ObserverFibre
  (R : Render.JPhaseRenderingAlgebra)
  (F : Repair.SamePointFibreObservers R) : Set where
  constructor encoded369-observer-fibre
  field
    observer9Code : NineCode
    observer27Code : Code27

open Encoded369ObserverFibre public

encodeObserverFibreAt :
  (R : Render.JPhaseRenderingAlgebra) →
  (F : Repair.SamePointFibreObservers R) →
  (z : Klein.Point (Render.klein R)) →
  Encoded369ObserverFibre R F
encodeObserverFibreAt R F z =
  encoded369-observer-fibre
    (encodeNine (Repair.observer9At F z))
    (encode27 (Repair.observer27At F z))

observer9CodecRoundtripAt :
  (R : Render.JPhaseRenderingAlgebra) →
  (F : Repair.SamePointFibreObservers R) →
  (z : Klein.Point (Render.klein R)) →
  decodeNine (observer9Code (encodeObserverFibreAt R F z))
  ≡ just (Repair.observer9At F z)
observer9CodecRoundtripAt R F z = decodeEncodeNine (Repair.observer9At F z)

observer27CodecRoundtripAt :
  (R : Render.JPhaseRenderingAlgebra) →
  (F : Repair.SamePointFibreObservers R) →
  (z : Klein.Point (Render.klein R)) →
  decode27 (observer27Code (encodeObserverFibreAt R F z))
  ≡ just (Repair.observer27At F z)
observer27CodecRoundtripAt R F z = decodeEncode27 (Repair.observer27At F z)

------------------------------------------------------------------------
-- 6. Cross-pollination boundary.
------------------------------------------------------------------------

record JInvariant369CodecBoundary : Set where
  constructor j-invariant-369-codec-boundary
  field
    existingVerifiedFiniteTritCoderReused : Bool
    nineObserverLosslessFiniteRoundtrip : Bool
    twentySevenObserverLosslessFiniteRoundtrip : Bool
    supportSignFibreOwnerReused : Bool
    codec369AddressOwnerReused : Bool
    analyticJPayloadRetainedOutsideFiniteCodec : Bool
    finiteObserverRoundtripImpliesAnalyticJRoundtrip : Bool
    entropyOptimalityProvedHere : Bool
    sourceExactHomannRGBRecoveredHere : Bool

canonicalJInvariant369CodecBoundary : JInvariant369CodecBoundary
canonicalJInvariant369CodecBoundary =
  j-invariant-369-codec-boundary
    true true true true true true false false false
