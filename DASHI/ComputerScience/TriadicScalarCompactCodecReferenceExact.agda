module DASHI.ComputerScience.TriadicScalarCompactCodecReferenceExact where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Codec.TriadicMaskSignFactorization as MaskSign
import DASHI.ComputerScience.TriadicActiveCountPhysicalLoweringExact as Active
import DASHI.ComputerScience.TriadicPrefixSignCompactionPhysicalLoweringExact as Prefix

------------------------------------------------------------------------
-- BOUNDED SCALAR REFERENCE CODEC
--
-- This is the first complete compact encode/decode carrier for a three-trit
-- symbol.  The constructor shape itself enforces that the number of compact
-- signs agrees with the support mask.  Signs are stored in positional order.
--
-- This is executable Agda/reference logic.  It is not yet a machine-word,
-- SWAR, SIMD, CUDA, ROCm, or measured-runtime implementation.
------------------------------------------------------------------------

data Encoded3 : Set where
  enc000 : Encoded3
  enc001 : MaskSign.Sign → Encoded3
  enc010 : MaskSign.Sign → Encoded3
  enc011 : MaskSign.Sign → MaskSign.Sign → Encoded3
  enc100 : MaskSign.Sign → Encoded3
  enc101 : MaskSign.Sign → MaskSign.Sign → Encoded3
  enc110 : MaskSign.Sign → MaskSign.Sign → Encoded3
  enc111 : MaskSign.Sign → MaskSign.Sign → MaskSign.Sign → Encoded3

encodedMask : Encoded3 → MaskSign.Mask3
encodedMask enc000 = MaskSign.mask000
encodedMask (enc001 _) = MaskSign.mask001
encodedMask (enc010 _) = MaskSign.mask010
encodedMask (enc011 _ _) = MaskSign.mask011
encodedMask (enc100 _) = MaskSign.mask100
encodedMask (enc101 _ _) = MaskSign.mask101
encodedMask (enc110 _ _) = MaskSign.mask110
encodedMask (enc111 _ _ _) = MaskSign.mask111

encodedSignCount : Encoded3 → Nat
encodedSignCount enc000 = 0
encodedSignCount (enc001 _) = 1
encodedSignCount (enc010 _) = 1
encodedSignCount (enc011 _ _) = 2
encodedSignCount (enc100 _) = 1
encodedSignCount (enc101 _ _) = 2
encodedSignCount (enc110 _ _) = 2
encodedSignCount (enc111 _ _ _) = 3

signToTrit : MaskSign.Sign → Trit
signToTrit MaskSign.negative = neg
signToTrit MaskSign.positive = pos

encode3 : MaskSign.Triple Trit → Encoded3
encode3 (MaskSign.triple neg neg neg) = enc111 MaskSign.negative MaskSign.negative MaskSign.negative
encode3 (MaskSign.triple neg neg zer) = enc110 MaskSign.negative MaskSign.negative
encode3 (MaskSign.triple neg neg pos) = enc111 MaskSign.negative MaskSign.negative MaskSign.positive
encode3 (MaskSign.triple neg zer neg) = enc101 MaskSign.negative MaskSign.negative
encode3 (MaskSign.triple neg zer zer) = enc100 MaskSign.negative
encode3 (MaskSign.triple neg zer pos) = enc101 MaskSign.negative MaskSign.positive
encode3 (MaskSign.triple neg pos neg) = enc111 MaskSign.negative MaskSign.positive MaskSign.negative
encode3 (MaskSign.triple neg pos zer) = enc110 MaskSign.negative MaskSign.positive
encode3 (MaskSign.triple neg pos pos) = enc111 MaskSign.negative MaskSign.positive MaskSign.positive
encode3 (MaskSign.triple zer neg neg) = enc011 MaskSign.negative MaskSign.negative
encode3 (MaskSign.triple zer neg zer) = enc010 MaskSign.negative
encode3 (MaskSign.triple zer neg pos) = enc011 MaskSign.negative MaskSign.positive
encode3 (MaskSign.triple zer zer neg) = enc001 MaskSign.negative
encode3 (MaskSign.triple zer zer zer) = enc000
encode3 (MaskSign.triple zer zer pos) = enc001 MaskSign.positive
encode3 (MaskSign.triple zer pos neg) = enc011 MaskSign.positive MaskSign.negative
encode3 (MaskSign.triple zer pos zer) = enc010 MaskSign.positive
encode3 (MaskSign.triple zer pos pos) = enc011 MaskSign.positive MaskSign.positive
encode3 (MaskSign.triple pos neg neg) = enc111 MaskSign.positive MaskSign.negative MaskSign.negative
encode3 (MaskSign.triple pos neg zer) = enc110 MaskSign.positive MaskSign.negative
encode3 (MaskSign.triple pos neg pos) = enc111 MaskSign.positive MaskSign.negative MaskSign.positive
encode3 (MaskSign.triple pos zer neg) = enc101 MaskSign.positive MaskSign.negative
encode3 (MaskSign.triple pos zer zer) = enc100 MaskSign.positive
encode3 (MaskSign.triple pos zer pos) = enc101 MaskSign.positive MaskSign.positive
encode3 (MaskSign.triple pos pos neg) = enc111 MaskSign.positive MaskSign.positive MaskSign.negative
encode3 (MaskSign.triple pos pos zer) = enc110 MaskSign.positive MaskSign.positive
encode3 (MaskSign.triple pos pos pos) = enc111 MaskSign.positive MaskSign.positive MaskSign.positive

decode3 : Encoded3 → MaskSign.Triple Trit
decode3 enc000 = MaskSign.triple zer zer zer
decode3 (enc001 c) = MaskSign.triple zer zer (signToTrit c)
decode3 (enc010 b) = MaskSign.triple zer (signToTrit b) zer
decode3 (enc011 b c) = MaskSign.triple zer (signToTrit b) (signToTrit c)
decode3 (enc100 a) = MaskSign.triple (signToTrit a) zer zer
decode3 (enc101 a c) = MaskSign.triple (signToTrit a) zer (signToTrit c)
decode3 (enc110 a b) = MaskSign.triple (signToTrit a) (signToTrit b) zer
decode3 (enc111 a b c) = MaskSign.triple (signToTrit a) (signToTrit b) (signToTrit c)

------------------------------------------------------------------------
-- Exact round trips.
------------------------------------------------------------------------

decode3-encode3 : (t : MaskSign.Triple Trit) → decode3 (encode3 t) ≡ t
decode3-encode3 (MaskSign.triple neg neg neg) = refl
decode3-encode3 (MaskSign.triple neg neg zer) = refl
decode3-encode3 (MaskSign.triple neg neg pos) = refl
decode3-encode3 (MaskSign.triple neg zer neg) = refl
decode3-encode3 (MaskSign.triple neg zer zer) = refl
decode3-encode3 (MaskSign.triple neg zer pos) = refl
decode3-encode3 (MaskSign.triple neg pos neg) = refl
decode3-encode3 (MaskSign.triple neg pos zer) = refl
decode3-encode3 (MaskSign.triple neg pos pos) = refl
decode3-encode3 (MaskSign.triple zer neg neg) = refl
decode3-encode3 (MaskSign.triple zer neg zer) = refl
decode3-encode3 (MaskSign.triple zer neg pos) = refl
decode3-encode3 (MaskSign.triple zer zer neg) = refl
decode3-encode3 (MaskSign.triple zer zer zer) = refl
decode3-encode3 (MaskSign.triple zer zer pos) = refl
decode3-encode3 (MaskSign.triple zer pos neg) = refl
decode3-encode3 (MaskSign.triple zer pos zer) = refl
decode3-encode3 (MaskSign.triple zer pos pos) = refl
decode3-encode3 (MaskSign.triple pos neg neg) = refl
decode3-encode3 (MaskSign.triple pos neg zer) = refl
decode3-encode3 (MaskSign.triple pos neg pos) = refl
decode3-encode3 (MaskSign.triple pos zer neg) = refl
decode3-encode3 (MaskSign.triple pos zer zer) = refl
decode3-encode3 (MaskSign.triple pos zer pos) = refl
decode3-encode3 (MaskSign.triple pos pos neg) = refl
decode3-encode3 (MaskSign.triple pos pos zer) = refl
decode3-encode3 (MaskSign.triple pos pos pos) = refl

encode3-decode3 : (e : Encoded3) → encode3 (decode3 e) ≡ e
encode3-decode3 enc000 = refl
encode3-decode3 (enc001 MaskSign.negative) = refl
encode3-decode3 (enc001 MaskSign.positive) = refl
encode3-decode3 (enc010 MaskSign.negative) = refl
encode3-decode3 (enc010 MaskSign.positive) = refl
encode3-decode3 (enc011 MaskSign.negative MaskSign.negative) = refl
encode3-decode3 (enc011 MaskSign.negative MaskSign.positive) = refl
encode3-decode3 (enc011 MaskSign.positive MaskSign.negative) = refl
encode3-decode3 (enc011 MaskSign.positive MaskSign.positive) = refl
encode3-decode3 (enc100 MaskSign.negative) = refl
encode3-decode3 (enc100 MaskSign.positive) = refl
encode3-decode3 (enc101 MaskSign.negative MaskSign.negative) = refl
encode3-decode3 (enc101 MaskSign.negative MaskSign.positive) = refl
encode3-decode3 (enc101 MaskSign.positive MaskSign.negative) = refl
encode3-decode3 (enc101 MaskSign.positive MaskSign.positive) = refl
encode3-decode3 (enc110 MaskSign.negative MaskSign.negative) = refl
encode3-decode3 (enc110 MaskSign.negative MaskSign.positive) = refl
encode3-decode3 (enc110 MaskSign.positive MaskSign.negative) = refl
encode3-decode3 (enc110 MaskSign.positive MaskSign.positive) = refl
encode3-decode3 (enc111 MaskSign.negative MaskSign.negative MaskSign.negative) = refl
encode3-decode3 (enc111 MaskSign.negative MaskSign.negative MaskSign.positive) = refl
encode3-decode3 (enc111 MaskSign.negative MaskSign.positive MaskSign.negative) = refl
encode3-decode3 (enc111 MaskSign.negative MaskSign.positive MaskSign.positive) = refl
encode3-decode3 (enc111 MaskSign.positive MaskSign.negative MaskSign.negative) = refl
encode3-decode3 (enc111 MaskSign.positive MaskSign.negative MaskSign.positive) = refl
encode3-decode3 (enc111 MaskSign.positive MaskSign.positive MaskSign.negative) = refl
encode3-decode3 (enc111 MaskSign.positive MaskSign.positive MaskSign.positive) = refl

------------------------------------------------------------------------
-- Agreement with the existing support/count semantics.
------------------------------------------------------------------------

encodedMask-agrees :
  (t : MaskSign.Triple Trit) →
  encodedMask (encode3 t) ≡ MaskSign.maskOf (MaskSign.encodeTriple t)
encodedMask-agrees (MaskSign.triple neg neg neg) = refl
encodedMask-agrees (MaskSign.triple neg neg zer) = refl
encodedMask-agrees (MaskSign.triple neg neg pos) = refl
encodedMask-agrees (MaskSign.triple neg zer neg) = refl
encodedMask-agrees (MaskSign.triple neg zer zer) = refl
encodedMask-agrees (MaskSign.triple neg zer pos) = refl
encodedMask-agrees (MaskSign.triple neg pos neg) = refl
encodedMask-agrees (MaskSign.triple neg pos zer) = refl
encodedMask-agrees (MaskSign.triple neg pos pos) = refl
encodedMask-agrees (MaskSign.triple zer neg neg) = refl
encodedMask-agrees (MaskSign.triple zer neg zer) = refl
encodedMask-agrees (MaskSign.triple zer neg pos) = refl
encodedMask-agrees (MaskSign.triple zer zer neg) = refl
encodedMask-agrees (MaskSign.triple zer zer zer) = refl
encodedMask-agrees (MaskSign.triple zer zer pos) = refl
encodedMask-agrees (MaskSign.triple zer pos neg) = refl
encodedMask-agrees (MaskSign.triple zer pos zer) = refl
encodedMask-agrees (MaskSign.triple zer pos pos) = refl
encodedMask-agrees (MaskSign.triple pos neg neg) = refl
encodedMask-agrees (MaskSign.triple pos neg zer) = refl
encodedMask-agrees (MaskSign.triple pos neg pos) = refl
encodedMask-agrees (MaskSign.triple pos zer neg) = refl
encodedMask-agrees (MaskSign.triple pos zer zer) = refl
encodedMask-agrees (MaskSign.triple pos zer pos) = refl
encodedMask-agrees (MaskSign.triple pos pos neg) = refl
encodedMask-agrees (MaskSign.triple pos pos zer) = refl
encodedMask-agrees (MaskSign.triple pos pos pos) = refl

encodedSignCount-agrees :
  (t : MaskSign.Triple Trit) →
  encodedSignCount (encode3 t) ≡ MaskSign.activeCount (MaskSign.encodeTriple t)
encodedSignCount-agrees (MaskSign.triple neg neg neg) = refl
encodedSignCount-agrees (MaskSign.triple neg neg zer) = refl
encodedSignCount-agrees (MaskSign.triple neg neg pos) = refl
encodedSignCount-agrees (MaskSign.triple neg zer neg) = refl
encodedSignCount-agrees (MaskSign.triple neg zer zer) = refl
encodedSignCount-agrees (MaskSign.triple neg zer pos) = refl
encodedSignCount-agrees (MaskSign.triple neg pos neg) = refl
encodedSignCount-agrees (MaskSign.triple neg pos zer) = refl
encodedSignCount-agrees (MaskSign.triple neg pos pos) = refl
encodedSignCount-agrees (MaskSign.triple zer neg neg) = refl
encodedSignCount-agrees (MaskSign.triple zer neg zer) = refl
encodedSignCount-agrees (MaskSign.triple zer neg pos) = refl
encodedSignCount-agrees (MaskSign.triple zer zer neg) = refl
encodedSignCount-agrees (MaskSign.triple zer zer zer) = refl
encodedSignCount-agrees (MaskSign.triple zer zer pos) = refl
encodedSignCount-agrees (MaskSign.triple zer pos neg) = refl
encodedSignCount-agrees (MaskSign.triple zer pos zer) = refl
encodedSignCount-agrees (MaskSign.triple zer pos pos) = refl
encodedSignCount-agrees (MaskSign.triple pos neg neg) = refl
encodedSignCount-agrees (MaskSign.triple pos neg zer) = refl
encodedSignCount-agrees (MaskSign.triple pos neg pos) = refl
encodedSignCount-agrees (MaskSign.triple pos zer neg) = refl
encodedSignCount-agrees (MaskSign.triple pos zer zer) = refl
encodedSignCount-agrees (MaskSign.triple pos zer pos) = refl
encodedSignCount-agrees (MaskSign.triple pos pos neg) = refl
encodedSignCount-agrees (MaskSign.triple pos pos zer) = refl
encodedSignCount-agrees (MaskSign.triple pos pos pos) = refl

------------------------------------------------------------------------
-- Roadmap update: reference executable semantics are now closed, but no
-- physical backend has been paid merely by defining total Agda functions.
------------------------------------------------------------------------

prefixRoadmap : Prefix.PortableTriadicCodecRoadmap
prefixRoadmap = Prefix.currentPortableTriadicCodecRoadmap

record ScalarReferenceBoundary : Set where
  constructor scalar-reference-boundary
  field
    finiteEncodedCarrier : Bool
    encodeTotal : Bool
    decodeTotal : Bool
    decodeEncodeRoundTrip : Bool
    encodeDecodeRoundTrip : Bool
    supportMaskAgreement : Bool
    activeCountAgreement : Bool
    compactSignsStoredInPositionOrder : Bool
    machineWordBindingPaid : Bool
    exactSWARInstructionSequencePaid : Bool
    compiledRuntimeReceiptPaid : Bool
    measuredPerformancePaid : Bool
open ScalarReferenceBoundary public

canonicalScalarReferenceBoundary : ScalarReferenceBoundary
canonicalScalarReferenceBoundary = scalar-reference-boundary
  true true true true true true true true false false false false
