module DASHI.Moonshine.OggSSPP2ArithmeticBidiDualCodecTransportExact where

------------------------------------------------------------------------
-- ONE ARITHMETIC BIDI INHABITANT TRANSPORTS TO BOTH EXACT p=2 CODECS
--
-- DASHI CONTRIBUTION
--
-- Assume a future arithmetic marked source over the unique raw Gamma_0(4)
-- subgroup ker(F^2) inhabits:
--
--   UniqueGamma0FourMarkingBidi source
--
-- i.e. it is exactly equivalent to the paid ten-state target.
--
-- Then no further source theorem is needed merely to obtain either of the
-- target's two dependent normal forms:
--
--   (A) F4/Frobenius coarse code with fibre profile 1,1,8;
--   (B) PhaseNine coarse code with a two-branch residual only at the centre.
--
-- Both are transported losslessly through the same arithmetic bidi, and the
-- two induced source codes commute with the paid DualDependentCodecBidi.
--
-- Thus the remaining arithmetic wall is reduced to constructing the one
-- same-object bidi inhabitant; the two finite coarse descriptions then follow
-- automatically.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Core.DependentRecoverableProjectionExact as Dependent
import DASHI.Moonshine.OggSSPP2Gamma0FourUniqueSupersingularSubgroupSeparationExact as Unique
import DASHI.Moonshine.OggSSPP2UniqueGamma0FourMarkingBidiExact as Bidi
import DASHI.Moonshine.OggSSPP2F4DependentMarkedCoverExact as F4Code
import DASHI.Moonshine.OggSSPP2BalancedTernaryPuncturedPlaneExact as Plane
import DASHI.Moonshine.OggSSPP2TrialecticNineCentreResidualBidiExact as PhaseCode
import DASHI.Moonshine.OggSSPP2DualDependentCodecBidiExact as Dual
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

F4DependentCode : Set
F4DependentCode =
  Dependent.DependentCode F4Code.p2F4DependentMarkedProjection

PhaseDependentCode : Set
PhaseDependentCode =
  Dependent.DependentCode PhaseCode.trialecticNineCentreResidualProjection

------------------------------------------------------------------------
-- 1. Source <-> F4 dependent code.
------------------------------------------------------------------------

encodeArithmeticF4 :
  {source : Unique.MarkingOverUniqueGamma0FourSubgroup} ->
  Bidi.UniqueGamma0FourMarkingBidi source ->
  Unique.MarkedState source ->
  F4DependentCode
encodeArithmeticF4 bidi state =
  F4Code.encodeMarked (Bidi.toTarget bidi state)

decodeArithmeticF4 :
  {source : Unique.MarkingOverUniqueGamma0FourSubgroup} ->
  Bidi.UniqueGamma0FourMarkingBidi source ->
  F4DependentCode ->
  Unique.MarkedState source
decodeArithmeticF4 bidi code =
  Bidi.fromTarget bidi (F4Code.decodeMarked code)

arithmeticF4DecodeEncode :
  {source : Unique.MarkingOverUniqueGamma0FourSubgroup} ->
  (bidi : Bidi.UniqueGamma0FourMarkingBidi source) ->
  (state : Unique.MarkedState source) ->
  decodeArithmeticF4 bidi (encodeArithmeticF4 bidi state)
  ≡ state
arithmeticF4DecodeEncode bidi state
  rewrite F4Code.decodeEncodeMarked (Bidi.toTarget bidi state)
        | Bidi.sourceRoundTrip bidi state = refl

arithmeticF4EncodeDecode :
  {source : Unique.MarkingOverUniqueGamma0FourSubgroup} ->
  (bidi : Bidi.UniqueGamma0FourMarkingBidi source) ->
  (code : F4DependentCode) ->
  encodeArithmeticF4 bidi (decodeArithmeticF4 bidi code)
  ≡ code
arithmeticF4EncodeDecode bidi code
  rewrite Bidi.targetRoundTrip bidi (F4Code.decodeMarked code)
        | F4Code.encodeDecodeMarked code = refl

------------------------------------------------------------------------
-- 2. Source <-> PhaseNine + centre residual code.
------------------------------------------------------------------------

encodeArithmeticPhase :
  {source : Unique.MarkingOverUniqueGamma0FourSubgroup} ->
  Bidi.UniqueGamma0FourMarkingBidi source ->
  Unique.MarkedState source ->
  PhaseDependentCode
encodeArithmeticPhase bidi state =
  PhaseCode.encode
    (Plane.stratifiedToDuplicatedCentre
      (Bidi.toTarget bidi state))

decodeArithmeticPhase :
  {source : Unique.MarkingOverUniqueGamma0FourSubgroup} ->
  Bidi.UniqueGamma0FourMarkingBidi source ->
  PhaseDependentCode ->
  Unique.MarkedState source
decodeArithmeticPhase bidi code =
  Bidi.fromTarget bidi
    (Plane.duplicatedCentreToStratified
      (PhaseCode.decode code))

arithmeticPhaseDecodeEncode :
  {source : Unique.MarkingOverUniqueGamma0FourSubgroup} ->
  (bidi : Bidi.UniqueGamma0FourMarkingBidi source) ->
  (state : Unique.MarkedState source) ->
  decodeArithmeticPhase bidi (encodeArithmeticPhase bidi state)
  ≡ state
arithmeticPhaseDecodeEncode bidi state
  rewrite PhaseCode.decodeEncode
    (Plane.stratifiedToDuplicatedCentre
      (Bidi.toTarget bidi state))
        | Plane.stratifiedDuplicatedCentreRoundTrip
            (Bidi.toTarget bidi state)
        | Bidi.sourceRoundTrip bidi state = refl

arithmeticPhaseEncodeDecode :
  {source : Unique.MarkingOverUniqueGamma0FourSubgroup} ->
  (bidi : Bidi.UniqueGamma0FourMarkingBidi source) ->
  (code : PhaseDependentCode) ->
  encodeArithmeticPhase bidi (decodeArithmeticPhase bidi code)
  ≡ code
arithmeticPhaseEncodeDecode bidi code
  rewrite Bidi.targetRoundTrip bidi
    (Plane.duplicatedCentreToStratified
      (PhaseCode.decode code))
        | Plane.duplicatedCentreStratifiedRoundTrip
            (PhaseCode.decode code)
        | PhaseCode.encodeDecode code = refl

------------------------------------------------------------------------
-- 3. The two induced arithmetic code paths commute exactly.
------------------------------------------------------------------------

arithmeticF4ToPhaseCommutes :
  {source : Unique.MarkingOverUniqueGamma0FourSubgroup} ->
  (bidi : Bidi.UniqueGamma0FourMarkingBidi source) ->
  (state : Unique.MarkedState source) ->
  Dual.f4CodeToPhaseCode (encodeArithmeticF4 bidi state)
  ≡ encodeArithmeticPhase bidi state
arithmeticF4ToPhaseCommutes bidi state
  rewrite F4Code.decodeEncodeMarked (Bidi.toTarget bidi state) = refl

arithmeticPhaseToF4Commutes :
  {source : Unique.MarkingOverUniqueGamma0FourSubgroup} ->
  (bidi : Bidi.UniqueGamma0FourMarkingBidi source) ->
  (state : Unique.MarkedState source) ->
  Dual.phaseCodeToF4Code (encodeArithmeticPhase bidi state)
  ≡ encodeArithmeticF4 bidi state
arithmeticPhaseToF4Commutes bidi state
  rewrite PhaseCode.decodeEncode
    (Plane.stratifiedToDuplicatedCentre
      (Bidi.toTarget bidi state))
        | Plane.stratifiedDuplicatedCentreRoundTrip
            (Bidi.toTarget bidi state) = refl

------------------------------------------------------------------------
-- 4. Frontier compression.
------------------------------------------------------------------------

data SeparateArithmeticProofOfBothFiniteCodecsRequired : Set where

separateArithmeticProofsNotRequiredAfterBidi :
  SeparateArithmeticProofOfBothFiniteCodecsRequired ->
  ⊥
separateArithmeticProofsNotRequiredAfterBidi ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryCrossModuleInference

record ArithmeticBidiDualCodecTransportBoundary : Set where
  constructor arithmetic-bidi-dual-codec-transport-boundary
  field
    arithmeticBidiSufficesForF4Codec : Bool
    arithmeticBidiSufficesForPhaseCodec : Bool
    f4SourceCodecBidiPaidConditionally : Bool
    phaseSourceCodecBidiPaidConditionally : Bool
    dualCodeChangeCommutes : Bool
    separateFiniteCodecRecognitionProofsRequiredAfterBidi : Bool
    arithmeticBidiInhabitedHere : Bool

canonicalArithmeticBidiDualCodecTransportBoundary :
  ArithmeticBidiDualCodecTransportBoundary
canonicalArithmeticBidiDualCodecTransportBoundary =
  arithmetic-bidi-dual-codec-transport-boundary
    true true true true true false false
