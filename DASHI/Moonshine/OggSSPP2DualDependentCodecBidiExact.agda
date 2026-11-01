module DASHI.Moonshine.OggSSPP2DualDependentCodecBidiExact where

------------------------------------------------------------------------
-- p=2 DUAL DEPENDENT CODECS OF THE SAME TEN-STATE TARGET
--
-- DASHI CONTRIBUTION
--
-- The p=2 target now has two exact dependent descriptions.
--
-- Arithmetic/F4 coarse language:
--
--   Sigma(o : F4/Frob), Mark_F4(o)
--
-- with fibre profile
--
--   1, 1, 8.
--
-- Pre-RH trialectic observer language:
--
--   Sigma(q : T^2), CentreResidual(q)
--
-- with fibre profile
--
--   2 at q=0, 1 at each of the eight noncentral q.
--
-- Both decode to the same ten-state fine target, so this module constructs the
-- exact two-sided change of code by decode -> rechart -> encode.
--
-- This is a finite same-fine-object theorem.  It does not identify the
-- arithmetic meaning of F4 strata with the trialectic meaning of T^2 states.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Core.DependentRecoverableProjectionExact as Dependent
import DASHI.Moonshine.OggSSPP2F4DependentMarkedCoverExact as F4Code
import DASHI.Moonshine.OggSSPP2BalancedTernaryPuncturedPlaneExact as Plane
import DASHI.Moonshine.OggSSPP2TrialecticNineCentreResidualBidiExact as PhaseCode
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

F4DependentCode : Set
F4DependentCode =
  Dependent.DependentCode F4Code.p2F4DependentMarkedProjection

PhaseDependentCode : Set
PhaseDependentCode =
  Dependent.DependentCode PhaseCode.trialecticNineCentreResidualProjection

------------------------------------------------------------------------
-- 1. Exact change of coarse language.
------------------------------------------------------------------------

f4CodeToPhaseCode :
  F4DependentCode ->
  PhaseDependentCode
f4CodeToPhaseCode code =
  PhaseCode.encode
    (Plane.stratifiedToDuplicatedCentre
      (F4Code.decodeMarked code))

phaseCodeToF4Code :
  PhaseDependentCode ->
  F4DependentCode
phaseCodeToF4Code code =
  F4Code.encodeMarked
    (Plane.duplicatedCentreToStratified
      (PhaseCode.decode code))

------------------------------------------------------------------------
-- 2. Two-sided recovery.
------------------------------------------------------------------------

f4PhaseRoundTrip :
  (code : F4DependentCode) ->
  phaseCodeToF4Code (f4CodeToPhaseCode code)
  ≡ code
f4PhaseRoundTrip code
  rewrite PhaseCode.decodeEncode
    (Plane.stratifiedToDuplicatedCentre
      (F4Code.decodeMarked code))
        | Plane.stratifiedDuplicatedCentreRoundTrip
            (F4Code.decodeMarked code)
        | F4Code.encodeDecodeMarked code = refl

phaseF4RoundTrip :
  (code : PhaseDependentCode) ->
  f4CodeToPhaseCode (phaseCodeToF4Code code)
  ≡ code
phaseF4RoundTrip code
  rewrite F4Code.decodeEncodeMarked
    (Plane.duplicatedCentreToStratified
      (PhaseCode.decode code))
        | Plane.duplicatedCentreStratifiedRoundTrip
            (PhaseCode.decode code)
        | PhaseCode.encodeDecode code = refl

------------------------------------------------------------------------
-- 3. Same fine state under both codes.
------------------------------------------------------------------------

f4FineState :
  F4DependentCode ->
  Plane.DuplicatedCentreNineSheet
f4FineState code =
  Plane.stratifiedToDuplicatedCentre
    (F4Code.decodeMarked code)

phaseFineState :
  PhaseDependentCode ->
  Plane.DuplicatedCentreNineSheet
phaseFineState =
  PhaseCode.decode

f4ToPhasePreservesFineState :
  (code : F4DependentCode) ->
  phaseFineState (f4CodeToPhaseCode code)
  ≡ f4FineState code
f4ToPhasePreservesFineState code =
  PhaseCode.decodeEncode
    (Plane.stratifiedToDuplicatedCentre
      (F4Code.decodeMarked code))

phaseToF4PreservesFineState :
  (code : PhaseDependentCode) ->
  f4FineState (phaseCodeToF4Code code)
  ≡ phaseFineState code
phaseToF4PreservesFineState code
  rewrite F4Code.decodeEncodeMarked
    (Plane.duplicatedCentreToStratified
      (PhaseCode.decode code))
        | Plane.duplicatedCentreStratifiedRoundTrip
            (PhaseCode.decode code) = refl

------------------------------------------------------------------------
-- 4. Semantic firewall.
------------------------------------------------------------------------

data EqualFineObjectIdentifiesCoarseSemantics : Set where
data CodecBidiCreatesArithmeticTrialecticIdentity : Set where

equalFineObjectDoesNotIdentifyCoarseSemantics :
  EqualFineObjectIdentifiesCoarseSemantics -> ⊥
equalFineObjectDoesNotIdentifyCoarseSemantics ()

codecBidiDoesNotCreateArithmeticTrialecticIdentity :
  CodecBidiCreatesArithmeticTrialecticIdentity -> ⊥
codecBidiDoesNotCreateArithmeticTrialecticIdentity ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryCrossModuleInference

record DualDependentCodecBidiBoundary : Set where
  constructor dual-dependent-codec-bidi-boundary
  field
    f4OneOneEightCodecReused : Bool
    phaseNineCentreResidualCodecReused : Bool
    f4ToPhaseCodeConstructed : Bool
    phaseToF4CodeConstructed : Bool
    twoSidedRoundTripsPaid : Bool
    commonFineStatePreservedBothWays : Bool
    coarseSemanticsIdentified : Bool
    arithmeticTrialecticIdentityClaimed : Bool

canonicalDualDependentCodecBidiBoundary :
  DualDependentCodecBidiBoundary
canonicalDualDependentCodecBidiBoundary =
  dual-dependent-codec-bidi-boundary
    true true true true true true false false
