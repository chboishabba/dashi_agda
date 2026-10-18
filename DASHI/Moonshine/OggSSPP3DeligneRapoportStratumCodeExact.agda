module DASHI.Moonshine.OggSSPP3DeligneRapoportStratumCodeExact where

------------------------------------------------------------------------
-- p=3 F9 QUOTIENT AS DELIGNE--RAPOPORT STRATUM CODE
--
-- Classical local geometry:
--   completed supersingular neighbourhood: semistable node xy = p^a
--   special fibre: xy = 0
--
-- DASHI finite code:
--   negative / zero / positive
--
-- Correct interpretation:
--   the finite ternary state is an exact code for the three local incidence
--   strata (Frobenius branch / node / Verschiebung branch).
--
-- Incorrect interpretation:
--   the finite ternary state is NOT itself a formal/local coordinate x or y,
--   and the F9 extension coordinate is not promoted to a scheme parameter.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Biology.TriadicKernelLiftQuotientExact as Kernel
import DASHI.Moonshine.OggSSPP3F9ExtensionQuotientCandidateExact as F9
import DASHI.Moonshine.OggSSPP3DeligneRapoportLocalStrataRecognitionExact as DR
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Exact finite incidence-code rechart.
------------------------------------------------------------------------

extensionQuotientToLocalStratum :
  F9.P3ExtensionQuotientState ->
  DR.P3LocalStratum
extensionQuotientToLocalStratum =
  DR.kernelToLocal

localStratumToExtensionQuotient :
  DR.P3LocalStratum ->
  F9.P3ExtensionQuotientState
localStratumToExtensionQuotient =
  DR.localToKernel

extensionStratumRoundTrip :
  (state : F9.P3ExtensionQuotientState) ->
  localStratumToExtensionQuotient
    (extensionQuotientToLocalStratum state)
  ≡ state
extensionStratumRoundTrip =
  DR.kernelRoundTrip

stratumExtensionRoundTrip :
  (stratum : DR.P3LocalStratum) ->
  extensionQuotientToLocalStratum
    (localStratumToExtensionQuotient stratum)
  ≡ stratum
stratumExtensionRoundTrip =
  DR.localRoundTrip

------------------------------------------------------------------------
-- 2. Semantic role distinction.
------------------------------------------------------------------------

data LocalGeometricRole : Set where
  incidenceStratumCode :
    LocalGeometricRole
  formalCoordinateX :
    LocalGeometricRole
  formalCoordinateY :
    LocalGeometricRole
  completedLocalRing :
    LocalGeometricRole

p3FiniteCarrierRole : LocalGeometricRole
p3FiniteCarrierRole =
  incidenceStratumCode

data F9FiniteStateIsFormalCoordinate : Set where
data ThreeStrataAreThreeGeometricPoints : Set where
data FiniteRechartIsCompletedLocalRingIsomorphism : Set where

f9FiniteStateIsNotFormalCoordinate :
  F9FiniteStateIsFormalCoordinate -> ⊥
f9FiniteStateIsNotFormalCoordinate ()

threeStrataAreNotThreeGeometricPoints :
  ThreeStrataAreThreeGeometricPoints -> ⊥
threeStrataAreNotThreeGeometricPoints ()

finiteRechartIsNotCompletedLocalRingIsomorphism :
  FiniteRechartIsCompletedLocalRingIsomorphism -> ⊥
finiteRechartIsNotCompletedLocalRingIsomorphism ()

------------------------------------------------------------------------
-- 3. Live boundary.
------------------------------------------------------------------------

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryCrossModuleInference

record P3DeligneRapoportStratumCodeBoundary : Set where
  constructor p3-deligne-rapoport-stratum-code-boundary
  field
    semistableNodeClassicallySourced : Bool
    threeLocalIncidenceStrataClassicallySourced : Bool
    exactFiniteStratumRechartProved : Bool
    f9QuotientInterpretedAsStratumCode : Bool
    f9QuotientInterpretedAsLocalCoordinate : Bool
    completedLocalRingIsomorphismClaimed : Bool

canonicalP3DeligneRapoportStratumCodeBoundary :
  P3DeligneRapoportStratumCodeBoundary
canonicalP3DeligneRapoportStratumCodeBoundary =
  p3-deligne-rapoport-stratum-code-boundary
    true true true true false false
