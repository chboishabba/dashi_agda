module DASHI.Physics.Closure.FeynmanKelvinTrajectoryCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Foundations.CoupledTrajectoryCoherenceExact as Coupled
import DASHI.Physics.Foundations.StationaryCoherenceClassificationExact as Stationary
import DASHI.Physics.Foundations.ContextConditionedTrajectoryWeightExact as ContextWeight
import DASHI.Physics.Foundations.PathIntegralExperimentalSourceRegistryExact as Sources
import DASHI.Physics.Foundations.FiniteHistoryFunctionalExact as History
import DASHI.Physics.Closure.QuantumPathFibreObservationQuotient as Quantum
import DASHI.Physics.Closure.TSFVCandidate256CalibrationLawDiagnostic as TSFV
import DASHI.Physics.Closure.W4SurrogateScaleSettingBoundary as Surrogate

------------------------------------------------------------------------
-- Cross-pollination owner for the 2023/2026 single-photon path-integral
-- experiments, the existing DASHI path-fibre/history machinery, TSFV's
-- representative/invariant boundary, and finite-source Kelvin wakes.
--
-- The architecture is:
--
--   law/background + experimental/source context
--     -> structured admissible trajectory family
--     -> context-conditioned weights
--     -> action/phase coordinates
--     -> stationary/coherent loci or caustics
--     -> coherent aggregate
--     -> observation quotient
--
-- No step licenses an ontology of independently real reconstructed paths.
------------------------------------------------------------------------

data ExperimentalSupportLayer : Set where
  finitePathDecompositionSupported : ExperimentalSupportLayer
  pathAmplitudeReconstructionSupported : ExperimentalSupportLayer
  coherentCompositionSupported : ExperimentalSupportLayer
  equalMagnitudePostulateSupported : ExperimentalSupportLayer
  actionPhasePostulateSupported : ExperimentalSupportLayer
  propagatorObservationSupported : ExperimentalSupportLayer
  stationaryClassicalExtractionSupported : ExperimentalSupportLayer

data NotEstablishedLayer : Set where
  independentPathOntologyNotEstablished : NotEstablishedLayer
  tsfvUnderlyingFabricNotEstablished : NotEstablishedLayer
  universalMinimumNotEstablished : NotEstablishedLayer
  universalMetricShortestNotEstablished : NotEstablishedLayer
  quantumEntanglementOfAllContextNotEstablished : NotEstablishedLayer

canonicalExperimentalSupport : List ExperimentalSupportLayer
canonicalExperimentalSupport =
  finitePathDecompositionSupported
  ∷ pathAmplitudeReconstructionSupported
  ∷ coherentCompositionSupported
  ∷ equalMagnitudePostulateSupported
  ∷ actionPhasePostulateSupported
  ∷ propagatorObservationSupported
  ∷ stationaryClassicalExtractionSupported
  ∷ []

canonicalNotEstablished : List NotEstablishedLayer
canonicalNotEstablished =
  independentPathOntologyNotEstablished
  ∷ tsfvUnderlyingFabricNotEstablished
  ∷ universalMinimumNotEstablished
  ∷ universalMetricShortestNotEstablished
  ∷ quantumEntanglementOfAllContextNotEstablished
  ∷ []

------------------------------------------------------------------------
-- Exact finite experimental count recorded by Wen et al. 2026.

reconstructedPathCount : Nat
reconstructedPathCount = 1419857

reconstructedPathCountIsReportedValue :
  reconstructedPathCount ≡ 1419857
reconstructedPathCountIsReportedValue = refl

------------------------------------------------------------------------
-- TSFV cross-pollination: transformed quotient representatives are related by
-- an involution and retain the existing diagnostic calibration invariant.
-- This is a structural analogy/bridge only; it is not empirical TSFV support.

tsfvRepresentativeInvolution :
  (q : Surrogate.Candidate256QuotientClass) →
  TSFV.candidate256QuotientT (TSFV.candidate256QuotientT q) ≡ q
tsfvRepresentativeInvolution =
  TSFV.candidate256QuotientTInvolutive

tsfvTransformedRepresentativeCalibrationInvariant :
  (q : Surrogate.Candidate256QuotientClass) →
  TSFV.candidate256TritQuotientCalibrationMap
    (TSFV.candidate256QuotientT q)
  ≡
  TSFV.candidate256TritQuotientCalibrationMap q
tsfvTransformedRepresentativeCalibrationInvariant =
  TSFV.candidate256TritDimensionalInvarianceUnderT

------------------------------------------------------------------------
-- Kelvin-wake boundary: outer admissible caustic and dominant-amplitude angle
-- are separate typed notions.  Source geometry may change the latter while
-- the ideal deep-water Kelvin boundary remains the reference outer wedge.

data KelvinWakeAngleRole : Set where
  outerKelvinCausticBoundary : KelvinWakeAngleRole
  dominantAmplitudeWakeAngle : KelvinWakeAngleRole

data KelvinWakeSourceRegime : Set where
  pointLikeOrLowFroudeRegime : KelvinWakeSourceRegime
  finiteSourceHighFroudeRegime : KelvinWakeSourceRegime

data KelvinWakeSelectionReading : Set where
  fixedOuterBoundaryReading : KelvinWakeSelectionReading
  sourceWeightedInteriorMaximumReading : KelvinWakeSelectionReading

kelvinRoleReading :
  KelvinWakeAngleRole →
  KelvinWakeSelectionReading
kelvinRoleReading outerKelvinCausticBoundary = fixedOuterBoundaryReading
kelvinRoleReading dominantAmplitudeWakeAngle = sourceWeightedInteriorMaximumReading

outerAndDominantWakeRolesAreDistinct :
  outerKelvinCausticBoundary ≡ dominantAmplitudeWakeAngle → ⊥
outerAndDominantWakeRolesAreDistinct ()

------------------------------------------------------------------------
-- Aggregate bridge reusing existing owners.

record FeynmanKelvinTrajectoryBridge : Set₁ where
  field
    coupledTrajectorySurface : Coupled.CoupledTrajectoryFamily
    distinctRelatedPair :
      Coupled.DistinctRelatedPair coupledTrajectorySurface

    stationaryCoherenceSurface : Stationary.StationaryCoherenceSurface
    contextConditionedWeightSurface :
      ContextWeight.ContextConditionedTrajectoryWeight

    finiteHistoryBoundary : History.FiniteHistoryFunctionalBoundary
    quantumPathSurface : Quantum.QuantumPathFibreObservationQuotient

    feynmanHistoricalSource : Sources.SourceReference
    photonPropagator2023Source : Sources.SourceReference
    photonPostulates2026Source : Sources.SourceReference
    photonPostulates2026Dataset : Sources.SourceReference
    shipWake2013Source : Sources.SourceReference
    kelvinWake2014Source : Sources.SourceReference

    experimentalSupport : List ExperimentalSupportLayer
    experimentalSupportIsCanonical :
      experimentalSupport ≡ canonicalExperimentalSupport

    notEstablished : List NotEstablishedLayer
    notEstablishedIsCanonical :
      notEstablished ≡ canonicalNotEstablished

    trajectoryEnumerationIsIndependentOntology : Bool
    trajectoryEnumerationIsIndependentOntologyIsFalse :
      trajectoryEnumerationIsIndependentOntology ≡ false

    stationaryImpliesMinimum : Bool
    stationaryImpliesMinimumIsFalse : stationaryImpliesMinimum ≡ false

    stationaryImpliesMetricShortest : Bool
    stationaryImpliesMetricShortestIsFalse :
      stationaryImpliesMetricShortest ≡ false

    finiteSourceWeightingEqualsAdmissibility : Bool
    finiteSourceWeightingEqualsAdmissibilityIsFalse :
      finiteSourceWeightingEqualsAdmissibility ≡ false

    experimentValidatesTSFV : Bool
    experimentValidatesTSFVIsFalse : experimentValidatesTSFV ≡ false

    bridgeReading : String

open FeynmanKelvinTrajectoryBridge public

canonicalFeynmanKelvinTrajectoryBridge : FeynmanKelvinTrajectoryBridge
canonicalFeynmanKelvinTrajectoryBridge =
  record
    { coupledTrajectorySurface =
        Coupled.canonicalCoupledTrajectoryFamily
    ; distinctRelatedPair =
        Coupled.canonicalDistinctRelatedPair
    ; stationaryCoherenceSurface =
        Stationary.canonicalStationaryCoherenceSurface
    ; contextConditionedWeightSurface =
        ContextWeight.canonicalContextConditionedTrajectoryWeight
    ; finiteHistoryBoundary =
        History.canonicalFiniteHistoryFunctionalBoundary
    ; quantumPathSurface =
        Quantum.canonicalQuantumPathFibreObservationQuotient
    ; feynmanHistoricalSource =
        Sources.feynman1948
    ; photonPropagator2023Source =
        Sources.wenEtAl2023
    ; photonPostulates2026Source =
        Sources.wenEtAl2026
    ; photonPostulates2026Dataset =
        Sources.wenEtAl2026Dataset
    ; shipWake2013Source =
        Sources.rabaudMoisy2013
    ; kelvinWake2014Source =
        Sources.darmonBenzaquenRaphael2014
    ; experimentalSupport =
        canonicalExperimentalSupport
    ; experimentalSupportIsCanonical =
        refl
    ; notEstablished =
        canonicalNotEstablished
    ; notEstablishedIsCanonical =
        refl
    ; trajectoryEnumerationIsIndependentOntology =
        false
    ; trajectoryEnumerationIsIndependentOntologyIsFalse =
        refl
    ; stationaryImpliesMinimum =
        false
    ; stationaryImpliesMinimumIsFalse =
        refl
    ; stationaryImpliesMetricShortest =
        false
    ; stationaryImpliesMetricShortestIsFalse =
        refl
    ; finiteSourceWeightingEqualsAdmissibility =
        false
    ; finiteSourceWeightingEqualsAdmissibilityIsFalse =
        refl
    ; experimentValidatesTSFV =
        false
    ; experimentValidatesTSFVIsFalse =
        refl
    ; bridgeReading =
        "Wen et al. experimentally support the finite path-amplitude/action-phase/coherent-composition layer; DASHI reuses relational path fibres, finite histories, context-conditioned weighting, stationary classification, and TSFV invariant structure without promoting reconstructed paths to independent ontology or the experiments to TSFV validation."
    }
