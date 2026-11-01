module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseAttributedSparseTransitionKernelExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseWeightedNDimStateGraphExact as Graph
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSparseCalibrationFibreExact as Sparse
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attr

------------------------------------------------------------------------
-- ATTRIBUTED SPARSE TRANSITION KERNEL
--
-- This is the first kernel-shaped object in the AdK lane that carries the
-- source/provenance envelope all the way down to each rate coordinate.  It is
-- deliberately sparse: graph topology is paid, Kramers rate *role* is paid,
-- but the exact Figure-5 arrow numerics remain unpaid.  Missing values stay in
-- the kernel instead of disappearing from it.
------------------------------------------------------------------------

record AttributedKernelEdge : Set where
  constructor attributed-kernel-edge
  field
    graphEdge : Graph.DirectedLandscapeEdge
    rateCalibration : Sparse.EdgeRateCalibration
    rateAtom : Attr.CalibrationAtomEnvelope
    interpretation : String
open AttributedKernelEdge public

mkKernelEdge :
  (edge : Graph.DirectedLandscapeEdge) →
  (calibration : Sparse.EdgeRateCalibration) →
  String →
  AttributedKernelEdge
mkKernelEdge edge calibration label =
  attributed-kernel-edge
    edge
    calibration
    (Attr.mkLiLiuJiAtom
      label
      (Sparse.rate calibration)
      "Kramers-derived Figure-5 edge-rate role"
      "topology is source-paid; exact rate numeral stays unpaid until same-object figure acquisition")
    "edge topology and rate provenance are retained independently; missing rate does not erase the edge"

alphaBetaKernelEdge : AttributedKernelEdge
alphaBetaKernelEdge = mkKernelEdge Graph.alphaBeta Sparse.alphaBetaRate "alpha->beta Kramers-rate atom"

betaGammaKernelEdge : AttributedKernelEdge
betaGammaKernelEdge = mkKernelEdge Graph.betaGamma Sparse.betaGammaRate "beta->gamma Kramers-rate atom"

gammaDeltaKernelEdge : AttributedKernelEdge
gammaDeltaKernelEdge = mkKernelEdge Graph.gammaDelta Sparse.gammaDeltaRate "gamma->delta Kramers-rate atom"

deltaXiKernelEdge : AttributedKernelEdge
deltaXiKernelEdge = mkKernelEdge Graph.deltaXi Sparse.deltaXiRate "delta->terminal xi/zeta-role Kramers-rate atom"

betaEpsilonKernelEdge : AttributedKernelEdge
betaEpsilonKernelEdge = mkKernelEdge Graph.betaEpsilon Sparse.betaEpsilonRate "beta->epsilon Kramers-rate atom"

epsilonXiKernelEdge : AttributedKernelEdge
epsilonXiKernelEdge = mkKernelEdge Graph.epsilonXi Sparse.epsilonXiRate "epsilon->terminal xi/zeta-role Kramers-rate atom"

kernelEdges : List AttributedKernelEdge
kernelEdges =
  alphaBetaKernelEdge ∷
  betaGammaKernelEdge ∷
  gammaDeltaKernelEdge ∷
  deltaXiKernelEdge ∷
  betaEpsilonKernelEdge ∷
  epsilonXiKernelEdge ∷ []

------------------------------------------------------------------------
-- State-side calibration is retained as a separate fibre.  This prevents a
-- state energy/geometry coordinate from being mistaken for an edge rate.
------------------------------------------------------------------------

stateCalibrationCarrier :
  Sparse.CalibrationStateLabel → Sparse.StateCalibrationObservation
stateCalibrationCarrier = Sparse.stateCalibration

alphaThetaOneAttributed : Attr.CalibrationAtomEnvelope
alphaThetaOneAttributed = Attr.alphaThetaOneAtom

alphaThetaTwoAttributed : Attr.CalibrationAtomEnvelope
alphaThetaTwoAttributed = Attr.alphaThetaTwoAtom

gammaReferenceEnergyAttributed : Attr.CalibrationAtomEnvelope
gammaReferenceEnergyAttributed = Attr.gammaReferenceEnergyAtom

pathFluxObservation : Sparse.PathFluxObservation
pathFluxObservation = Sparse.primaryToAlternativeFlux

------------------------------------------------------------------------
-- Kernel status distinguishes structure from calibration completeness.
------------------------------------------------------------------------

record AttributedSparseTransitionKernel : Set where
  constructor attributed-sparse-transition-kernel
  field
    edges : List AttributedKernelEdge
    stateCalibration : Sparse.CalibrationStateLabel → Sparse.StateCalibrationObservation
    pathFlux : Sparse.PathFluxObservation
    topologyPaid : Bool
    exactPerEdgeNumericsPaid : Bool
    experimentalRateKernelPaid : Bool
    calibrationReading : String
open AttributedSparseTransitionKernel public

canonicalAttributedSparseTransitionKernel : AttributedSparseTransitionKernel
canonicalAttributedSparseTransitionKernel =
  attributed-sparse-transition-kernel
    kernelEdges
    stateCalibrationCarrier
    pathFluxObservation
    true
    false
    false
    "source-bounded six-edge topology with provenance-preserving sparse state/rate calibration; exact Kramers arrow numerics and experimental kinetic kernel remain unpaid"

------------------------------------------------------------------------
-- WrongType / same-object firewalls.
------------------------------------------------------------------------

data MissingRateMayBeDroppedFromKernel : Set where
data KramersKernelIsExperimentalKernel : Set where
data IdentityMetadataCreatesMissingNumbers : Set where
data PathFluxIsEdgeKernel : Set where
data StateEnergyIsEdgeRate : Set where

missingRateMustRemainRepresented : MissingRateMayBeDroppedFromKernel → ⊥
missingRateMustRemainRepresented ()

kramersKernelDoesNotBecomeExperimental : KramersKernelIsExperimentalKernel → ⊥
kramersKernelDoesNotBecomeExperimental ()

identityMetadataDoesNotPayNumericCell : IdentityMetadataCreatesMissingNumbers → ⊥
identityMetadataDoesNotPayNumericCell ()

pathFluxDoesNotBecomeEdgeKernel : PathFluxIsEdgeKernel → ⊥
pathFluxDoesNotBecomeEdgeKernel ()

stateEnergyDoesNotBecomeRate : StateEnergyIsEdgeRate → ⊥
stateEnergyDoesNotBecomeRate ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record AdKAttributedSparseKernelBoundary : Set where
  constructor adk-attributed-sparse-kernel-boundary
  field
    sixRouteEdgesRetained : Bool
    everyEdgeCarriesAttributionEnvelope : Bool
    kramersRateRoleRetained : Bool
    missingNumericRateRetained : Bool
    stateCalibrationFibreRetained : Bool
    relativeEnergyReferenceRetained : Bool
    endpointAnglesRetained : Bool
    kernelIsFullyNumericallyCalibrated : Bool
    kramersKernelEqualsExperimentalKernel : Bool
    identityMetadataCreatesMissingNumbers : Bool
    pathFluxEqualsEdgeKernel : Bool
    stateEnergyEqualsEdgeRate : Bool
    unresolvedArticleQidBlocksKernelTopology : Bool

canonicalAdKAttributedSparseKernelBoundary : AdKAttributedSparseKernelBoundary
canonicalAdKAttributedSparseKernelBoundary =
  adk-attributed-sparse-kernel-boundary
    true true true true
    true true true
    false false false false false false
