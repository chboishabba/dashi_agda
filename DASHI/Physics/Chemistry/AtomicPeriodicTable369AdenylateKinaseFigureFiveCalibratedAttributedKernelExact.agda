module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFigureFiveCalibratedAttributedKernelExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseAttributedSparseTransitionKernelExact as SparseKernel
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSparseCalibrationFibreExact as Sparse
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFigureFivePanelCFullNumericAcquisitionExact as Full
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationPaymentLedgerExact as Ledger
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseMetadynamicsUncertaintyExact as Uncertainty

------------------------------------------------------------------------
-- FIGURE-5 CALIBRATED ATTRIBUTED KERNEL
--
-- The older attributed sparse kernel remains an append-only record of the state
-- before full-resolution Figure-5 acquisition.  This owner performs the missing
-- weld: each of its six source-route edges is retained together with the exact
-- same-object Figure-5 forward Kramers value now paid by Full.
--
-- The larger 20-directed-rate Figure-5 network and all eight relative energies
-- are retained alongside that six-edge route projection.  Nothing here promotes
-- Kramers-derived values to experimental kinetics, relative energies to absolute
-- thermodynamic energies, or equation-xi to Figure-zeta definitional identity.
------------------------------------------------------------------------

record CalibratedAttributedRouteEdge : Set where
  constructor calibrated-attributed-route-edge
  field
    attributedSparseEdge : SparseKernel.AttributedKernelEdge
    figureFiveRate : Full.DirectedKramersRate
    rateRole : String
    sameObjectNumericPayment : Bool
    experimentalRate : Bool
open CalibratedAttributedRouteEdge public

mkCalibratedRouteEdge :
  SparseKernel.AttributedKernelEdge →
  Full.DirectedKramersRate →
  String →
  CalibratedAttributedRouteEdge
mkCalibratedRouteEdge sparseEdge exactRate role =
  calibrated-attributed-route-edge
    sparseEdge exactRate role true false

alphaBetaCalibrated : CalibratedAttributedRouteEdge
alphaBetaCalibrated =
  mkCalibratedRouteEdge
    SparseKernel.alphaBetaKernelEdge
    Full.alphaBetaForward
    "alpha->beta; Figure-5 Kramers-derived rate, display unit 10^-2 ns^-1"

betaGammaCalibrated : CalibratedAttributedRouteEdge
betaGammaCalibrated =
  mkCalibratedRouteEdge
    SparseKernel.betaGammaKernelEdge
    Full.betaGammaForward
    "beta->gamma; Figure-5 Kramers-derived rate, display unit 10^-2 ns^-1"

gammaDeltaCalibrated : CalibratedAttributedRouteEdge
gammaDeltaCalibrated =
  mkCalibratedRouteEdge
    SparseKernel.gammaDeltaKernelEdge
    Full.gammaDeltaForward
    "gamma->delta; Figure-5 Kramers-derived rate, display unit 10^-2 ns^-1"

deltaTerminalCalibrated : CalibratedAttributedRouteEdge
deltaTerminalCalibrated =
  mkCalibratedRouteEdge
    SparseKernel.deltaXiKernelEdge
    Full.deltaTerminalForward
    "graph edge retains equation-xi notation history; paid Figure-5 rate is delta->zeta at shared terminal-route role; no xi=zeta definitional equality"

betaEpsilonCalibrated : CalibratedAttributedRouteEdge
betaEpsilonCalibrated =
  mkCalibratedRouteEdge
    SparseKernel.betaEpsilonKernelEdge
    Full.betaEpsilonForward
    "beta->epsilon; Figure-5 Kramers-derived rate, display unit 10^-2 ns^-1"

epsilonTerminalCalibrated : CalibratedAttributedRouteEdge
epsilonTerminalCalibrated =
  mkCalibratedRouteEdge
    SparseKernel.epsilonXiKernelEdge
    Full.epsilonTerminalForward
    "graph edge retains equation-xi notation history; paid Figure-5 rate is epsilon->zeta at shared terminal-route role; no xi=zeta definitional equality"

calibratedRouteEdges : List CalibratedAttributedRouteEdge
calibratedRouteEdges =
  alphaBetaCalibrated ∷
  betaGammaCalibrated ∷
  gammaDeltaCalibrated ∷
  deltaTerminalCalibrated ∷
  betaEpsilonCalibrated ∷
  epsilonTerminalCalibrated ∷ []

calibratedRouteEdgeCount : Nat
calibratedRouteEdgeCount = 6

------------------------------------------------------------------------
-- Full Figure-5 numeric surface retained beside the route projection.
------------------------------------------------------------------------

figureFiveStateEnergies : List Full.RelativeEnergyTenths
figureFiveStateEnergies = Full.stateEnergies

figureFiveDirectedRates : List Full.DirectedKramersRate
figureFiveDirectedRates = Full.directedRates

figureFiveStateEnergyCount : Nat
figureFiveStateEnergyCount = Full.stateEnergyCount

figureFiveDirectedRateCount : Nat
figureFiveDirectedRateCount = Full.directedRateCount

paymentLedger = Ledger.calibrationPaymentLedger
freeEnergyUncertainty = Uncertainty.canonicalFreeEnergyUncertaintyEnvelope

------------------------------------------------------------------------
-- Calibrated kernel object.
------------------------------------------------------------------------

record FigureFiveCalibratedAttributedKernel : Set where
  constructor figure-five-calibrated-attributed-kernel
  field
    sparseKernelHistory : SparseKernel.AttributedSparseTransitionKernel
    routeEdges : List CalibratedAttributedRouteEdge
    stateEnergies : List Full.RelativeEnergyTenths
    directedRates : List Full.DirectedKramersRate
    pathFlux : Sparse.PathFluxObservation
    exactFigureFiveStateEnergiesPaid : Bool
    exactFigureFiveDirectedRatesPaid : Bool
    exactSixForwardRouteRatesPaid : Bool
    kramersRateKindRetained : Bool
    relativeEnergyReferenceRetained : Bool
    terminalNotationHistoryRetained : Bool
    experimentalRateKernelPaid : Bool
    calibrationReading : String
open FigureFiveCalibratedAttributedKernel public

canonicalFigureFiveCalibratedAttributedKernel : FigureFiveCalibratedAttributedKernel
canonicalFigureFiveCalibratedAttributedKernel =
  figure-five-calibrated-attributed-kernel
    SparseKernel.canonicalAttributedSparseTransitionKernel
    calibratedRouteEdges
    figureFiveStateEnergies
    figureFiveDirectedRates
    SparseKernel.pathFluxObservation
    true true true true true true false
    "Figure-5 calibrated attributed kernel: eight relative-energy cells and twenty directed Kramers cells retained at source precision; six paid forward route cells enrich the pre-existing attributed route edges while Kramers-vs-experiment, relative-energy reference, and xi/zeta notation boundaries remain fail-closed"

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data KramersKernelBecomesExperimentalKernel : Set where
data RelativeEnergyBecomesAbsoluteEnergy : Set where
data FigureZetaBecomesEquationXi : Set where
data IdentityMetadataCreatesFigureNumerics : Set where
data PathFluxBecomesEdgeRate : Set where

kramersKernelDoesNotBecomeExperimental : KramersKernelBecomesExperimentalKernel → ⊥
kramersKernelDoesNotBecomeExperimental ()

relativeEnergyDoesNotBecomeAbsolute : RelativeEnergyBecomesAbsoluteEnergy → ⊥
relativeEnergyDoesNotBecomeAbsolute ()

figureZetaDoesNotBecomeEquationXi : FigureZetaBecomesEquationXi → ⊥
figureZetaDoesNotBecomeEquationXi ()

identityMetadataDoesNotCreateNumerics : IdentityMetadataCreatesFigureNumerics → ⊥
identityMetadataDoesNotCreateNumerics ()

pathFluxDoesNotBecomeEdgeRate : PathFluxBecomesEdgeRate → ⊥
pathFluxDoesNotBecomeEdgeRate ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record FigureFiveCalibratedAttributedKernelBoundary : Set where
  constructor figure-five-calibrated-attributed-kernel-boundary
  field
    sparseAttributedHistoryRetained : Bool
    sixAttributedRouteEdgesCalibrated : Bool
    allEightStateEnergiesRetained : Bool
    allTwentyDirectedRatesRetained : Bool
    kramersRateKindRetainedBoundary : Bool
    relativeEnergyReferenceRetainedBoundary : Bool
    metadynamicsUncertaintyEnvelopeRetained : Bool
    paymentLedgerRetained : Bool
    figureZetaEqualsEquationXi : Bool
    kramersKernelEqualsExperimentalKernel : Bool
    relativeEnergyEqualsAbsoluteThermodynamicEnergy : Bool
    identityMetadataCreatesNumericCells : Bool
    pathFluxEqualsEdgeRate : Bool
open FigureFiveCalibratedAttributedKernelBoundary public

canonicalFigureFiveCalibratedAttributedKernelBoundary :
  FigureFiveCalibratedAttributedKernelBoundary
canonicalFigureFiveCalibratedAttributedKernelBoundary =
  figure-five-calibrated-attributed-kernel-boundary
    true true true true true true true true
    false false false false false
