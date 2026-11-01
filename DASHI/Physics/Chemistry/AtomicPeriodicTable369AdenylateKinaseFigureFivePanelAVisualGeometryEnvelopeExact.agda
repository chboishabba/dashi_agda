module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFigureFivePanelAVisualGeometryEnvelopeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSparseCalibrationFibreExact as Sparse
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attribution
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCollectiveVariableDefinitionAcquisitionExact as CV
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAcquisitionFrontierExact as Frontier

------------------------------------------------------------------------
-- FIGURE-5A VISUAL GEOMETRY ENVELOPES
--
-- The merged acquisition ledger already pays the Figure-5 panel-c energies and
-- Kramers-rate numerics.  The remaining apo named-state geometry debt is
-- theta1/theta2/dLN for beta/gamma/delta/epsilon/eta/lambda.
--
-- Figure 5a is a same-article, same-observable manifestation with named states
-- visibly positioned on theta1/theta2 axes.  This owner records deliberately
-- conservative visual axis envelopes.  They are *not* exact printed coordinate
-- values and therefore do not close the exact numeric ledger cells.
--
-- dLN is not plotted in Figure 5a and remains wholly outside this acquisition.
-- The Li-Liu-Ji DOI/PMID/PMCID/QID/UniProt/PDB attribution envelope and the
-- Figure-1 observable definitions are imported rather than restated.
------------------------------------------------------------------------

record DegreeInterval : Set where
  constructor degree-interval
  field
    lower : Nat
    upper : Nat
open DegreeInterval public

record NamedStateVisualEnvelope : Set where
  constructor named-state-visual-envelope
  field
    state : Sparse.CalibrationStateLabel
    thetaOneDegrees : DegreeInterval
    thetaTwoDegrees : DegreeInterval
    sourceLocator : String
    acquisitionRole : String
    exactThetaOneCellPaid : Bool
    exactThetaTwoCellPaid : Bool
    dLnCellPaid : Bool
open NamedStateVisualEnvelope public

-- Conservative panel-axis boxes.  These intentionally bracket the visibly
-- plotted labels/minima rather than pretending to recover exact centroids.
-- Endpoints alpha/zeta are included for consistency checks but their stronger
-- source-paid endpoint coordinates remain owned by the existing endpoint lane.

alphaEnvelope : NamedStateVisualEnvelope
alphaEnvelope = named-state-visual-envelope
  Sparse.alphaState
  (degree-interval 94 100)
  (degree-interval 60 68)
  "Li-Liu-Ji 2015 Figure 5a: alpha/open basin at upper-right of theta1/theta2 map"
  "visual axis envelope only; existing endpoint owner carries stronger open-state coordinates"
  false false false

betaEnvelope : NamedStateVisualEnvelope
betaEnvelope = named-state-visual-envelope
  Sparse.betaState
  (degree-interval 82 92)
  (degree-interval 57 64)
  "Li-Liu-Ji 2015 Figure 5a: beta named minimum on upper open-like valley"
  "same-object Figure-5a visual interval; not an exact printed theta coordinate"
  false false false

gammaEnvelope : NamedStateVisualEnvelope
gammaEnvelope = named-state-visual-envelope
  Sparse.gammaState
  (degree-interval 60 70)
  (degree-interval 55 63)
  "Li-Liu-Ji 2015 Figure 5a: gamma reference minimum in upper-left/intermediate valley"
  "same-object Figure-5a visual interval; gamma-near PDB references remain separate role evidence"
  false false false

deltaEnvelope : NamedStateVisualEnvelope
deltaEnvelope = named-state-visual-envelope
  Sparse.deltaState
  (degree-interval 64 75)
  (degree-interval 39 47)
  "Li-Liu-Ji 2015 Figure 5a: delta intermediate minimum"
  "same-object Figure-5a visual interval; not an exact state centroid"
  false false false

epsilonEnvelope : NamedStateVisualEnvelope
epsilonEnvelope = named-state-visual-envelope
  Sparse.epsilonState
  (degree-interval 82 92)
  (degree-interval 35 43)
  "Li-Liu-Ji 2015 Figure 5a: epsilon alternative-route intermediate minimum"
  "same-object Figure-5a visual interval; not an exact state centroid"
  false false false

etaEnvelope : NamedStateVisualEnvelope
etaEnvelope = named-state-visual-envelope
  Sparse.etaState
  (degree-interval 61 72)
  (degree-interval 27 35)
  "Li-Liu-Ji 2015 Figure 5a: eta near-closed minimum"
  "same-object Figure-5a visual interval; near-closed role remains qualitative beyond this plotted box"
  false false false

zetaEnvelope : NamedStateVisualEnvelope
zetaEnvelope = named-state-visual-envelope
  Sparse.zetaState
  (degree-interval 67 78)
  (degree-interval 24 32)
  "Li-Liu-Ji 2015 Figure 5a: zeta/closed basin near 1AKE"
  "visual axis envelope only; existing endpoint owner carries stronger closed-state coordinates"
  false false false

lambdaEnvelope : NamedStateVisualEnvelope
lambdaEnvelope = named-state-visual-envelope
  Sparse.lambdaState
  (degree-interval 90 100)
  (degree-interval 30 39)
  "Li-Liu-Ji 2015 Figure 5a: lambda near-closed right-hand basin"
  "same-object Figure-5a visual interval; not an exact state centroid"
  false false false

figureFiveVisualEnvelopes : List NamedStateVisualEnvelope
figureFiveVisualEnvelopes =
  alphaEnvelope ∷ betaEnvelope ∷ gammaEnvelope ∷ deltaEnvelope ∷
  epsilonEnvelope ∷ etaEnvelope ∷ zetaEnvelope ∷ lambdaEnvelope ∷ []

------------------------------------------------------------------------
-- Reused attribution / observable / frontier surfaces.
------------------------------------------------------------------------

articleAttributionBoundary : Attribution.AdKCalibrationAttributionBoundary
articleAttributionBoundary = Attribution.canonicalAdKCalibrationAttributionBoundary

collectiveVariableBoundary : CV.AdKCollectiveVariableDefinitionAcquisitionBoundary
collectiveVariableBoundary = CV.canonicalAdKCollectiveVariableDefinitionAcquisitionBoundary

priorAcquisitionFrontier : Frontier.AdKCalibrationAcquisitionFrontierBoundary
priorAcquisitionFrontier = Frontier.canonicalAdKCalibrationAcquisitionFrontierBoundary

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data VisualEnvelopeCreatesExactNamedStatePoint : Set where
data FigureFivePanelACreatesDLnValue : Set where
data SharedStateLabelCreatesObservableIdentity : Set where
data AttributionIdentifierCreatesGeometryValue : Set where

visualEnvelopeDoesNotCreateExactNamedStatePoint :
  VisualEnvelopeCreatesExactNamedStatePoint → ⊥
visualEnvelopeDoesNotCreateExactNamedStatePoint ()

figureFivePanelADoesNotCreateDLnValue : FigureFivePanelACreatesDLnValue → ⊥
figureFivePanelADoesNotCreateDLnValue ()

sharedLabelDoesNotCreateObservableIdentity :
  SharedStateLabelCreatesObservableIdentity → ⊥
sharedLabelDoesNotCreateObservableIdentity ()

attributionIdentifierDoesNotCreateGeometryValue :
  AttributionIdentifierCreatesGeometryValue → ⊥
attributionIdentifierDoesNotCreateGeometryValue ()

visualEnvelopeNarrowsButDoesNotPayExactPoint : Bool
visualEnvelopeNarrowsButDoesNotPayExactPoint = true

figureFivePanelADoesNotPayDLn : Bool
figureFivePanelADoesNotPayDLn = true

sameObservableDefinitionRetained : Bool
sameObservableDefinitionRetained = true

attributionEnvelopeRetained : Bool
attributionEnvelopeRetained = true

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record AdKFigureFivePanelAVisualGeometryEnvelopeBoundary : Set where
  constructor adk-figure-five-panel-a-visual-geometry-envelope-boundary
  field
    sameArticleManifestation : Bool
    sameThetaObservableDefinition : Bool
    allEightNamedStatesVisuallyLocated : Bool
    visualIntervalsNarrowGeometryDebt : Bool
    exactNamedThetaCellsPaid : Bool
    namedStateDLnCellsPaid : Bool
    visualReadoutPromotedToExactCentroid : Bool
    qidDoiPdbUniProtCreateGeometryValue : Bool
    priorFigureFiveEnergyRatePaymentsRemainClosed : Bool
    nextResidual : String
open AdKFigureFivePanelAVisualGeometryEnvelopeBoundary public

canonicalAdKFigureFivePanelAVisualGeometryEnvelopeBoundary :
  AdKFigureFivePanelAVisualGeometryEnvelopeBoundary
canonicalAdKFigureFivePanelAVisualGeometryEnvelopeBoundary =
  adk-figure-five-panel-a-visual-geometry-envelope-boundary
    true true true true
    false false false false true
    "acquire an exact same-object named-state theta1/theta2/dLN table or coordinate-bearing supplement manifestation if available. Figure-5a visual boxes narrow search/consistency bounds only. For dLN, request the exact same-object 3-CV/supplement panel or table; do not infer from theta1/theta2 or neighbouring states."
