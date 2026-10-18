module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFigureSixPanelAVisualGeometryEnvelopeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFigureSixPanelCFullNumericAcquisitionExact as Full
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attribution
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCollectiveVariableDefinitionAcquisitionExact as CV
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAcquisitionFrontierExact as Frontier

------------------------------------------------------------------------
-- FIGURE-6A LIGAND-BOUND VISUAL GEOMETRY ENVELOPES
--
-- Source manifestation:
--   Li, Liu & Ji 2015, DOI 10.1016/j.bpj.2015.06.059,
--   supplied same-object PDF, Figure 6a, journal page 654.
--
-- Figure 6a visibly locates the eight ligand-bound named states on the same
-- theta1/theta2 observables defined by Figure 1.  This owner records only broad
-- visual axis envelopes.  It does not promote the plotted minima to exact
-- centroids and cannot pay dLN because dLN is not plotted in Figure 6a.
--
-- The ligand-bound state carrier is reused from the already-paid Figure-6c
-- numeric owner.  Same Greek letters across ligand-free and ligand-bound
-- contexts remain different source roles unless a separate same-object relation
-- is paid.
------------------------------------------------------------------------

record DegreeInterval : Set where
  constructor degree-interval
  field
    lower : Nat
    upper : Nat
open DegreeInterval public

record LigandBoundNamedStateVisualEnvelope : Set where
  constructor ligand-bound-named-state-visual-envelope
  field
    state : Full.LigandBoundFigureState
    thetaOneDegrees : DegreeInterval
    thetaTwoDegrees : DegreeInterval
    sourceLocator : String
    acquisitionRole : String
    exactThetaOneCellPaid : Bool
    exactThetaTwoCellPaid : Bool
    dLnCellPaid : Bool
open LigandBoundNamedStateVisualEnvelope public

figureSixPanelALocator : String
figureSixPanelALocator =
  "Li-Liu-Ji 2015, DOI 10.1016/j.bpj.2015.06.059, supplied same-object PDF Figure 6a, journal page 654; visual theta1/theta2 envelope"

-- Conservative visual boxes around the plotted labels/minima.  They intentionally
-- exceed apparent plotting precision rather than claiming exact graph extraction.

alphaLEnvelope : LigandBoundNamedStateVisualEnvelope
alphaLEnvelope = ligand-bound-named-state-visual-envelope
  Full.alphaL
  (degree-interval 94 100)
  (degree-interval 61 69)
  figureSixPanelALocator
  "ligand-bound alpha_L/open basin; visual interval only"
  false false false

betaLEnvelope : LigandBoundNamedStateVisualEnvelope
betaLEnvelope = ligand-bound-named-state-visual-envelope
  Full.betaL
  (degree-interval 82 91)
  (degree-interval 55 62)
  figureSixPanelALocator
  "ligand-bound beta_L intermediate; visual interval only"
  false false false

gammaLEnvelope : LigandBoundNamedStateVisualEnvelope
gammaLEnvelope = ligand-bound-named-state-visual-envelope
  Full.gammaL
  (degree-interval 66 75)
  (degree-interval 50 58)
  figureSixPanelALocator
  "ligand-bound gamma_L intermediate; visual interval only; gamma_L-near PDB references remain separate role evidence"
  false false false

deltaLEnvelope : LigandBoundNamedStateVisualEnvelope
deltaLEnvelope = ligand-bound-named-state-visual-envelope
  Full.deltaL
  (degree-interval 62 70)
  (degree-interval 37 43)
  figureSixPanelALocator
  "ligand-bound delta_L semi-open NMP intermediate; visual interval only"
  false false false

epsilonLEnvelope : LigandBoundNamedStateVisualEnvelope
epsilonLEnvelope = ligand-bound-named-state-visual-envelope
  Full.epsilonL
  (degree-interval 81 90)
  (degree-interval 40 47)
  figureSixPanelALocator
  "ligand-bound epsilon_L alternative-region intermediate; visual interval only"
  false false false

zetaLEnvelope : LigandBoundNamedStateVisualEnvelope
zetaLEnvelope = ligand-bound-named-state-visual-envelope
  Full.zetaL
  (degree-interval 61 69)
  (degree-interval 27 33)
  figureSixPanelALocator
  "ligand-bound zeta_L closed-state basin; visual interval only"
  false false false

muLEnvelope : LigandBoundNamedStateVisualEnvelope
muLEnvelope = ligand-bound-named-state-visual-envelope
  Full.muL
  (degree-interval 76 85)
  (degree-interval 26 32)
  figureSixPanelALocator
  "ligand-bound mu_L intermediate; visual interval only"
  false false false

lambdaLEnvelope : LigandBoundNamedStateVisualEnvelope
lambdaLEnvelope = ligand-bound-named-state-visual-envelope
  Full.lambdaL
  (degree-interval 59 66)
  (degree-interval 24 30)
  figureSixPanelALocator
  "ligand-bound lambda_L compact closed reference basin; visual interval only"
  false false false

figureSixVisualEnvelopes : List LigandBoundNamedStateVisualEnvelope
figureSixVisualEnvelopes =
  alphaLEnvelope ∷ betaLEnvelope ∷ gammaLEnvelope ∷ deltaLEnvelope ∷
  epsilonLEnvelope ∷ zetaLEnvelope ∷ muLEnvelope ∷ lambdaLEnvelope ∷ []

------------------------------------------------------------------------
-- Reused attribution / observable / frontier surfaces.
------------------------------------------------------------------------

articleAttributionBoundary : Attribution.AdKCalibrationAttributionBoundary
articleAttributionBoundary = Attribution.canonicalAdKCalibrationAttributionBoundary

collectiveVariableBoundary : CV.AdKCollectiveVariableDefinitionAcquisitionBoundary
collectiveVariableBoundary = CV.canonicalAdKCollectiveVariableDefinitionAcquisitionBoundary

priorAcquisitionFrontier : Frontier.AdKCalibrationAcquisitionFrontierBoundary
priorAcquisitionFrontier = Frontier.canonicalAdKCalibrationAcquisitionFrontierBoundary

figureSixNumericBoundary : Full.FigureSixPanelCFullNumericBoundary
figureSixNumericBoundary = Full.canonicalFigureSixPanelCFullNumericBoundary

------------------------------------------------------------------------
-- Promotion / attribution firewalls.
------------------------------------------------------------------------

data VisualEnvelopeCreatesExactNamedStatePoint : Set where
data FigureSixPanelACreatesDLnValue : Set where
data SameGreekLetterCreatesCrossContextStateIdentity : Set where
data AttributionIdentifierCreatesGeometryValue : Set where
data FigureSixGeometryCreatesExperimentalKinetics : Set where

visualEnvelopeDoesNotCreateExactNamedStatePoint :
  VisualEnvelopeCreatesExactNamedStatePoint → ⊥
visualEnvelopeDoesNotCreateExactNamedStatePoint ()

figureSixPanelADoesNotCreateDLnValue : FigureSixPanelACreatesDLnValue → ⊥
figureSixPanelADoesNotCreateDLnValue ()

sameGreekLetterDoesNotCreateCrossContextStateIdentity :
  SameGreekLetterCreatesCrossContextStateIdentity → ⊥
sameGreekLetterDoesNotCreateCrossContextStateIdentity ()

attributionIdentifierDoesNotCreateGeometryValue :
  AttributionIdentifierCreatesGeometryValue → ⊥
attributionIdentifierDoesNotCreateGeometryValue ()

figureGeometryDoesNotCreateExperimentalKinetics :
  FigureSixGeometryCreatesExperimentalKinetics → ⊥
figureGeometryDoesNotCreateExperimentalKinetics ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record AdKFigureSixPanelAVisualGeometryEnvelopeBoundary : Set where
  constructor adk-figure-six-panel-a-visual-geometry-envelope-boundary
  field
    sameArticleManifestation : Bool
    sameThetaObservableDefinition : Bool
    allEightLigandBoundStatesVisuallyLocated : Bool
    visualIntervalsNarrowGeometryDebt : Bool
    exactNamedThetaCellsPaid : Bool
    namedStateDLnCellsPaid : Bool
    visualReadoutPromotedToExactCentroid : Bool
    sameGreekLetterCreatesCrossContextStateIdentity : Bool
    qidDoiPdbUniProtCreateGeometryValue : Bool
    figureGeometryCreatesExperimentalKinetics : Bool
    figureSixEnergyRatePaymentsRemainSeparate : Bool
    nextResidual : String
open AdKFigureSixPanelAVisualGeometryEnvelopeBoundary public

canonicalAdKFigureSixPanelAVisualGeometryEnvelopeBoundary :
  AdKFigureSixPanelAVisualGeometryEnvelopeBoundary
canonicalAdKFigureSixPanelAVisualGeometryEnvelopeBoundary =
  adk-figure-six-panel-a-visual-geometry-envelope-boundary
    true true true true
    false false false false false false true
    "acquire exact same-object ligand-bound named-state theta1/theta2/dLN values only from an exact table or coordinate-bearing supplement manifestation. Figure-6a visual boxes are consistency/search envelopes; dLN remains outside this panel. Preserve ligand context, observable definition, source locator and DOI/QID/PDB/UniProt roles separately."
