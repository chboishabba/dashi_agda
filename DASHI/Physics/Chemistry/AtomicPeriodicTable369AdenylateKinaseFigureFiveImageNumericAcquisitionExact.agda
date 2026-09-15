module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFigureFiveImageNumericAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSparseCalibrationFibreExact as Sparse
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attr
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseGuardedCalibrationAcquisitionExact as Guard

------------------------------------------------------------------------
-- FIGURE-5 SOURCE-IMAGE NUMERIC ACQUISITION
--
-- This is the original narrow Figure-5 acquisition surface.  A later
-- full-resolution same-object readout made the sign convention unambiguous:
-- Figure 5 reports NONNEGATIVE relative free energies with gamma as the zero
-- reference minimum.  The earlier draft's minus signs on delta/eta/lambda were
-- a visual-reading error and are corrected here in append-only history.
--
-- The newer FullNumeric owner pays all eight state energies and twenty directed
-- Kramers arrow labels.  This owner remains as the narrow historical surface.
------------------------------------------------------------------------

source : Attribution.AttributedSource
source = Sparse.liLiuJi2015Source

sourceReceipt : Snowball.SourceRoleSnowballReceipt source
sourceReceipt = Snowball.canonicalSourceRoleSnowballReceipt source

attributionEnvelope = Attr.canonicalAdKCalibrationAttributionBoundary
acquisitionGuard = Guard.canonicalGuardedCalibrationAcquisitionBoundary

figureFiveImageLocator : String
figureFiveImageLocator =
  "PMC4572606 Figure 5 panel c / same-object source image; DOI 10.1016/j.bpj.2015.06.059"

data Sign : Set where
  nonnegative negative : Sign

record SignedTenthsKcalMol : Set where
  constructor signed-tenths-kcal-mol
  field
    sign : Sign
    magnitudeTenths : Nat
    printedReading : String
    sourceLocator : String
    acquisitionMethod : String
open SignedTenthsKcalMol public

gammaEnergy : SignedTenthsKcalMol
gammaEnergy = signed-tenths-kcal-mol
  nonnegative 0 "DeltaG = 0.0 kcal/mol" figureFiveImageLocator
  "direct same-object source-image readout"

deltaEnergy : SignedTenthsKcalMol
deltaEnergy = signed-tenths-kcal-mol
  nonnegative 6 "DeltaG = 0.6 kcal/mol" figureFiveImageLocator
  "direct same-object full-resolution source-image readout; corrects earlier sign misread"

etaEnergy : SignedTenthsKcalMol
etaEnergy = signed-tenths-kcal-mol
  nonnegative 7 "DeltaG = 0.7 kcal/mol" figureFiveImageLocator
  "direct same-object full-resolution source-image readout; corrects earlier sign misread"

lambdaEnergy : SignedTenthsKcalMol
lambdaEnergy = signed-tenths-kcal-mol
  nonnegative 10 "DeltaG = 1.0 kcal/mol" figureFiveImageLocator
  "direct same-object full-resolution source-image readout; corrects earlier sign misread"

record PrintedBidirectionalRatePair : Set where
  constructor printed-bidirectional-rate-pair
  field
    statePair : String
    firstPrintedRate : String
    secondPrintedRate : String
    displayUnit : String
    sourceLocator : String
    directionalAssignmentPaid : Bool
    interpretation : String
open PrintedBidirectionalRatePair public

gammaDeltaRatePair : PrintedBidirectionalRatePair
gammaDeltaRatePair = printed-bidirectional-rate-pair
  "gamma <-> delta" "2.66" "7.32" "10^-2 ns^-1"
  figureFiveImageLocator false
  "historical narrow acquisition retained the pair only; full-resolution owner now pays directions"

deltaEtaRatePair : PrintedBidirectionalRatePair
deltaEtaRatePair = printed-bidirectional-rate-pair
  "delta <-> eta" "2.84" "3.36" "10^-2 ns^-1"
  figureFiveImageLocator false
  "historical narrow acquisition retained the pair only; full-resolution owner now pays directions"

etaLambdaRatePair : PrintedBidirectionalRatePair
etaLambdaRatePair = printed-bidirectional-rate-pair
  "eta <-> lambda" "13.57" "22.51" "10^-2 ns^-1"
  figureFiveImageLocator false
  "historical narrow acquisition retained the pair only; full-resolution owner now pays directions"

------------------------------------------------------------------------
-- Attribution / payment firewall.
------------------------------------------------------------------------

data FigureImageCreatesUnseenCells : Set where
data PrintedRatePairCreatesDirectionalAssignment : Set where
data ImageReadoutCreatesExperimentalRate : Set where
data ArticleIdentityCreatesFigureValue : Set where

figureImageDoesNotCreateUnseenCells : FigureImageCreatesUnseenCells → ⊥
figureImageDoesNotCreateUnseenCells ()

printedPairDoesNotCreateDirection : PrintedRatePairCreatesDirectionalAssignment → ⊥
printedPairDoesNotCreateDirection ()

imageKramersReadoutDoesNotCreateExperimentalRate : ImageReadoutCreatesExperimentalRate → ⊥
imageKramersReadoutDoesNotCreateExperimentalRate ()

articleIdentityDoesNotCreateFigureValue : ArticleIdentityCreatesFigureValue → ⊥
articleIdentityDoesNotCreateFigureValue ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record AdKFigureFiveImageNumericAcquisitionBoundary : Set where
  constructor adk-figure-five-image-numeric-acquisition-boundary
  field
    sameArticleFigureManifestationPaid : Bool
    gammaEnergyImagePaid : Bool
    deltaEnergyImagePaid : Bool
    etaEnergyImagePaid : Bool
    lambdaEnergyImagePaid : Bool
    ratePairLabelsObserved : Bool
    directionalRateAssignmentPaid : Bool
    individualAlphaBetaEpsilonZetaImageCellsPaid : Bool
    imageReadoutCreatesExperimentalRate : Bool
    figureImageCreatesUnseenCells : Bool
    attributionEnvelopeRetained : Bool
    guardedAcquisitionRetained : Bool
    nextResidual : String
open AdKFigureFiveImageNumericAcquisitionBoundary public

canonicalAdKFigureFiveImageNumericAcquisitionBoundary :
  AdKFigureFiveImageNumericAcquisitionBoundary
canonicalAdKFigureFiveImageNumericAcquisitionBoundary =
  adk-figure-five-image-numeric-acquisition-boundary
    true
    true true true true
    true
    false
    false
    false
    false
    true
    true
    "superseded for completeness by FigureFivePanelCFullNumericAcquisitionExact; this narrow owner retains the corrected nonnegative relative-energy readings and historical pair-only acquisition strength"
