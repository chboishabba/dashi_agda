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
-- This owner pays only labels that are legible on the same-object NCBI/PMC
-- Figure-5 image for Li-Liu-Ji 2015.  It does not OCR the figure, infer hidden
-- labels, or assign a direction to paired arrow-rate numerals when the thumbnail
-- does not make the arrowhead/value association sufficiently unambiguous.
--
-- Source image:
--   PMC4572606 Figure 5 / gr5.jpg
--   https://cdn.ncbi.nlm.nih.gov/pmc/blobs/6169/4572606/85378128ea21/gr5.jpg
--
-- Clearly readable state-energy labels in panel c:
--   gamma  : DeltaG =  0.0 kcal/mol
--   delta  : DeltaG = -0.6 kcal/mol
--   eta    : DeltaG = -0.7 kcal/mol
--   lambda : DeltaG = -1.0 kcal/mol
--
-- Clearly readable paired Kramers-rate numerals are retained as pair labels,
-- not yet as directional edge payments:
--   gamma <-> delta  : 2.66 , 7.32
--   delta <-> eta    : 2.84 , 3.36
--   eta   <-> lambda : 13.57, 22.51
-- in the Figure-5 caption unit 10^-2 ns^-1.
------------------------------------------------------------------------

source : Attribution.AttributedSource
source = Sparse.liLiuJi2015Source

sourceReceipt : Snowball.SourceRoleSnowballReceipt source
sourceReceipt = Snowball.canonicalSourceRoleSnowballReceipt source

attributionEnvelope = Attr.canonicalAdKCalibrationAttributionBoundary
acquisitionGuard = Guard.canonicalGuardedCalibrationAcquisitionBoundary

figureFiveImageLocator : String
figureFiveImageLocator =
  "PMC4572606 Figure 5 panel c / NCBI source image gr5.jpg; DOI 10.1016/j.bpj.2015.06.059"

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
  "separately receipted direct source-image readout; not OCR inference"

deltaEnergy : SignedTenthsKcalMol
deltaEnergy = signed-tenths-kcal-mol
  negative 6 "DeltaG = -0.6 kcal/mol" figureFiveImageLocator
  "separately receipted direct source-image readout; not OCR inference"

etaEnergy : SignedTenthsKcalMol
etaEnergy = signed-tenths-kcal-mol
  negative 7 "DeltaG = -0.7 kcal/mol" figureFiveImageLocator
  "separately receipted direct source-image readout; not OCR inference"

lambdaEnergy : SignedTenthsKcalMol
lambdaEnergy = signed-tenths-kcal-mol
  negative 10 "DeltaG = -1.0 kcal/mol" figureFiveImageLocator
  "separately receipted direct source-image readout; not OCR inference"

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
  "both Figure-5 Kramers-derived numerals are legible; association of each numeral with the directed arrow remains unpaid in this acquisition"

deltaEtaRatePair : PrintedBidirectionalRatePair
deltaEtaRatePair = printed-bidirectional-rate-pair
  "delta <-> eta" "2.84" "3.36" "10^-2 ns^-1"
  figureFiveImageLocator false
  "both Figure-5 Kramers-derived numerals are legible; directional assignment remains unpaid"

etaLambdaRatePair : PrintedBidirectionalRatePair
etaLambdaRatePair = printed-bidirectional-rate-pair
  "eta <-> lambda" "13.57" "22.51" "10^-2 ns^-1"
  figureFiveImageLocator false
  "both Figure-5 Kramers-derived numerals are legible; directional assignment remains unpaid"

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
    "use the same-object full-resolution Figure-5 manifestation or supplement to pay direction-specific Kramers arrows and still-hidden alpha/beta/epsilon/zeta energy cells; do not infer them from the visible pair labels or DOI/QID/PDB identity"
