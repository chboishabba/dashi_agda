module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseLigandBoundPartialCalibrationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSparseCalibrationFibreExact as Sparse
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attr
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFigureSixPanelCFullNumericAcquisitionExact as Fig6
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseLigandBoundGeometryTextAcquisitionExact as Geometry
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseGammaLCrystalReferenceAcquisitionExact as GammaLRefs

------------------------------------------------------------------------
-- LIGAND-BOUND PARTIAL CALIBRATION TABLE
--
-- This owner composes independently paid source surfaces:
--   * exact printed Figure-6 state relative energies;
--   * exact printed Figure-6 directed Kramers labels;
--   * machine-readable ligand-bound geometry/route constraints;
--   * separately attributed 1DVR/2C9Y gamma_L-near structural references.
--
-- Composition is DASHI synthesis.  It does not upgrade missing theta/dLN cells.
------------------------------------------------------------------------

source : Attribution.AttributedSource
source = Sparse.liLiuJi2015Source

sourceReceipt : Snowball.SourceRoleSnowballReceipt source
sourceReceipt = Snowball.canonicalSourceRoleSnowballReceipt source

attributionEnvelope = Attr.canonicalAdKCalibrationAttributionBoundary

------------------------------------------------------------------------
-- State table.
------------------------------------------------------------------------

data LigandBoundCalibrationState : Set where
  alphaL betaL gammaL deltaL epsilonL zetaL muL lambdaL : LigandBoundCalibrationState

record LigandBoundStateCalibration : Set where
  constructor ligand-bound-state-calibration
  field
    state : LigandBoundCalibrationState
    relativeEnergyTenthsKcalMol : Nat
    energyPrintedReading : String
    thetaOneRole : String
    thetaTwoRole : String
    dLnRole : String
    geometryPayment : String
    sourceLocator : String
open LigandBoundStateCalibration public

stateCalibration : LigandBoundCalibrationState → LigandBoundStateCalibration
stateCalibration alphaL = ligand-bound-state-calibration
  alphaL 80 "DeltaG = 8.0 kcal/mol"
  "open endpoint/ligand-bound route start; no exact alpha_L theta1 value imported here beyond separately paid source context"
  "open endpoint/ligand-bound route start; no exact alpha_L theta2 value imported here beyond separately paid source context"
  "named-state dLN unpaid"
  "route membership paid; exact named-state geometry not paid by this table"
  "Figure 6 panel c + ligand-bound metadynamics prose"
stateCalibration betaL = ligand-bound-state-calibration
  betaL 37 "DeltaG = 3.7 kcal/mol"
  "exact beta_L theta1 unpaid"
  "exact beta_L theta2 unpaid"
  "exact beta_L dLN unpaid"
  "intermediate role paid; exact coordinates unpaid"
  "Figure 6 panel c + ligand-bound metadynamics prose"
stateCalibration gammaL = ligand-bound-state-calibration
  gammaL 28 "DeltaG = 2.8 kcal/mol"
  "exact gamma_L theta1 unpaid"
  "exact gamma_L theta2 unpaid"
  "exact gamma_L dLN unpaid"
  "two cross-species crystal structures are reported near gamma_L under theta1/theta2 projection; proximity does not invert to exact coordinates"
  "Figure 6 panel c + Figure 6a/prose + 1DVR/2C9Y reference snowball"
stateCalibration deltaL = ligand-bound-state-calibration
  deltaL 8 "DeltaG = 0.8 kcal/mol"
  "exact delta_L theta1 unpaid"
  "exact delta_L theta2 unpaid"
  "exact delta_L dLN unpaid"
  "source classifies delta_L as NMP semi-open; exact coordinates unpaid"
  "Figure 6 panel c + ligand-bound metadynamics prose"
stateCalibration epsilonL = ligand-bound-state-calibration
  epsilonL 41 "DeltaG = 4.1 kcal/mol"
  "exact epsilon_L theta1 unpaid"
  "exact epsilon_L theta2 unpaid"
  "exact epsilon_L dLN unpaid"
  "source reports one crystal structure near epsilon_L but inspected machine-readable text does not identify that PDB object"
  "Figure 6 panel c + ligand-bound metadynamics prose"
stateCalibration zetaL = ligand-bound-state-calibration
  zetaL 9 "DeltaG = 0.9 kcal/mol"
  "closed-state role; most ligand-bound crystal structures cluster near theta1 approximately 65 degrees, but cluster center is not exact zeta_L coordinate"
  "closed-state role; most ligand-bound crystal structures cluster near theta2 approximately 28 degrees, but cluster center is not exact zeta_L coordinate"
  "exact zeta_L dLN unpaid"
  "closed-role and cluster-level geometry paid; exact named-state point remains unpaid"
  "Figure 6 panel c + ligand-bound metadynamics prose"
stateCalibration muL = ligand-bound-state-calibration
  muL 33 "DeltaG = 3.3 kcal/mol"
  "exact mu_L theta1 unpaid"
  "exact mu_L theta2 unpaid"
  "exact mu_L dLN unpaid"
  "intermediate role paid; exact coordinates unpaid"
  "Figure 6 panel c"
stateCalibration lambdaL = ligand-bound-state-calibration
  lambdaL 0 "DeltaG = 0.0 kcal/mol"
  "exact lambda_L theta1 unpaid"
  "exact lambda_L theta2 unpaid"
  "exact lambda_L dLN unpaid"
  "reference-minimum role paid; exact coordinates unpaid"
  "Figure 6 panel c / caption reference minimum"

------------------------------------------------------------------------
-- Directed-rate table is reused verbatim from the paid Figure-6 acquisition.
------------------------------------------------------------------------

directedRates : List Fig6.DirectedKramersRate
directedRates = Fig6.directedRates

allEightEnergiesPaid : Bool
allEightEnergiesPaid = Fig6.allEightStateEnergiesPaid

allSixteenRatesPaid : Bool
allSixteenRatesPaid = Fig6.allDirectedRateLabelsPaid

closedClusterGeometryPaid : Bool
closedClusterGeometryPaid = true

gammaLExactGeometryPaid : Bool
gammaLExactGeometryPaid = false

namedIntermediateDLnPaid : Bool
namedIntermediateDLnPaid = false

oneDVRNearGammaL = GammaLRefs.oneDVRReference
twoC9YNearGammaL = GammaLRefs.twoC9YReference

------------------------------------------------------------------------
-- WrongType / composition firewalls.
------------------------------------------------------------------------

data PaidEnergyCreatesPaidGeometry : Set where
data PaidRateCreatesExperimentalKinetics : Set where
data ClosedClusterCenterEqualsZetaLPoint : Set where
data NearGammaLStructureCreatesGammaLPoint : Set where
data SameGreekLetterAcrossContextsCreatesIdentity : Set where

data CompositionTransfersSourceAuthorship : Set where

paidEnergyDoesNotCreateGeometry : PaidEnergyCreatesPaidGeometry → ⊥
paidEnergyDoesNotCreateGeometry ()

paidKramersRateDoesNotCreateExperimentalKinetics : PaidRateCreatesExperimentalKinetics → ⊥
paidKramersRateDoesNotCreateExperimentalKinetics ()

closedClusterCenterDoesNotEqualZetaLPoint : ClosedClusterCenterEqualsZetaLPoint → ⊥
closedClusterCenterDoesNotEqualZetaLPoint ()

nearGammaLStructureDoesNotCreateGammaLPoint : NearGammaLStructureCreatesGammaLPoint → ⊥
nearGammaLStructureDoesNotCreateGammaLPoint ()

sameGreekLetterDoesNotCreateCrossContextIdentity : SameGreekLetterAcrossContextsCreatesIdentity → ⊥
sameGreekLetterDoesNotCreateCrossContextIdentity ()

compositionDoesNotTransferSourceAuthorship : CompositionTransfersSourceAuthorship → ⊥
compositionDoesNotTransferSourceAuthorship ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record LigandBoundPartialCalibrationBoundary : Set where
  constructor ligand-bound-partial-calibration-boundary
  field
    eightRelativeEnergyCellsPaid : Bool
    sixteenKramersRateCellsPaid : Bool
    closedClusterApprox65_28Paid : Bool
    nmpFirstUnfavourableApprox90_30Paid : Bool
    gammaLCrystalNeighbourRolePaid : Bool
    gammaLExactThetaPointPaid : Bool
    namedIntermediateDLnTablePaid : Bool
    kramersRatesEqualExperimentalRates : Bool
    stateEnergyCreatesGeometry : Bool
    closedClusterEqualsZetaLExactPoint : Bool
    nearGammaLReferenceEqualsGammaL : Bool
    sourceOwnsDashiComposition : Bool
    nextResidual : String
open LigandBoundPartialCalibrationBoundary public

canonicalLigandBoundPartialCalibrationBoundary : LigandBoundPartialCalibrationBoundary
canonicalLigandBoundPartialCalibrationBoundary = ligand-bound-partial-calibration-boundary
  true true true true true
  false false false false false false false
  "next same-object acquisition targets are exact named-state theta/dLN cells and the identity of the crystal reported near epsilon_L. Keep Figure-6 energies/rates paid independently from geometry, and retain all PDB/DOI/PMID/UniProt/QID source roles without using identity metadata to fill missing coordinates."
