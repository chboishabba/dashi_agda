module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseNamedIntermediateGeometryConstraintAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attr
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseIntermediateGeometryTextAcquisitionExact as Region
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseNamedIntermediateRoleTextAcquisitionExact as Role
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationPaymentLedgerExact as Ledger

------------------------------------------------------------------------
-- NAMED-INTERMEDIATE GEOMETRY CONSTRAINT ACQUISITION
--
-- Li-Liu-Ji's machine-readable prose does not supply a locator-specific table
-- of (theta1, theta2, dLN) for beta/gamma/delta/epsilon/eta/lambda.  It does,
-- however, pay two independent kinds of information:
--
--   * named-state roles: gamma has LID closed/contacting NMP with NMP open;
--     delta has LID closed/contacting NMP with NMP semi-open;
--   * LT-MD region envelopes: intermediate structures have theta1 ~60--70 deg,
--     theta2 ~35--60 deg and dLN ~16--30 A; NMP semi-open theta2 ~35--45 deg.
--
-- This owner composes those same-article facts only into CONSTRAINTS.  It does
-- not upgrade any named-state numeric payment cell.  In particular, the source
-- does not say "delta theta2 = X" or "gamma dLN = Y" at an exact Figure-5
-- locator.  The composition is therefore DASHI synthesis over source-paid
-- premises, with the source retaining ownership of the premises only.
------------------------------------------------------------------------

source : Attribution.AttributedSource
source = Attr.liLiuJiSource

sourceReceipt : Snowball.SourceRoleSnowballReceipt source
sourceReceipt = Snowball.canonicalSourceRoleSnowballReceipt source

articleDOI = Attr.articleDOI
articlePMID = Attr.articlePMID
articlePMCID = Attr.articlePMCID
articleQID = Attr.articleQID
adkQID = Attr.adkQID
adkUniProt = Attr.adkUniProt

intermediateRegion = Region.ligandFreeIntermediateGeometryEnvelope
nmpSemiOpenThetaTwoRegion = Region.nmpSemiOpenThetaTwoEnvelope

gammaRole = Role.gammaRole
deltaRole = Role.deltaRole

data ConstraintStrength : Set where
  sourceRoleOnly : ConstraintStrength
  sourceRegionOnly : ConstraintStrength
  dashiComposedConstraint : ConstraintStrength
  exactNamedStateNumericValue : ConstraintStrength

record NamedGeometryConstraint : Set where
  constructor named-geometry-constraint
  field
    stateLabel : String
    thetaOneConstraint : String
    thetaTwoConstraint : String
    dLnConstraint : String
    sourceLocator : String
    sourcePremiseRole : String
    compositionRole : String
    strength : ConstraintStrength
    exactThetaOnePaid : Bool
    exactThetaTwoPaid : Bool
    exactDLnPaid : Bool
    updatesCalibrationLedgerCell : Bool
open NamedGeometryConstraint public

gammaGeometryConstraint : NamedGeometryConstraint
gammaGeometryConstraint = named-geometry-constraint
  "gamma"
  "DASHI-composed constraint only: gamma is source-described as LID closed/contacting NMP; ligand-free LT-MD intermediate structures occupy theta1 approximately 60--70 degrees. This does not assign a gamma-specific theta1 numeral."
  "source role only: gamma retains NMP-open status; no locator-specific gamma theta2 numeral or narrow named-state interval is acquired here"
  "DASHI-composed constraint only: gamma is a source-named intermediate and the ligand-free LT-MD intermediate region has dLN approximately 16--30 Angstrom. This is not a gamma-specific dLN payment."
  "PMC4572606 ligand-free transition prose + LT-MD intermediate-geometry text; Figure 5 names gamma but does not print a gamma geometry tuple"
  "Li-Liu-Ji pay the named gamma role and the separate LT-MD intermediate-region envelope"
  "DASHI composes role compatibility with the region envelope without claiming source authorship for that composition"
  dashiComposedConstraint
  false false false false

deltaGeometryConstraint : NamedGeometryConstraint
deltaGeometryConstraint = named-geometry-constraint
  "delta"
  "DASHI-composed constraint only: delta is source-described as LID closed/contacting NMP; ligand-free LT-MD intermediate structures occupy theta1 approximately 60--70 degrees. This does not assign a delta-specific theta1 numeral."
  "DASHI-composed constraint: delta is source-described as NMP semi-open and the same article reports the NMP semi-open theta2 region approximately 35--45 degrees. This is a named-role/range constraint, not an exact delta theta2 cell."
  "DASHI-composed constraint only: delta is a source-named intermediate and the ligand-free LT-MD intermediate region has dLN approximately 16--30 Angstrom. This is not a delta-specific dLN payment."
  "PMC4572606 ligand-free transition prose + LT-MD NMP-semi-open/intermediate-geometry text; Figure 5 names delta but does not print a delta geometry tuple"
  "Li-Liu-Ji pay the named delta role, NMP semi-open range, and separate LT-MD intermediate-region envelope"
  "DASHI composes those premises into a partial named-state constraint while leaving all exact named-state cells unpaid"
  dashiComposedConstraint
  false false false false

------------------------------------------------------------------------
-- The existing ledger stays authoritative for numeric payment state.
------------------------------------------------------------------------

gammaThetaOneCell = Ledger.gammaThetaOne
gammaThetaTwoCell = Ledger.gammaThetaTwo
gammaDLnCell = Ledger.gammaDLn
deltaThetaOneCell = Ledger.deltaThetaOne
deltaThetaTwoCell = Ledger.deltaThetaTwo
deltaDLnCell = Ledger.deltaDLn

gammaThetaOneRegionConstraintPaid : Bool
gammaThetaOneRegionConstraintPaid = true

gammaDLnRegionConstraintPaid : Bool
gammaDLnRegionConstraintPaid = true

deltaThetaOneRegionConstraintPaid : Bool
deltaThetaOneRegionConstraintPaid = true

deltaThetaTwoSemiOpenConstraintPaid : Bool
deltaThetaTwoSemiOpenConstraintPaid = true

deltaDLnRegionConstraintPaid : Bool
deltaDLnRegionConstraintPaid = true

namedStateExactThetaStillUnpaid : Bool
namedStateExactThetaStillUnpaid = true

namedStateExactDLnStillUnpaid : Bool
namedStateExactDLnStillUnpaid = true

ledgerCellsRemainUnchanged : Bool
ledgerCellsRemainUnchanged = true

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data ConstraintCreatesExactNamedValue : Set where
data RegionEnvelopeCreatesFigureFiveStateIdentity : Set where
data OpenRoleCreatesEndpointThetaValue : Set where
data DOIOrQidCreatesGeometryConstraint : Set where
data DashiCompositionTransfersSourceAuthorship : Set where

constraintDoesNotCreateExactNamedValue : ConstraintCreatesExactNamedValue → ⊥
constraintDoesNotCreateExactNamedValue ()

regionEnvelopeDoesNotCreateFigureFiveStateIdentity : RegionEnvelopeCreatesFigureFiveStateIdentity → ⊥
regionEnvelopeDoesNotCreateFigureFiveStateIdentity ()

openRoleDoesNotCreateEndpointThetaValue : OpenRoleCreatesEndpointThetaValue → ⊥
openRoleDoesNotCreateEndpointThetaValue ()

doiOrQidDoesNotCreateGeometryConstraint : DOIOrQidCreatesGeometryConstraint → ⊥
doiOrQidDoesNotCreateGeometryConstraint ()

dashiCompositionDoesNotTransferSourceAuthorship : DashiCompositionTransfersSourceAuthorship → ⊥
dashiCompositionDoesNotTransferSourceAuthorship ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record NamedIntermediateGeometryConstraintBoundary : Set where
  constructor named-intermediate-geometry-constraint-boundary
  field
    gammaThetaOneRegionConstraint : Bool
    gammaDLnRegionConstraint : Bool
    deltaThetaOneRegionConstraint : Bool
    deltaThetaTwoSemiOpenRangeConstraint : Bool
    deltaDLnRegionConstraint : Bool
    exactGammaGeometryTuplePaid : Bool
    exactDeltaGeometryTuplePaid : Bool
    exactNamedIntermediateDLnCellsPaid : Bool
    regionConstraintUpdatesNumericLedger : Bool
    regionEnvelopeCreatesFigureFiveStateIdentity : Bool
    doiQidUniProtCreateGeometry : Bool
    dashiCompositionTransfersSourceAuthorship : Bool
    attributionEnvelopeRetained : Bool
    nextResidual : String
open NamedIntermediateGeometryConstraintBoundary public

canonicalNamedIntermediateGeometryConstraintBoundary :
  NamedIntermediateGeometryConstraintBoundary
canonicalNamedIntermediateGeometryConstraintBoundary =
  named-intermediate-geometry-constraint-boundary
    true true true true true
    false false false false false false false
    true
    "acquire locator-specific named-state geometry if available. Current same-article text constrains gamma/delta through role-plus-region composition but does not pay beta/gamma/delta/epsilon/eta/lambda theta/dLN numeric cells. Preserve DOI/PMID/PMCID/QID/UniProt only as attribution and identity coordinates."
