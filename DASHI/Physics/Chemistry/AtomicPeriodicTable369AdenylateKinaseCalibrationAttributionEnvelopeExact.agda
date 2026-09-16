module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSparseCalibrationFibreExact as Sparse

------------------------------------------------------------------------
-- CALIBRATION ATTRIBUTION ENVELOPE
--
-- This owner does not invent an AdK-specific bibliography or QID calculus.
-- It reuses AttributedSourceCore + source-role snowball + external-identity
-- availability and binds those objects directly to sparse calibration atoms.
--
-- DOI/PMID/PMCID/OpenAlex/QID/PDB/UniProt are identity/provenance coordinates.
-- They do not pay a numeric value, a same-object state alignment, a kinetic
-- interpretation, or scientific authority.  Unresolved identities remain typed.
------------------------------------------------------------------------

liLiuJiSource : Attribution.AttributedSource
liLiuJiSource = Sparse.liLiuJi2015Source

liLiuJiSourceRoleReceipt : Snowball.SourceRoleSnowballReceipt liLiuJiSource
liLiuJiSourceRoleReceipt = Snowball.canonicalSourceRoleSnowballReceipt liLiuJiSource

------------------------------------------------------------------------
-- Publication/entity identity demands.
------------------------------------------------------------------------

articleDOI : Identity.ExternalIdentityDemand
articleDOI =
  Identity.mkOptionalIdentityDemand
    "AdK calibration attribution envelope"
    "Li Liu Ji 2015 DOI"
    "Mapping the Dynamics Landscape of Conformational Transitions in Enzyme: The Adenylate Kinase Case"
    Identity.doi
    (Identity.verified "DOI / PubMed article record" "10.1016/j.bpj.2015.06.059")

articlePMID : Identity.ExternalIdentityDemand
articlePMID =
  Identity.mkOptionalIdentityDemand
    "AdK calibration attribution envelope"
    "Li Liu Ji 2015 PubMed identifier"
    "Mapping the Dynamics Landscape of Conformational Transitions in Enzyme: The Adenylate Kinase Case"
    Identity.officialIdentifier
    (Identity.verified "PubMed" "26244746")

articlePMCID : Identity.ExternalIdentityDemand
articlePMCID =
  Identity.mkOptionalIdentityDemand
    "AdK calibration attribution envelope"
    "Li Liu Ji 2015 PubMed Central identifier"
    "Mapping the Dynamics Landscape of Conformational Transitions in Enzyme: The Adenylate Kinase Case"
    Identity.officialIdentifier
    (Identity.verified "PubMed Central" "PMC4572606")

articleOpenAlex : Identity.ExternalIdentityDemand
articleOpenAlex =
  Identity.mkOptionalIdentityDemand
    "AdK calibration attribution envelope"
    "Li Liu Ji 2015 OpenAlex work identity"
    "Mapping the Dynamics Landscape of Conformational Transitions in Enzyme: The Adenylate Kinase Case"
    Identity.officialIdentifier
    (Identity.verified "OpenAlex inspected 2026-09-15" "W1506211024")

articleQID : Identity.ExternalIdentityDemand
articleQID = Sparse.liLiuJiArticleQid

adkQID : Identity.ExternalIdentityDemand
adkQID = Sparse.adkQid

adkUniProt : Identity.ExternalIdentityDemand
adkUniProt = Sparse.uniprotP69441

openPDB : Identity.ExternalIdentityDemand
openPDB = Sparse.pdb4AKE

closedPDB : Identity.ExternalIdentityDemand
closedPDB = Sparse.pdb1AKE

calibrationIdentityDemands : List Identity.ExternalIdentityDemand
calibrationIdentityDemands =
  articleDOI ∷
  articlePMID ∷
  articlePMCID ∷
  articleOpenAlex ∷
  articleQID ∷
  adkQID ∷
  adkUniProt ∷
  openPDB ∷
  closedPDB ∷ []

------------------------------------------------------------------------
-- Every numerical atom carries the source + source-role receipt + identity
-- bundle + the numeric coordinate's own source locator/method/uncertainty.
------------------------------------------------------------------------

record CalibrationAtomEnvelope : Set where
  constructor calibration-atom-envelope
  field
    atomLabel : String
    coordinate : Sparse.SparseNumericCoordinate
    source : Attribution.AttributedSource
    sourceRoleReceipt : Snowball.SourceRoleSnowballReceipt source
    identityDemands : List Identity.ExternalIdentityDemand
    sourceLocator : String
    methodRole : String
    formalisationRole : String
open CalibrationAtomEnvelope public

mkLiLiuJiAtom :
  String → Sparse.SparseNumericCoordinate → String → String →
  CalibrationAtomEnvelope
mkLiLiuJiAtom label coordinate methodRole formalisationRole =
  calibration-atom-envelope
    label
    coordinate
    liLiuJiSource
    liLiuJiSourceRoleReceipt
    calibrationIdentityDemands
    (Sparse.sourceLocator coordinate)
    methodRole
    formalisationRole

alphaThetaOneAtom : CalibrationAtomEnvelope
alphaThetaOneAtom =
  mkLiLiuJiAtom
    "alpha theta1 endpoint"
    (Sparse.thetaOneDegrees (Sparse.stateCalibration Sparse.alphaState))
    "composed source facts"
    "DASHI composes source-paid alpha/open identity with separately source-paid open theta1; identity coordinates do not create the value"

alphaThetaTwoAtom : CalibrationAtomEnvelope
alphaThetaTwoAtom =
  mkLiLiuJiAtom
    "alpha theta2 endpoint"
    (Sparse.thetaTwoDegrees (Sparse.stateCalibration Sparse.alphaState))
    "composed source facts"
    "DASHI composes source-paid alpha/open identity with separately source-paid open theta2"

gammaReferenceEnergyAtom : CalibrationAtomEnvelope
gammaReferenceEnergyAtom =
  mkLiLiuJiAtom
    "gamma relative-free-energy zero reference"
    (Sparse.relativeFreeEnergyTenthsKcalMol (Sparse.stateCalibration Sparse.gammaState))
    "source text / existing graph receipt"
    "retains source zero-reference convention; does not promote to absolute thermodynamic free energy"

alphaBetaRateAtom : CalibrationAtomEnvelope
alphaBetaRateAtom =
  mkLiLiuJiAtom
    "alpha->beta Kramers-rate coordinate"
    (Sparse.rate Sparse.alphaBetaRate)
    "Kramers-derived Figure-5 rate role"
    "the rate coordinate is attributable even while the exact numeric label remains unpaid"

------------------------------------------------------------------------
-- Explicit WrongType firewalls.
------------------------------------------------------------------------

data QidCreatesScientificAuthority : Set where
data DoiCreatesScientificAuthority : Set where
data ExternalIdentityCreatesNumericPayment : Set where
data SameIdentifierCreatesSameRole : Set where

data UnpaidCoordinateLosesAttribution : Set where

qidDoesNotCreateScientificAuthority : QidCreatesScientificAuthority → ⊥
qidDoesNotCreateScientificAuthority ()

doiDoesNotCreateScientificAuthority : DoiCreatesScientificAuthority → ⊥
doiDoesNotCreateScientificAuthority ()

identityDoesNotPayNumber : ExternalIdentityCreatesNumericPayment → ⊥
identityDoesNotPayNumber ()

sameIdentifierDoesNotCollapseRole : SameIdentifierCreatesSameRole → ⊥
sameIdentifierDoesNotCollapseRole ()

unpaidCoordinateStillHasSource : UnpaidCoordinateLosesAttribution → ⊥
unpaidCoordinateStillHasSource ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record AdKCalibrationAttributionBoundary : Set where
  constructor adk-calibration-attribution-boundary
  field
    doiRetained : Bool
    pmidRetained : Bool
    pmcidRetained : Bool
    openAlexRetained : Bool
    articleQidExplicitlyUnresolved : Bool
    adkQidRetained : Bool
    uniprotRetained : Bool
    pdbEndpointsRetained : Bool
    numericAtomCarriesSource : Bool
    numericAtomCarriesLocator : Bool
    numericAtomCarriesMethodRole : Bool
    unpaidAtomRemainsAttributable : Bool
    qidCreatesScientificAuthority : Bool
    doiCreatesScientificAuthority : Bool
    identityEqualityCreatesNumericPayment : Bool
    identifierEqualityCollapsesSourceRole : Bool

canonicalAdKCalibrationAttributionBoundary : AdKCalibrationAttributionBoundary
canonicalAdKCalibrationAttributionBoundary =
  adk-calibration-attribution-boundary
    true true true true true true true true
    true true true true
    false false false false
