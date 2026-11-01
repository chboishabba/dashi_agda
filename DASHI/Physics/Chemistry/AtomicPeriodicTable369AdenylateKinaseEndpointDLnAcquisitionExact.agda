module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseEndpointDLnAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSparseCalibrationFibreExact as Sparse
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attr
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseStructuralIdentitySnowballExact as Structural

------------------------------------------------------------------------
-- ENDPOINT dLN ACQUISITION
--
-- Li, Liu & Ji's article text explicitly reports the LID--NMP centre-of-mass
-- distance for the open and closed crystal references:
--   dLN^O ≈ 38 A in PDB 4AKE
--   dLN^C ≈ 20 A in PDB 1AKE.
--
-- This pays two endpoint numeric cells directly from the article text.  It does
-- not pay a complete named-state dLN table for beta/gamma/delta/epsilon/eta/
-- lambda, and it does not turn a PDB/UniProt/QID identity into a numeric fact.
------------------------------------------------------------------------

source : Attribution.AttributedSource
source = Sparse.liLiuJi2015Source

sourceReceipt : Snowball.SourceRoleSnowballReceipt source
sourceReceipt = Snowball.canonicalSourceRoleSnowballReceipt source

articleDOI : Identity.ExternalIdentityDemand
articleDOI = Attr.articleDOI

articlePMID : Identity.ExternalIdentityDemand
articlePMID = Attr.articlePMID

articlePMCID : Identity.ExternalIdentityDemand
articlePMCID = Attr.articlePMCID

articleQID : Identity.ExternalIdentityDemand
articleQID = Attr.articleQID

adkQID : Identity.ExternalIdentityDemand
adkQID = Structural.adkQid

adkUniProt : Identity.ExternalIdentityDemand
adkUniProt = Structural.adkUniProt

openPdbDOI : Identity.ExternalIdentityDemand
openPdbDOI = Structural.openPdbDoi

closedPdbDOI : Identity.ExternalIdentityDemand
closedPdbDOI = Structural.closedPdbDoi

openPdbObjectQID : Identity.ExternalIdentityDemand
openPdbObjectQID = Structural.openPdbObjectQid

closedPdbObjectQID : Identity.ExternalIdentityDemand
closedPdbObjectQID = Structural.closedPdbObjectQid

openEndpointDLnAngstrom : Nat
openEndpointDLnAngstrom = 38

closedEndpointDLnAngstrom : Nat
closedEndpointDLnAngstrom = 20

openEndpointPdbLabel : String
openEndpointPdbLabel = "4AKE"

closedEndpointPdbLabel : String
closedEndpointPdbLabel = "1AKE"

openEndpointDLnCoordinate : Sparse.SparseNumericCoordinate
openEndpointDLnCoordinate =
  Sparse.paidCoordinate
    openEndpointDLnAngstrom
    "angstrom"
    "Li-Liu-Ji 2015 Materials and Methods / conformational-transition variables: dLN^O approximately 38 A in PDB 4AKE"
    "source reports approximate endpoint value"
    Sparse.sourceTextReadout

closedEndpointDLnCoordinate : Sparse.SparseNumericCoordinate
closedEndpointDLnCoordinate =
  Sparse.paidCoordinate
    closedEndpointDLnAngstrom
    "angstrom"
    "Li-Liu-Ji 2015 Materials and Methods / conformational-transition variables: dLN^C approximately 20 A in PDB 1AKE"
    "source reports approximate endpoint value"
    Sparse.sourceTextReadout

openEndpointDLnAtom : Attr.CalibrationAtomEnvelope
openEndpointDLnAtom =
  Attr.mkLiLiuJiAtom
    "open endpoint dLN / 4AKE"
    openEndpointDLnCoordinate
    "article-text endpoint geometry readout"
    "approximately 38 A; same article DOI/PMID/PMCID retained; PDB/UniProt/QID remain identity coordinates"

closedEndpointDLnAtom : Attr.CalibrationAtomEnvelope
closedEndpointDLnAtom =
  Attr.mkLiLiuJiAtom
    "closed endpoint dLN / 1AKE"
    closedEndpointDLnCoordinate
    "article-text endpoint geometry readout"
    "approximately 20 A; same article DOI/PMID/PMCID retained; PDB/UniProt/QID remain identity coordinates"

record EndpointDLnAcquisition : Set where
  constructor endpoint-dln-acquisition
  field
    endpointRole : String
    pdbLabel : String
    pdbSource : Attribution.AttributedSource
    proteinIdentity : Identity.ExternalIdentityDemand
    enzymeIdentity : Identity.ExternalIdentityDemand
    articleIdentity : Attribution.AttributedSource
    numericAtom : Attr.CalibrationAtomEnvelope
    interpretation : String
open EndpointDLnAcquisition public

openEndpointDLnAcquisition : EndpointDLnAcquisition
openEndpointDLnAcquisition = endpoint-dln-acquisition
  "open structural endpoint"
  openEndpointPdbLabel
  Structural.open4AKESource
  adkUniProt
  adkQID
  source
  openEndpointDLnAtom
  "source-text dLN endpoint tied to the open 4AKE structural reference; not a universal open-state distance"

closedEndpointDLnAcquisition : EndpointDLnAcquisition
closedEndpointDLnAcquisition = endpoint-dln-acquisition
  "closed structural endpoint"
  closedEndpointPdbLabel
  Structural.closed1AKESource
  adkUniProt
  adkQID
  source
  closedEndpointDLnAtom
  "source-text dLN endpoint tied to the closed 1AKE structural reference; not a universal closed-state distance"

------------------------------------------------------------------------
-- WrongType / promotion firewalls.
------------------------------------------------------------------------

data EndpointValuesCreateIntermediateDLnTable : Set where
data IdentityMetadataCreatesEndpointDLn : Set where
data ApproximateEndpointValueBecomesExactPhysicalTruth : Set where
data SameProteinCreatesSameConformation : Set where

endpointValuesDoNotCreateIntermediateTable : EndpointValuesCreateIntermediateDLnTable → ⊥
endpointValuesDoNotCreateIntermediateTable ()

identityMetadataDoesNotCreateEndpointDLn : IdentityMetadataCreatesEndpointDLn → ⊥
identityMetadataDoesNotCreateEndpointDLn ()

approximateValueDoesNotBecomeExactPhysicalTruth : ApproximateEndpointValueBecomesExactPhysicalTruth → ⊥
approximateValueDoesNotBecomeExactPhysicalTruth ()

sameProteinDoesNotCreateSameConformation : SameProteinCreatesSameConformation → ⊥
sameProteinDoesNotCreateSameConformation ()

record EndpointDLnAcquisitionBoundary : Set where
  constructor endpoint-dln-acquisition-boundary
  field
    openEndpointDLnPaid : Bool
    closedEndpointDLnPaid : Bool
    endpointValuesBoundToArticleText : Bool
    endpointValuesBoundToPdbRoles : Bool
    articleDoiPmidPmcidRetained : Bool
    articleQidResolved : Bool
    adkQidRetained : Bool
    uniprotRetained : Bool
    exactPdbObjectQidsResolved : Bool
    namedIntermediateDLnTablePaid : Bool
    endpointValuesCreateIntermediateDLnTable : Bool
    identityMetadataCreatesEndpointDLn : Bool
    approximateEndpointPromotedToExactPhysicalTruth : Bool
open EndpointDLnAcquisitionBoundary public

canonicalEndpointDLnAcquisitionBoundary : EndpointDLnAcquisitionBoundary
canonicalEndpointDLnAcquisitionBoundary = endpoint-dln-acquisition-boundary
  true true true true true
  false true true false
  false false false false

namedIntermediateDLnTablePaid : Bool
namedIntermediateDLnTablePaid = false

endpointValuesCreateIntermediateDLnTable : Bool
endpointValuesCreateIntermediateDLnTable = false

identityMetadataCreatesEndpointDLn : Bool
identityMetadataCreatesEndpointDLn = false
