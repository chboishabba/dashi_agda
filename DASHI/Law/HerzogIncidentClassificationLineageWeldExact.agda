module DASHI.Law.HerzogIncidentClassificationLineageWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Law.DisclosureReadyClassificationInputAtomExact as Atom
import DASHI.Law.HerzogConcreteIncidentHypervoxelExact as Incident

------------------------------------------------------------------------
-- Same-object weld from a disclosed input atom to one concrete incident.
------------------------------------------------------------------------

data IncidentLinkClosure : Set where
  incidentLinkClosed
  incidentLinkOpen
  incidentLinkConflict : IncidentLinkClosure

record IncidentLineageWeld : Set where
  constructor incidentLineageWeld
  field
    atomChain : Atom.AtomLineageChain
    incident : Incident.HerzogIncidentHypervoxel
    fieldUnitReceipt : IncidentLinkClosure
    tacticIdentityReceipt : IncidentLinkClosure
    temporalPriorityReceipt : IncidentLinkClosure
    causalUseReceipt : IncidentLinkClosure
    weldReference : String

open IncidentLineageWeld public

------------------------------------------------------------------------
-- Current event fixtures deliberately remain open at the causal weld.
------------------------------------------------------------------------

prayerInterventionOpenWeld : IncidentLineageWeld
prayerInterventionOpenWeld = incidentLineageWeld
  Atom.canonicalOpenHerzogAtomChain
  Incident.prayerIncident
  incidentLinkOpen incidentLinkOpen incidentLinkOpen incidentLinkOpen
  "authorised prayer interruption: command-level permission known, but pre-event threat/classification atom -> field intervention chain not yet acquired"

whiteShirtOpenWeld : IncidentLineageWeld
whiteShirtOpenWeld = incidentLineageWeld
  Atom.canonicalOpenHerzogAtomChain
  Incident.whiteShirtIncident
  incidentLinkOpen incidentLinkOpen incidentLinkOpen incidentLinkOpen
  "white-shirt force sequence: physical sequence partly video-backed; classification/order producer for the force remains open"

ricketsonOpenWeld : IncidentLineageWeld
ricketsonOpenWeld = incidentLineageWeld
  Atom.canonicalOpenHerzogAtomChain
  Incident.ricketsonIncident
  incidentLinkOpen incidentLinkOpen incidentLinkOpen incidentLinkOpen
  "Ricketson arrest: arrest occurrence and later release/bodycam review are sourced; threat/order lineage remains open"

ocSprayOpenWeld : IncidentLineageWeld
ocSprayOpenWeld = incidentLineageWeld
  Atom.canonicalOpenHerzogAtomChain
  Incident.ocSprayNoDirectionIncident
  incidentLinkOpen incidentLinkOpen incidentLinkOpen incidentLinkOpen
  "OC spray incident family: Legal Observers report no prior direction in incidents; classification-to-force lineage remains open"

bodycamOpenWeld : IncidentLineageWeld
bodycamOpenWeld = incidentLineageWeld
  Atom.canonicalOpenHerzogAtomChain
  Incident.bodycamIncident
  incidentLinkOpen incidentLinkOpen incidentLinkOpen incidentLinkOpen
  "bodycam conduct account: recorded utterance does not identify upstream classification/order producer"

------------------------------------------------------------------------
-- BIDI claims.
------------------------------------------------------------------------

data IncidentLineageClaim : Set where
  prayerInterventionProducedByThreatClassification
  whiteShirtForceProducedByOperationalOrder
  ricketsonArrestProducedByOperationalOrder
  ocSprayProducedByClassification
  bodycamForceProducedByCommandCulture
  operationWideClassificationCausedCoercivePattern : IncidentLineageClaim

data IncidentLineageProducer : Set where
  prayerSameObjectWeldProducer
  whiteShirtSameObjectWeldProducer
  ricketsonSameObjectWeldProducer
  ocSpraySameObjectWeldProducer
  bodycamCommandCultureCorpusProducer
  crossIncidentSameClassificationProducer : IncidentLineageProducer

reverseIncidentLineage : IncidentLineageClaim → IncidentLineageProducer
reverseIncidentLineage prayerInterventionProducedByThreatClassification = prayerSameObjectWeldProducer
reverseIncidentLineage whiteShirtForceProducedByOperationalOrder = whiteShirtSameObjectWeldProducer
reverseIncidentLineage ricketsonArrestProducedByOperationalOrder = ricketsonSameObjectWeldProducer
reverseIncidentLineage ocSprayProducedByClassification = ocSpraySameObjectWeldProducer
reverseIncidentLineage bodycamForceProducedByCommandCulture = bodycamCommandCultureCorpusProducer
reverseIncidentLineage operationWideClassificationCausedCoercivePattern = crossIncidentSameClassificationProducer

record IncidentLineageBoundary : Set where
  constructor incidentLineageBoundary
  field
    sameOperationProvesSameClassificationCause : Bool
    sameOperationProvesSameClassificationCauseIsFalse : sameOperationProvesSameClassificationCause ≡ false
    aggregateCoerciveRoutingProvesCommonCommand : Bool
    aggregateCoerciveRoutingProvesCommonCommandIsFalse : aggregateCoerciveRoutingProvesCommonCommand ≡ false
    bodycamUtteranceProvesUpstreamCommand : Bool
    bodycamUtteranceProvesUpstreamCommandIsFalse : bodycamUtteranceProvesUpstreamCommand ≡ false
    prayerPermissionFailureProvesProvocationPolicy : Bool
    prayerPermissionFailureProvesProvocationPolicyIsFalse : prayerPermissionFailureProvesProvocationPolicy ≡ false
    repeatedIncidentPatternProvesIdeologicalMotive : Bool
    repeatedIncidentPatternProvesIdeologicalMotiveIsFalse : repeatedIncidentPatternProvesIdeologicalMotive ≡ false

canonicalIncidentLineageBoundary : IncidentLineageBoundary
canonicalIncidentLineageBoundary =
  incidentLineageBoundary false refl false refl false refl false refl false refl
