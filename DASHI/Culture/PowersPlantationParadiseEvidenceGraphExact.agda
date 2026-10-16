module DASHI.Culture.PowersPlantationParadiseEvidenceGraphExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Culture.PowersPlantationParadiseEmpiricalProgrammeExact as Empirical
import DASHI.Culture.PowersPlantationParadiseMinetteMicrohistoryExact as Minette
import DASHI.Culture.PowersPlantationParadisePerformerComparisonExact as Comparison
import DASHI.Culture.PowersPlantationParadiseEnslavedDistributionEvidenceExact as Enslaved
import DASHI.Culture.PowersPlantationParadiseMinetteChronologyContestationExact as Chronology

------------------------------------------------------------------------
-- SOURCE-ROOTED HISTORICAL EVIDENCE GRAPH
--
-- This is a graph of receipted coordinates, not an ontology of historical
-- reality.  Edges preserve the relation actually paid by the cited receipt;
-- graph reachability never manufactures identity, causation or missing facts.
------------------------------------------------------------------------

data EvidenceNodeKind : Set where
  sourceManifestationNode : EvidenceNodeKind
  assertionNode : EvidenceNodeKind
  eventNode : EvidenceNodeKind
  personNode : EvidenceNodeKind
  venueNode : EvidenceNodeKind
  roleNode : EvidenceNodeKind
  compensationNode : EvidenceNodeKind
  burdenNode : EvidenceNodeKind
  voiceNode : EvidenceNodeKind
  chronologyClaimNode : EvidenceNodeKind

record EvidenceNode : Set where
  constructor evidence-node
  field
    nodeId : String
    kind : EvidenceNodeKind
    label : String

open EvidenceNode public

data EvidenceEdgeKind : Set where
  sourceSupportsAssertion : EvidenceEdgeKind
  assertionLocatesEvent : EvidenceEdgeKind
  eventInvolvesPerson : EvidenceEdgeKind
  eventOccursAtVenue : EvidenceEdgeKind
  personPerformsRole : EvidenceEdgeKind
  contractSpecifiesCompensation : EvidenceEdgeKind
  sourceRecordsNonpayment : EvidenceEdgeKind
  sourceRecordsCoerciveStatus : EvidenceEdgeKind
  claimsSameIncidentDifferentAccount : EvidenceEdgeKind
  descriptiveSiblingRelation : EvidenceEdgeKind

record EvidenceEdge : Set where
  constructor evidence-edge
  field
    edgeId : String
    edgeKind : EvidenceEdgeKind
    fromNode : EvidenceNode
    toNode : EvidenceNode
    provenanceReference : String
    promotesCausalEffect : Bool
    promotesCausalEffectIsFalse : promotesCausalEffect ≡ false

open EvidenceEdge public

minettePerson : EvidenceNode
minettePerson = evidence-node "person:minette" personNode "Minette"

lisePerson : EvidenceNode
lisePerson = evidence-node "person:lise" personNode "Lise"

julienPerson : EvidenceNode
julienPerson = evidence-node "person:julien-1781" personNode "Julien, viola player named in 13 November 1781 notice"

portAuPrinceVenue : EvidenceNode
portAuPrinceVenue = evidence-node "venue:port-au-prince-theatre" venueNode "Port-au-Prince theatre"

capVenue : EvidenceNode
capVenue = evidence-node "venue:comedie-du-cap" venueNode "Comédie du Cap"

minetteSalaryContract : EvidenceNode
minetteSalaryContract = evidence-node "compensation:minette-1784-contract" compensationNode "three-year contract at 8000 livres/year"

minetteSalaryNonpayment : EvidenceNode
minetteSalaryNonpayment = evidence-node "assertion:minette-1784-nonpayment" assertionNode "Saint-Martin will reports salary had never been paid"

julienContributionEvent : EvidenceNode
julienContributionEvent = evidence-node "event:julien-cap-theatre-1781" eventNode "Julien engaged as viola player at the Comédie du Cap"

julienCoerciveStatus : EvidenceNode
julienCoerciveStatus = evidence-node "burden:julien-sale-status-1781" burdenNode "same notice presents Julien as saleable enslaved person"

liseSaintMarcEvent : EvidenceNode
liseSaintMarcEvent = evidence-node "event:lise-saint-marc-1786" eventNode "Lise performs Thérèse at Saint-Marc, 6 February 1786"

july1Claim : EvidenceNode
july1Claim = evidence-node "chronology:minette-notice-1790-07-01" chronologyClaimNode "Prest date: 1 July 1790"

july17Claim : EvidenceNode
july17Claim = evidence-node "chronology:minette-notice-1790-07-17" chronologyClaimNode "Laméca date: 17 July 1790"

minetteContractEdge : EvidenceEdge
minetteContractEdge =
  evidence-edge
    "edge:minette-contract"
    contractSpecifiesCompensation
    minettePerson
    minetteSalaryContract
    "Prest 2019; ANOM DPPC Notaire Michel, Testament du Sr Saint-Martin, 9 June 1784"
    false refl

minetteNonpaymentEdge : EvidenceEdge
minetteNonpaymentEdge =
  evidence-edge
    "edge:minette-nonpayment"
    sourceRecordsNonpayment
    minetteSalaryContract
    minetteSalaryNonpayment
    "Prest 2019 reconstruction of Saint-Martin testament"
    false refl

julienContributionEdge : EvidenceEdge
julienContributionEdge =
  evidence-edge
    "edge:julien-contribution"
    eventInvolvesPerson
    julienContributionEvent
    julienPerson
    "Affiches américaines coordinate preserved by Laméca, 13 November 1781"
    false refl

julienBurdenEdge : EvidenceEdge
julienBurdenEdge =
  evidence-edge
    "edge:julien-burden"
    sourceRecordsCoerciveStatus
    julienPerson
    julienCoerciveStatus
    "same 13 November 1781 sale notice"
    false refl

liseEventEdge : EvidenceEdge
liseEventEdge =
  evidence-edge
    "edge:lise-event"
    eventInvolvesPerson
    liseSaintMarcEvent
    lisePerson
    "Affiches américaines, 28 January 1786 announcement; performance 6 February 1786"
    false refl

minetteLiseSiblingEdge : EvidenceEdge
minetteLiseSiblingEdge =
  evidence-edge
    "edge:minette-lise-sibling"
    descriptiveSiblingRelation
    minettePerson
    lisePerson
    "Prest descriptive same-family reconstruction; not a causal matching receipt"
    false refl

july1790ContestationEdge : EvidenceEdge
july1790ContestationEdge =
  evidence-edge
    "edge:minette-july-1790-contestation"
    claimsSameIncidentDifferentAccount
    july1Claim
    july17Claim
    "SensibLaw chronology contestation over Prest/Laméca secondary coordinates; primary issue pending"
    false refl

------------------------------------------------------------------------
-- Exact existing receipt anchors.  The graph cannot outrun these owners.
------------------------------------------------------------------------

minetteSalaryAnchor : Minette.MinetteSalaryNonpaymentReceipt
minetteSalaryAnchor = Minette.minette1784SalaryNonpaymentReceipt

liseEventAnchor : Comparison.PerformerEventReceipt
liseEventAnchor = Comparison.liseSaintMarc1786Receipt

julienContributionBurdenAnchor : Enslaved.EnslavedMusicianContributionBurdenReceipt
julienContributionBurdenAnchor = Enslaved.julien1781ContributionBurdenReceipt

portAuPrinceSeatingAnchor : Empirical.SameObjectEmpiricalReceipt
portAuPrinceSeatingAnchor = Empirical.portAuPrinceSeatingGeometryReceipt

july1790ContestationAnchor :
  Chronology.minette1790NoticeContestationRelation
  ≡ Chronology.minette1790NoticeContestationRelation
july1790ContestationAnchor = refl

data GraphReachabilityCreatesHistoricalIdentity : Set where

data CoerciveAdvertisementEqualsNeutralBiography : Set where

graphReachabilityDoesNotCreateHistoricalIdentity :
  GraphReachabilityCreatesHistoricalIdentity → ⊥
graphReachabilityDoesNotCreateHistoricalIdentity ()

coerciveAdvertisementDoesNotBecomeNeutralBiography :
  CoerciveAdvertisementEqualsNeutralBiography → ⊥
coerciveAdvertisementDoesNotBecomeNeutralBiography ()

record PowersEvidenceGraphBoundary : Set where
  constructor powers-evidence-graph-boundary
  field
    receiptAnchorsPreserved : Bool
    receiptAnchorsPreservedIsTrue : receiptAnchorsPreserved ≡ true
    sourceSpeakerAndHistoricalSubjectMayDiffer : Bool
    sourceSpeakerAndHistoricalSubjectMayDifferIsTrue :
      sourceSpeakerAndHistoricalSubjectMayDiffer ≡ true
    graphReachabilityCreatesIdentity : Bool
    graphReachabilityCreatesIdentityIsFalse : graphReachabilityCreatesIdentity ≡ false
    graphReachabilityCreatesCausation : Bool
    graphReachabilityCreatesCausationIsFalse : graphReachabilityCreatesCausation ≡ false
    unresolvedCoordinatesRemainOpen : Bool
    unresolvedCoordinatesRemainOpenIsTrue : unresolvedCoordinatesRemainOpen ≡ true

canonicalPowersEvidenceGraphBoundary : PowersEvidenceGraphBoundary
canonicalPowersEvidenceGraphBoundary =
  powers-evidence-graph-boundary
    true refl
    true refl
    false refl
    false refl
    true refl
