module DASHI.Law.SecurityThreatSemanticBroadeningTopologyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Law.DisclosureReadyClassificationInputAtomExact as Atom
import DASHI.Law.HerzogClassificationMultiSourceJoinExact as Join

------------------------------------------------------------------------
-- Semantic propagation topology.
-- Tracks whether a threat proposition is preserved, narrowed, broadened, or
-- reclassified as it moves from an individualised input toward a collective
-- operational classification.
------------------------------------------------------------------------

data ThreatScope : Set where
  namedIndividual : ThreatScope
  smallNamedGroup : ThreatScope
  eventSubset : ThreatScope
  wholeAssembly : ThreatScope
  politicalCommunity : ThreatScope
  populationCategory : ThreatScope
  scopeUnresolved : ThreatScope

data ThreatPredicate : Set where
  concreteActRisk : ThreatPredicate
  weaponsRisk : ThreatPredicate
  violenceRisk : ThreatPredicate
  disruptionRisk : ThreatPredicate
  hostilityRisk : ThreatPredicate
  aggressiveCrowdRisk : ThreatPredicate
  publicOrderRisk : ThreatPredicate
  enemyRisk : ThreatPredicate
  predicateUnresolved : ThreatPredicate

data PropagationTransform : Set where
  preserved : PropagationTransform
  narrowed : PropagationTransform
  broadenedByScope : PropagationTransform
  broadenedByPredicate : PropagationTransform
  broadenedByScopeAndPredicate : PropagationTransform
  reclassified : PropagationTransform
  conflicted : PropagationTransform
  transformOpen : PropagationTransform

record ThreatNode : Set where
  constructor threatNode
  field
    nodeId : String
    scope : ThreatScope
    predicate : ThreatPredicate
    contentReference : String
    sourceReference : String

open ThreatNode public

record ThreatPropagationEdge : Set where
  constructor threatPropagationEdge
  field
    sourceNode targetNode : ThreatNode
    transform : PropagationTransform
    producerReference : String
    semanticTransportReceipt : Atom.SemanticTransport
    sameObjectLineageClosed : Bool

open ThreatPropagationEdge public

record ThreatPropagationPath : Set where
  constructor threatPropagationPath
  field
    sourceThreat : ThreatNode
    riskAssessmentThreat : ThreatNode
    classificationThreat : ThreatNode
    orderThreat : ThreatNode
    sourceToRisk : ThreatPropagationEdge
    riskToClassification : ThreatPropagationEdge
    classificationToOrder : ThreatPropagationEdge
    pathClosed : Bool
    pathReference : String

open ThreatPropagationPath public

------------------------------------------------------------------------
-- Synthetic calibration for individual -> group broadening.
------------------------------------------------------------------------

specificIndividualThreat : ThreatNode
specificIndividualThreat = threatNode
  "SYNTHETIC-INDIVIDUAL-THREAT" namedIndividual concreteActRisk
  "specific conduct concern about a named individual"
  "synthetic calibration only"

subsetRisk : ThreatNode
subsetRisk = threatNode
  "SYNTHETIC-SUBSET-RISK" eventSubset violenceRisk
  "risk attributed to an event subset"
  "synthetic calibration only"

wholeAssemblyRisk : ThreatNode
wholeAssemblyRisk = threatNode
  "SYNTHETIC-ASSEMBLY-RISK" wholeAssembly aggressiveCrowdRisk
  "whole assembly classified as aggressive crowd"
  "synthetic calibration only"

wholeAssemblyOrder : ThreatNode
wholeAssemblyOrder = threatNode
  "SYNTHETIC-ASSEMBLY-ORDER" wholeAssembly publicOrderRisk
  "operational order treats whole assembly as public-order risk"
  "synthetic calibration only"

individualToSubset : ThreatPropagationEdge
individualToSubset = threatPropagationEdge
  specificIndividualThreat subsetRisk broadenedByScope
  "synthetic broadening step"
  Atom.broadenedMeaning
  true

subsetToAssembly : ThreatPropagationEdge
subsetToAssembly = threatPropagationEdge
  subsetRisk wholeAssemblyRisk broadenedByScopeAndPredicate
  "synthetic collective-attribution step"
  Atom.broadenedMeaning
  true

assemblyToOrder : ThreatPropagationEdge
assemblyToOrder = threatPropagationEdge
  wholeAssemblyRisk wholeAssemblyOrder reclassified
  "synthetic operational reclassification"
  Atom.reclassifiedMeaning
  true

canonicalCollectiveBroadeningPath : ThreatPropagationPath
canonicalCollectiveBroadeningPath = threatPropagationPath
  specificIndividualThreat subsetRisk wholeAssemblyRisk wholeAssemblyOrder
  individualToSubset subsetToAssembly assemblyToOrder true
  "synthetic path: named-individual conduct concern -> subset risk -> whole-assembly aggressive-crowd classification -> public-order order"

------------------------------------------------------------------------
-- Collective attribution receipts.
------------------------------------------------------------------------

data CollectiveAttributionStatus : Set where
  noCollectiveJump : CollectiveAttributionStatus
  collectiveJumpObserved : CollectiveAttributionStatus
  collectiveJumpOpen : CollectiveAttributionStatus

collectiveJumpStatus : ThreatPropagationPath → CollectiveAttributionStatus
collectiveJumpStatus p with transform (riskToClassification p)
... | broadenedByScope = collectiveJumpObserved
... | broadenedByScopeAndPredicate = collectiveJumpObserved
... | _ = collectiveJumpOpen

canonicalCollectiveJumpObserved :
  collectiveJumpStatus canonicalCollectiveBroadeningPath ≡ collectiveJumpObserved
canonicalCollectiveJumpObserved = refl

------------------------------------------------------------------------
-- BIDI consumers.
------------------------------------------------------------------------

data BroadeningClaim : Set where
  specificThreatBecameGroupThreat : BroadeningClaim
  groupThreatBecameWholeAssemblyThreat : BroadeningClaim
  wholeAssemblyThreatProducedOperationalOrder : BroadeningClaim
  collectiveAttributionWasEvidenceJustified : BroadeningClaim
  collectiveAttributionReachedSpecificIncident : BroadeningClaim
  broadeningWasIdeologicallyMotivated : BroadeningClaim

data BroadeningProducer : Set where
  sourceToGroupSemanticProducer : BroadeningProducer
  groupToAssemblySemanticProducer : BroadeningProducer
  classificationOrderProducer : BroadeningProducer
  collectiveEvidenceAdequacyProducer : BroadeningProducer
  incidentCausalWeldProducer : BroadeningProducer
  motiveAndCarrierProducer : BroadeningProducer

reverseBroadening : BroadeningClaim → BroadeningProducer
reverseBroadening specificThreatBecameGroupThreat = sourceToGroupSemanticProducer
reverseBroadening groupThreatBecameWholeAssemblyThreat = groupToAssemblySemanticProducer
reverseBroadening wholeAssemblyThreatProducedOperationalOrder = classificationOrderProducer
reverseBroadening collectiveAttributionWasEvidenceJustified = collectiveEvidenceAdequacyProducer
reverseBroadening collectiveAttributionReachedSpecificIncident = incidentCausalWeldProducer
reverseBroadening broadeningWasIdeologicallyMotivated = motiveAndCarrierProducer

record BroadeningBoundary : Set where
  constructor broadeningBoundary
  field
    onePersonThreatJustifiesWholeAssemblyThreat : Bool
    onePersonThreatJustifiesWholeAssemblyThreatIsFalse : onePersonThreatJustifiesWholeAssemblyThreat ≡ false
    repeatedCopiesJustifyScopeBroadening : Bool
    repeatedCopiesJustifyScopeBroadeningIsFalse : repeatedCopiesJustifyScopeBroadening ≡ false
    semanticBroadeningProvesIdeologicalMotive : Bool
    semanticBroadeningProvesIdeologicalMotiveIsFalse : semanticBroadeningProvesIdeologicalMotive ≡ false
    postHocCrowdLabelProvesPreActionBroadening : Bool
    postHocCrowdLabelProvesPreActionBroadeningIsFalse : postHocCrowdLabelProvesPreActionBroadening ≡ false
    collectiveThreatLabelCreatesIndependentEvidence : Bool
    collectiveThreatLabelCreatesIndependentEvidenceIsFalse : collectiveThreatLabelCreatesIndependentEvidence ≡ false

canonicalBroadeningBoundary : BroadeningBoundary
canonicalBroadeningBoundary =
  broadeningBoundary false refl false refl false refl false refl false refl

------------------------------------------------------------------------
-- Multi-source join remains orthogonal to scope broadening.
------------------------------------------------------------------------

joinIndependenceProducer : Join.JoinProducer
joinIndependenceProducer = Join.ultimateProducerSeparationProducer
