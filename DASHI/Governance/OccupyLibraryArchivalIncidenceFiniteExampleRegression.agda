module DASHI.Governance.OccupyLibraryArchivalIncidenceFiniteExampleRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.OccupyLibraryArchivalIncidenceFiniteExampleExact as Example

realBoundedEdgeCountPinned :
  Example.edgeCount Example.canonicalObservedEdges ≡ 18
realBoundedEdgeCountPinned = refl

firstPseudonymousSpokesEdgePresent :
  Example.ExplicitInteraction
    Example.p-ebddda
    Example.spokesCouncilProposal
firstPseudonymousSpokesEdgePresent = Example.e01

financeConsensusObservedSeparately :
  Example.DecisionObserved Example.financeIntegration
financeConsensusObservedSeparately = Example.financeConsensus

financeObservedDegreePinned :
  Example.observedIssueDegree Example.financeIntegration ≡ 3
financeObservedDegreePinned = refl

silentReadingObservedDegreePinned :
  Example.observedIssueDegree Example.silentReadingTechnology ≡ 3
silentReadingObservedDegreePinned = refl

participant442ac6DegreePinned :
  Example.observedParticipantDegree Example.p-442ac6 ≡ 3
participant442ac6DegreePinned = refl

participant33f894DegreePinned :
  Example.observedParticipantDegree Example.p-33f894 ≡ 3
participant33f894DegreePinned = refl

rawNamesNotPropagated :
  Example.rawNamesPropagatedIntoFormalTable Example.canonicalLibraryIncidenceBoundary ≡ false
rawNamesNotPropagated = refl

descriptiveDegreeIsNotCost :
  Example.observedDegreeInterpretedAsCoordinationCost Example.canonicalLibraryIncidenceBoundary ≡ false
descriptiveDegreeIsNotCost = refl

attendanceDoesNotGenerateAllIssueEdges :
  Example.attendanceCrossProductPromoted Example.canonicalLibraryIncidenceBoundary ≡ false
attendanceDoesNotGenerateAllIssueEdges = refl

speakerEdgeDoesNotEncodeAgreement :
  Example.speakerEdgeEncodesAgreement Example.canonicalLibraryIncidenceBoundary ≡ false
speakerEdgeDoesNotEncodeAgreement = refl
