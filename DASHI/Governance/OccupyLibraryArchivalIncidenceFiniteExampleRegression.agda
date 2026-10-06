module DASHI.Governance.OccupyLibraryArchivalIncidenceFiniteExampleRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.OccupyLibraryArchivalIncidenceFiniteExampleExact as Example

realBoundedEdgeCountPinned :
  Example.edgeCount Example.canonicalObservedEdges ≡ 18
realBoundedEdgeCountPinned = refl

adashSpokesEdgePresent :
  Example.ExplicitInteraction
    Example.adash
    Example.spokesCouncilProposal
adashSpokesEdgePresent = Example.adashSpokes

financeConsensusObservedSeparately :
  Example.DecisionObserved Example.financeIntegration
financeConsensusObservedSeparately = Example.financeConsensus

financeObservedDegreePinned :
  Example.observedIssueDegree Example.financeIntegration ≡ 3
financeObservedDegreePinned = refl

silentReadingObservedDegreePinned :
  Example.observedIssueDegree Example.silentReadingTechnology ≡ 3
silentReadingObservedDegreePinned = refl

steveObservedDegreePinned :
  Example.observedParticipantDegree Example.steve ≡ 3
steveObservedDegreePinned = refl

francesObservedDegreePinned :
  Example.observedParticipantDegree Example.frances ≡ 3
francesObservedDegreePinned = refl

descriptiveDegreeIsNotCost :
  Example.observedDegreeInterpretedAsCoordinationCost
    Example.canonicalLibraryIncidenceBoundary
  ≡ false
descriptiveDegreeIsNotCost = refl

attendanceDoesNotGenerateAllIssueEdges :
  Example.attendanceCrossProductPromoted
    Example.canonicalLibraryIncidenceBoundary
  ≡ false
attendanceDoesNotGenerateAllIssueEdges = refl

speakerEdgeDoesNotEncodeAgreement :
  Example.speakerEdgeEncodesAgreement
    Example.canonicalLibraryIncidenceBoundary
  ≡ false
speakerEdgeDoesNotEncodeAgreement = refl
