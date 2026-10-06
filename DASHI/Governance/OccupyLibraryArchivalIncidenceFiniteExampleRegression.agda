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
