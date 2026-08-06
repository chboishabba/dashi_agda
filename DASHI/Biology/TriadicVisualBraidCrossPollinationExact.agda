module DASHI.Biology.TriadicVisualBraidCrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Biology.TriadicBraidDialecticExact as TriadicBraid
import DASHI.Biology.VisualPathBraidResidual as VisualBraid

------------------------------------------------------------------------
-- Two complementary path-history witnesses.
--
-- The triadic braid has equal endpoints but distinct retained word residuals.
-- The visual path has the same component multiset but distinct endpoints.
-- Together they prove that neither endpoint equality nor component equality is
-- sufficient to erase path history.
--
-- Source-facing reference inherited from the Round Five source atlas:
-- Emil Artin, "Theory of Braids".  The visual operator source boundary is
-- inherited from the Round Three tranche.

data HistoryComparisonMode : Set where
  sameEndpointDifferentWord : HistoryComparisonMode
  sameComponentsDifferentEndpoint : HistoryComparisonMode

record CrossHistoryWitness : Set₁ where
  constructor crossHistoryWitness
  field
    triadicLeft : TriadicBraid.BraidedTransition
    triadicRight : TriadicBraid.BraidedTransition
    visualFirst : VisualBraid.TwoStepHistory
    visualSecond : VisualBraid.TwoStepHistory

    braidEndpointsAgree :
      TriadicBraid.endpoint triadicLeft
      ≡
      TriadicBraid.endpoint triadicRight

    braidWordsDiffer :
      TriadicBraid.wordKind (TriadicBraid.residual triadicLeft)
      ≡
      TriadicBraid.wordKind (TriadicBraid.residual triadicRight)
      →
      ⊥

    visualComponentsAgreeAsMultiset :
      VisualBraid.firstComponent visualFirst
      ≡
      VisualBraid.secondComponent visualSecond
      ×
      VisualBraid.secondComponent visualFirst
      ≡
      VisualBraid.firstComponent visualSecond

    visualEndpointsDiffer :
      VisualBraid.executeHistory visualFirst false
      ≡
      VisualBraid.executeHistory visualSecond false
      →
      ⊥

    visualResidualIsOne :
      VisualBraid.historyResidual visualFirst visualSecond false ≡ 1

open CrossHistoryWitness public

canonicalCrossHistoryWitness : CrossHistoryWitness
canonicalCrossHistoryWitness =
  crossHistoryWitness
    TriadicBraid.leftTransition
    TriadicBraid.rightTransition
    VisualBraid.inhibitionThenCompletion
    VisualBraid.completionThenInhibition
    TriadicBraid.braidRelationSharesEndpoint
    TriadicBraid.braidRelationRetainsDistinctWordResidual
    VisualBraid.sameComponentsDifferentOrder
    VisualBraid.historyEndpointsDiffer
    VisualBraid.canonicalHistoryResidualIsOne

endpointEqualityDoesNotEraseHistory :
  TriadicBraid.endpoint TriadicBraid.leftTransition
  ≡
  TriadicBraid.endpoint TriadicBraid.rightTransition
  ×
  ¬
    (TriadicBraid.wordKind (TriadicBraid.residual TriadicBraid.leftTransition)
    ≡
    TriadicBraid.wordKind (TriadicBraid.residual TriadicBraid.rightTransition))
endpointEqualityDoesNotEraseHistory =
  TriadicBraid.braidRelationSharesEndpoint
  ,
  TriadicBraid.braidRelationRetainsDistinctWordResidual

componentEqualityDoesNotFixEndpoint :
  VisualBraid.historyResidual
    VisualBraid.inhibitionThenCompletion
    VisualBraid.completionThenInhibition
    false
  ≡
  1
componentEqualityDoesNotFixEndpoint =
  VisualBraid.canonicalHistoryResidualIsOne

record TriadicVisualBraidBoundary : Set where
  constructor triadicVisualBraidBoundary
  field
    sameEndpointMeansSameHistory : Bool
    sameEndpointMeansSameHistoryIsFalse :
      sameEndpointMeansSameHistory ≡ false

    sameComponentsMeanSameEndpoint : Bool
    sameComponentsMeanSameEndpointIsFalse :
      sameComponentsMeanSameEndpoint ≡ false

    pathResidualRecoversAutobiography : Bool
    pathResidualRecoversAutobiographyIsFalse :
      pathResidualRecoversAutobiography ≡ false

canonicalTriadicVisualBraidBoundary : TriadicVisualBraidBoundary
canonicalTriadicVisualBraidBoundary =
  triadicVisualBraidBoundary false refl false refl false refl
