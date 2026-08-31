module DASHI.Analysis.RiemannG2DeterminantSymmetryRelevance369Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.ConsumerRelativeSymmetryRelevanceExact as Symmetry
import DASHI.Core.FrontierRelationStrengthBidiExact as Relation
import DASHI.Analysis.RiemannAristotleG2eDeterminantTaperKernelExact as G2e
import DASHI.Analysis.RiemannG2DeterminantConsumerQuotient369Exact as Quotient
import DASHI.Analysis.RiemannAristotleTwoZeroThreeTaperReturnExact as ThreeTaper

------------------------------------------------------------------------
-- RH G2 / DETERMINANT-LEVEL SYMMETRY RELEVANCE
--
-- The previous 369 audit found that the scalar determinant taper
--
--   q(u) = det3(n1,n2,h(u))
--
-- is already a sufficient observer for the fixed reflection-paired pointwise
-- zero kernel.  Therefore one does not need full equivariance of the original
-- three-channel carrier in order to know whether a candidate symmetry matters
-- to that consumer.  It is enough to ask what the symmetry does to q.
------------------------------------------------------------------------

DeterminantPreservingAction :
  (A : G2e.DeterminantTaperAlgebra) ->
  (G2e.Cell A -> G2e.Cell A) ->
  Set
DeterminantPreservingAction A act =
  Symmetry.PreservesObserver (Quotient.determinantObserver A) act

determinantPreservingActionIsInvisibleToFixedKernelConsumer :
  (A : G2e.DeterminantTaperAlgebra) ->
  (kernel : G2e.Scalar A) ->
  (act : G2e.Cell A -> G2e.Cell A) ->
  DeterminantPreservingAction A act ->
  Symmetry.ConsumerInvariantUnder
    (Quotient.fixedKernelConsumer A kernel)
    act
determinantPreservingActionIsInvisibleToFixedKernelConsumer A kernel act preservesQ =
  Symmetry.sufficientObserverPreservationImpliesConsumerInvariance
    (Quotient.determinantResponseSufficientForFixedKernel A kernel)
    preservesQ

------------------------------------------------------------------------
-- Literal-source audit.
--
-- The current cross-prover return owns existence of a constructed positive
-- three-taper triple and exact elimination of two selected nuisances.  Its
-- theorem surface does not supply a cyclic generator of those tapers, nor a
-- theorem that such a generator preserves q.  Absence of that receipt is not a
-- theorem that no symmetry exists; it is a precise current proof-search cut.
------------------------------------------------------------------------

constructedPositiveThreeTaperTripleOwned : Bool
constructedPositiveThreeTaperTripleOwned =
  ThreeTaper.constructedPositiveTaperTriple
    ThreeTaper.canonicalTwoZeroThreeTaperReturn

literalCyclicGeneratorRecoveredFromThreeTaperReturn : Bool
literalCyclicGeneratorRecoveredFromThreeTaperReturn = false

literalCyclicGeneratorRecoveredFromThreeTaperReturnIsFalse :
  literalCyclicGeneratorRecoveredFromThreeTaperReturn ≡ false
literalCyclicGeneratorRecoveredFromThreeTaperReturnIsFalse = refl

literalCyclicActionPreservesDeterminantTaperQ : Bool
literalCyclicActionPreservesDeterminantTaperQ = false

literalCyclicActionPreservesDeterminantTaperQIsFalse :
  literalCyclicActionPreservesDeterminantTaperQ ≡ false
literalCyclicActionPreservesDeterminantTaperQIsFalse = refl

------------------------------------------------------------------------
-- Search consequence.
--
-- A candidate C3 action that leaves q fixed is consumer-invisible at G2e.
-- Hence the only theorem-relevant C3 route is one that proves a useful action on
-- q itself: a nontrivial character law, factorization, sign law, or bound that
-- enters the signed scalar zero sum.
------------------------------------------------------------------------

rhDeterminantSymmetryRelation : Relation.RelationKind
rhDeterminantSymmetryRelation = Relation.provedSearchObstructionReuse

rhDeterminantSymmetryReuse : Relation.ReuseCapability rhDeterminantSymmetryRelation
rhDeterminantSymmetryReuse = Relation.reuseProvedSearchObstruction

record RiemannG2DeterminantSymmetryBoundary : Set where
  constructor riemannG2DeterminantSymmetryBoundary
  field
    fullThreeChannelEquivarianceRequiredToTestConsumerRelevance : Bool
    fullThreeChannelEquivarianceRequiredToTestConsumerRelevanceIsFalse :
      fullThreeChannelEquivarianceRequiredToTestConsumerRelevance ≡ false
    determinantPreservationForcesFixedKernelConsumerInvariance : Bool
    determinantPreservationForcesFixedKernelConsumerInvarianceIsTrue :
      determinantPreservationForcesFixedKernelConsumerInvariance ≡ true
    currentThreeTaperReturnSuppliesLiteralCyclicGenerator : Bool
    currentThreeTaperReturnSuppliesLiteralCyclicGeneratorIsFalse :
      currentThreeTaperReturnSuppliesLiteralCyclicGenerator ≡ false
    currentThreeTaperReturnSuppliesQInvariance : Bool
    currentThreeTaperReturnSuppliesQInvarianceIsFalse :
      currentThreeTaperReturnSuppliesQInvariance ≡ false
    usefulC3RouteMustControlQOrLaterNonfactoringConsumer : Bool
    usefulC3RouteMustControlQOrLaterNonfactoringConsumerIsTrue :
      usefulC3RouteMustControlQOrLaterNonfactoringConsumer ≡ true
    highestAlphaReading : String

canonicalRiemannG2DeterminantSymmetryBoundary :
  RiemannG2DeterminantSymmetryBoundary
canonicalRiemannG2DeterminantSymmetryBoundary =
  riemannG2DeterminantSymmetryBoundary
    false refl
    true refl
    false refl
    false refl
    true refl
    "The RH/369 search cut is now determinant-level: inspect any literal taper symmetry only for its induced action on q(u)=det3(n1,n2,h(u)). If q is invariant, the fixed-kernel G2e consumer is invariant automatically and the fine symmetry is irrelevant there. A useful C3 route must instead yield a nontrivial theorem about q or about a downstream consumer that does not factor through q."
