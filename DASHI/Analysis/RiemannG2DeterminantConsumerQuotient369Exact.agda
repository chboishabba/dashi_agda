module DASHI.Analysis.RiemannG2DeterminantConsumerQuotient369Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotleG2eDeterminantTaperKernelExact as G2e
import DASHI.Analysis.RiemannG2C3MonsterEquivarianceAuditExact as C3Audit
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ConsumerKernelQuotientPresentationExact as Kernel
import DASHI.Core.FrontierRelationStrengthBidiExact as Relation

------------------------------------------------------------------------
-- RH G2 / 369 RESIDUAL-SUFFICIENCY CROSS-POLLINATION
--
-- The 369/Monster lane taught us to retain hidden residual/frequency structure
-- when a coarse observer cannot recover a downstream consumer.  G2e gives the
-- complementary case.  Once fixed nuisance rows n1,n2 are chosen, the entire
-- three-taper point vector h(u) enters one reflection-paired zero response only
-- through
--
--   q(u) = det3(n1,n2,h(u)).
--
-- The common zero kernel then multiplies q(u).  Therefore, for the pointwise
-- fixed-kernel consumer, q is an exact sufficient observer.  Any finer three-
-- channel distinction that leaves q unchanged is consumer-invisible at this
-- stage.  This is a theorem about the G2e interface, not a claim that no useful
-- C3 action can exist upstream.
------------------------------------------------------------------------

fixedKernelConsumer :
  (A : G2e.DeterminantTaperAlgebra) ->
  G2e.Scalar A ->
  G2e.Cell A ->
  G2e.Scalar A
fixedKernelConsumer A kernel point =
  G2e.multiply A kernel (G2e.determinantResponse A point)

determinantObserver :
  (A : G2e.DeterminantTaperAlgebra) ->
  G2e.Cell A ->
  G2e.Scalar A
determinantObserver A = G2e.determinantResponse A

determinantResponseSufficientForFixedKernel :
  (A : G2e.DeterminantTaperAlgebra) ->
  (kernel : G2e.Scalar A) ->
  Descent.ConsumerSufficient
    (determinantObserver A)
    (fixedKernelConsumer A kernel)
determinantResponseSufficientForFixedKernel A kernel left right sameQ =
  cong (G2e.multiply A kernel) sameQ

sameDeterminantForcesSameFixedKernelResponse :
  (A : G2e.DeterminantTaperAlgebra) ->
  (kernel : G2e.Scalar A) ->
  (left right : G2e.Cell A) ->
  G2e.determinantResponse A left ≡ G2e.determinantResponse A right ->
  fixedKernelConsumer A kernel left ≡ fixedKernelConsumer A kernel right
sameDeterminantForcesSameFixedKernelResponse A kernel left right =
  determinantResponseSufficientForFixedKernel A kernel left right

canonicalFixedKernelConsumerQuotient :
  (A : G2e.DeterminantTaperAlgebra) ->
  (kernel : G2e.Scalar A) ->
  Kernel.ConsumerKernelPresentation (fixedKernelConsumer A kernel)
canonicalFixedKernelConsumerQuotient A kernel =
  Kernel.canonicalConsumerKernelPresentation (fixedKernelConsumer A kernel)

------------------------------------------------------------------------
-- Exact relation-strength consequence.
--
-- At the scalarized G2e consumer, importing extra C3/Monster labels merely
-- because the pre-compression object had three coordinates is now a prunable
-- search route unless one proves that the C3 structure changes or controls q,
-- or supplies a new consumer not factoring through q.
------------------------------------------------------------------------

rh369ScalarizedRouteRelation : Relation.RelationKind
rh369ScalarizedRouteRelation = Relation.provedSearchObstructionReuse

rh369ScalarizedRouteReuse : Relation.ReuseCapability rh369ScalarizedRouteRelation
rh369ScalarizedRouteReuse = Relation.reuseProvedSearchObstruction

rh369ScalarizedRouteHasNoDirectTheoremTransfer :
  Relation.TheoremTransferCapability rh369ScalarizedRouteRelation -> ⊥
rh369ScalarizedRouteHasNoDirectTheoremTransfer =
  Relation.searchPatternCannotDirectlyTransferTheorem

literalC3ActionStillUnrecovered : C3Audit.rhLiteralC3ActionRecovered ≡ false
literalC3ActionStillUnrecovered = C3Audit.rhLiteralC3ActionRecoveredIsFalse

record RiemannG2DeterminantConsumerBoundary : Set where
  constructor riemannG2DeterminantConsumerBoundary
  field
    determinantScalarIsSufficientForFixedPointKernel : Bool
    determinantScalarIsSufficientForFixedPointKernelIsTrue :
      determinantScalarIsSufficientForFixedPointKernel ≡ true
    hiddenThreeChannelLabelCanChangeFixedKernelConsumerWhileQFixed : Bool
    hiddenThreeChannelLabelCanChangeFixedKernelConsumerWhileQFixedIsFalse :
      hiddenThreeChannelLabelCanChangeFixedKernelConsumerWhileQFixed ≡ false
    c3MayStillMatterIfItControlsDeterminantTaperQ : Bool
    c3MayStillMatterIfItControlsDeterminantTaperQIsTrue :
      c3MayStillMatterIfItControlsDeterminantTaperQ ≡ true
    scalarSufficiencyProvesTheOpenLocalZeroBound : Bool
    scalarSufficiencyProvesTheOpenLocalZeroBoundIsFalse :
      scalarSufficiencyProvesTheOpenLocalZeroBound ≡ false
    highestAlphaReading : String

canonicalRiemannG2DeterminantConsumerBoundary :
  RiemannG2DeterminantConsumerBoundary
canonicalRiemannG2DeterminantConsumerBoundary =
  riemannG2DeterminantConsumerBoundary
    true refl
    false refl
    true refl
    false refl
    "After G2e determinant compression, search should target the scalar q(u) cosine transform. A C3/Fourier route becomes theorem-relevant only if a literal cyclic action gives a nontrivial invariant/decomposition of q itself or of a downstream consumer that does not already factor through q."
