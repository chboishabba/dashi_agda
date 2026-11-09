module DASHI.Foundations.TernaryThirteenOriginalConsumerRepairAndWorldTransportExact where

------------------------------------------------------------------------
-- H2.01: original observer/consumer sufficiency frontier and a
-- *source-payment contract* for the actual ITIR semantic-world node.
--
-- Constructively close sufficiency on the selected source carrier
-- after reopening the omitted centre. Transport non-descent to
-- actual ITIR nodes ONLY after separately supplied witnesses
-- identify two genuine nodes and their source projections.
--
-- IMPORTANT: no synthetic ITIR semantic nodes are manufactured here.
-- A node's semanticIdentity is not a thirteenth trit, and no
-- evidence/authority conclusion is promoted from this mathematics.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.RelationalAppraisalPointedPhaseExact as Rel
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ConsumerFibreRepairExact as Repair
import DASHI.Core.SectionedProjectionProvenanceBridgeExact as Sectioned
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Foundations.TernaryThirteenOriginalSourceObserverDescentExact as Source
import DASHI.Foundations.TernaryThirteenOriginalPullbackPushforwardWeldExact as Pull
import DASHI.Interop.ITIRFederatedTypedWorldProjectionExact as ITIR
import Base369 as Base

-- Exactly the selected original observer + separately retained
-- central coordinate. The consumer is the second projection.
repairedCentralObserver :
  Rel.SourceCentralCompletionCarrier →
  Rel.SourceTwelveAxisValuation × Base.TriTruth
repairedCentralObserver =
  Observer.pairObserver
    Rel.sourceCentralProjection
    Rel.sourceCentralCoordinate

centralRepairIsSufficient :
  Descent.ConsumerSufficient
    repairedCentralObserver
    Rel.sourceCentralCoordinate
centralRepairIsSufficient left right equalPair =
  cong proj₂ equalPair

centralRepairFactors :
  Descent.FactorsThrough
    repairedCentralObserver
    Rel.sourceCentralCoordinate
centralRepairFactors =
  Descent.sectionedFibreConstantFactors
    sectionedRepair Rel.sourceCentralCoordinate
    centralRepairIsSufficient
  where
    sectionedRepair :
      Sectioned.SectionedProjection
        Rel.SourceCentralCompletionCarrier
        (Rel.SourceTwelveAxisValuation × Base.TriTruth)
    sectionedRepair =
      Sectioned.sectionedProjection
        repairedCentralObserver
        (λ p → p)
        (λ p → refl)

sourceTwelveAloneCannotSuffice :
  Descent.ConsumerSufficient
    Rel.sourceCentralProjection
    Rel.sourceCentralCoordinate → ⊥
sourceTwelveAloneCannotSuffice =
  Source.originalCentralPunctureObserverDescent

everySufficientRepairSeparatesCentralCollision :
  {Refinement : Set}
  (refine : Rel.SourceCentralCompletionCarrier → Refinement) →
  Repair.RefinementRepairs
    Rel.sourceCentralProjection
    refine
    Rel.sourceCentralCoordinate →
  refine Source.neutralSourceState
    ≡ refine Source.positiveSourceState → ⊥
everySufficientRepairSeparatesCentralCollision refine repaired =
  Repair.refinementRepairSeparatesWitness
    Source.originalSourceCentralNonDescentWitness repaired

-- The actual original ITIR type has source-addressable identity,
-- revision and evidence receipts, none of which automatically give
-- this ternary-valuation and central-coordinate interpretation.
ITIRWorldState : Set
ITIRWorldState = ITIR.SourceAddressableSemanticNode

record OriginalWorldCentralTransport : Set₁ where
  field
    worldToSource :
      ITIRWorldState → Rel.SourceCentralCompletionCarrier
    worldObserve :
      ITIRWorldState → Rel.SourceTwelveAxisValuation
    worldConsume :
      ITIRWorldState → Base.TriTruth

    -- A source selection is paid by two actual original world
    -- nodes with opposite centre and SAME twelve-axis valuation.
    worldNeutral worldPositive : ITIRWorldState
    neutralIsSelectedSource :
      worldToSource worldNeutral ≡ Source.neutralSourceState
    positiveIsSelectedSource :
      worldToSource worldPositive ≡ Source.positiveSourceState

    -- Both consumers must be the independently intended actual
    -- projections of the SAME selected original state.
    observeCommutes :
      (world : ITIRWorldState) →
      worldObserve world ≡
        Rel.sourceCentralProjection (worldToSource world)
    consumerCommutes :
      (world : ITIRWorldState) →
      worldConsume world ≡
        Rel.sourceCentralCoordinate (worldToSource world)
open OriginalWorldCentralTransport public

worldPairSameObservation :
  (selected : OriginalWorldCentralTransport) →
  worldObserve selected (worldNeutral selected)
  ≡ worldObserve selected (worldPositive selected)
worldPairSameObservation selected =
  trans
    (observeCommutes selected (worldNeutral selected))
    (trans
      (cong Rel.sourceCentralProjection
        (neutralIsSelectedSource selected))
      (trans Source.sourceSameTwelveObservation
        (trans
          (sym (cong Rel.sourceCentralProjection
            (positiveIsSelectedSource selected)))
          (sym (observeCommutes selected
            (worldPositive selected))))))

worldPairDifferentConsumer :
  (selected : OriginalWorldCentralTransport) →
  worldConsume selected (worldNeutral selected)
  ≡ worldConsume selected (worldPositive selected) → ⊥
worldPairDifferentConsumer selected eq =
  Source.sourceDifferentCentralCoordinate
    (trans
      (sym (cong Rel.sourceCentralCoordinate
        (neutralIsSelectedSource selected)))
      (trans
        (sym (consumerCommutes selected (worldNeutral selected)))
        (trans eq
          (trans
            (consumerCommutes selected (worldPositive selected))
            (cong Rel.sourceCentralCoordinate
              (positiveIsSelectedSource selected))))))

originalWorldNonDescentFromPaidCorrespondence :
  (selected : OriginalWorldCentralTransport) →
  Descent.ConsumerNonDescentWitness
    (worldObserve selected)
    (worldConsume selected)
originalWorldNonDescentFromPaidCorrespondence selected =
  Descent.consumerNonDescentWitness
    (worldNeutral selected)
    (worldPositive selected)
    (worldPairSameObservation selected)
    (worldPairDifferentConsumer selected)

originalWorldCannotFactorAfterPaidCorrespondence :
  (selected : OriginalWorldCentralTransport) →
  Descent.FactorsThrough
    (worldObserve selected)
    (worldConsume selected) → ⊥
originalWorldCannotFactorAfterPaidCorrespondence selected =
  Descent.nonDescentWitnessBlocksFactorization
    (originalWorldNonDescentFromPaidCorrespondence selected)

originalWorldObserverInsufficientAfterPaidCorrespondence :
  (selected : OriginalWorldCentralTransport) →
  Descent.ConsumerSufficient
    (worldObserve selected)
    (worldConsume selected) → ⊥
originalWorldObserverInsufficientAfterPaidCorrespondence selected =
  Descent.nonDescentWitnessBlocksSufficiency
    (originalWorldNonDescentFromPaidCorrespondence selected)
