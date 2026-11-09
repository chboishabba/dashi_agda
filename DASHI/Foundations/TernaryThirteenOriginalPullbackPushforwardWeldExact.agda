module DASHI.Foundations.TernaryThirteenOriginalPullbackPushforwardWeldExact where

------------------------------------------------------------------------
-- Reuse original SectionedProjection / PredicatePullbackLattice
-- for the actual StageAtlas 12 + central TriTruth source model.
--
-- The chosen neutral section provides a representative/pushforward
-- of observables, NOT a claim that its left inverse reconstructs
-- an arbitrary central trit. Exact fine reopening uses the
-- separate residual centre with a proven round trip.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Biology.RelationalAppraisalPointedPhaseExact as Rel
import DASHI.Core.SectionedProjectionProvenanceBridgeExact as Sectioned
import DASHI.Core.PredicatePullbackLatticeExact as Pred
import Base369 as Base

sourceCentralSectionedProjection :
  Sectioned.SectionedProjection
    Rel.SourceCentralCompletionCarrier
    Rel.SourceTwelveAxisValuation
sourceCentralSectionedProjection =
  Sectioned.sectionedProjection
    Rel.sourceCentralProjection
    Rel.sourceNeutralSection
    Rel.sourceNeutralSectionProjects

sourcePullbackObservable :
  {Value : Set} →
  (Rel.SourceTwelveAxisValuation → Value) →
  Rel.SourceCentralCompletionCarrier → Value
sourcePullbackObservable =
  Sectioned.pullbackObservable Rel.sourceCentralProjection

-- The original representative operation pushes a fine observable
-- to its selected twelve-axis neutral representative. Call this
-- representative pushforward, not a derived categorical direct image.
selectedRepresentativePushforward :
  {Value : Set} →
  (Rel.SourceCentralCompletionCarrier → Value) →
  Rel.SourceTwelveAxisValuation → Value
selectedRepresentativePushforward =
  Sectioned.representativeObservable sourceCentralSectionedProjection

pushforwardAfterPullback :
  {Value : Set}
  (observable : Rel.SourceTwelveAxisValuation → Value)
  (valuation : Rel.SourceTwelveAxisValuation) →
  selectedRepresentativePushforward
    (sourcePullbackObservable observable)
    valuation ≡ observable valuation
pushforwardAfterPullback observable valuation =
  cong observable (Rel.sourceNeutralSectionProjects valuation)

pullbackOfPushforwardForFibreConstant :
  {Value : Set}
  (observable : Rel.SourceCentralCompletionCarrier → Value) →
  Sectioned.FibreConstant Rel.sourceCentralProjection observable →
  (state : Rel.SourceCentralCompletionCarrier) →
  observable state ≡
    sourcePullbackObservable
      (selectedRepresentativePushforward observable) state
pullbackOfPushforwardForFibreConstant observable constant state =
  Sectioned.fibreConstantObservableReconstructsFromSection
    sourceCentralSectionedProjection observable constant state

sourcePullbackPredicate :
  Pred.Predicate Rel.SourceTwelveAxisValuation →
  Pred.Predicate Rel.SourceCentralCompletionCarrier
sourcePullbackPredicate =
  Pred.pullbackPredicate Rel.sourceCentralProjection

sourcePullbackMeet :
  (p q : Pred.Predicate Rel.SourceTwelveAxisValuation)
  (state : Rel.SourceCentralCompletionCarrier) →
  sourcePullbackPredicate (Pred._⊓p_ p q) state
  ≡ Pred._⊓p_
      (sourcePullbackPredicate p)
      (sourcePullbackPredicate q) state
sourcePullbackMeet p q state =
  Pred.pullbackPreservesMeet Rel.sourceCentralProjection p q state

sourcePullbackJoin :
  (p q : Pred.Predicate Rel.SourceTwelveAxisValuation)
  (state : Rel.SourceCentralCompletionCarrier) →
  sourcePullbackPredicate (Pred._⊔p_ p q) state
  ≡ Pred._⊔p_
      (sourcePullbackPredicate p)
      (sourcePullbackPredicate q) state
sourcePullbackJoin p q state =
  Pred.pullbackPreservesJoin Rel.sourceCentralProjection p q state

-- The selected neutral section cannot reconstruct central trits:
-- no 'pushforward after pullback' identity is asserted on fine states.
sourceCentralResidual :
  Rel.SourceCentralCompletionCarrier → Base.TriTruth
sourceCentralResidual = Rel.sourceCentralCoordinate

sourceCentralReopen :
  Rel.SourceTwelveAxisValuation →
  Base.TriTruth → Rel.SourceCentralCompletionCarrier
sourceCentralReopen valuation centre = valuation , centre

sourceResidualExact :
  (state : Rel.SourceCentralCompletionCarrier) →
  sourceCentralReopen
    (Rel.sourceCentralProjection state)
    (sourceCentralResidual state)
  ≡ state
sourceResidualExact (valuation , centre) = refl

sourceCentralResidualReopening :
  Sectioned.ResidualReopening sourceCentralSectionedProjection
sourceCentralResidualReopening =
  Sectioned.residualReopening
    Base.TriTruth
    sourceCentralResidual
    sourceCentralReopen
    sourceResidualExact

-- This reuses the ORIGINAL provenance-bearing quotient certificate
-- instead of defining any substitute categorical pushforward.
sourceCentralProvenanceBearingQuotient =
  Sectioned.residualReopeningGivesProvenanceBearingQuotient
    sourceCentralResidualReopening
