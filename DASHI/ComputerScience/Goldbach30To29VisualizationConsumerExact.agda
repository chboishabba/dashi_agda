module DASHI.ComputerScience.Goldbach30To29VisualizationConsumerExact where

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.FutureObservationalRefinement as Future
import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.ComputerScience.FibreMachineFoundation369Exact as Fibre369
import DASHI.ComputerScience.Goldbach30To29SuccessMacroExact as Macro

------------------------------------------------------------------------
-- VISUALISATION / CONSUMER CUT
--
-- The question raised on Mike Dupont's visualisation thread is not whether a
-- renderer is injective on fine machine states.  DASHI's existing consumer
-- descent law asks whether the DECLARED downstream consumer is constant on
-- each visible fibre.  FutureObservationalRefinement then owns the stronger
-- trace/future version when a proof-bearing action system is supplied.
------------------------------------------------------------------------

coarse369CannotDetermineExecutionLength :
  Descent.ConsumerSufficient
    Fibre369.address369Observer
    Fibre369.executionLengthConsumer →
  ⊥
coarse369CannotDetermineExecutionLength =
  Fibre369.address369AloneNotConsumerSufficientForExecutionLength

consumerObserverRemainsLeastSufficient :
  Descent.LeastSufficientConsumerObserver
    Fibre369.executionLengthConsumer
consumerObserverRemainsLeastSufficient =
  Descent.canonicalConsumerObserverIsLeast
    Fibre369.executionLengthConsumer

------------------------------------------------------------------------
-- Success-macro consumer equality is a positive compression result.
--
-- The two different internal success tails may be quotiented at the terminal
-- boundary for the declared next-even and verdict consumers because DASHI has
-- a direct equality proof for those consumer outputs.
------------------------------------------------------------------------

successNextEvenConsumerSurvivesCompression :
  (x : Macro.SuccessEntry) →
  Macro.nextEvenBoundaryConsumer (Macro.oldSuccessTerminal x)
  ≡
  Macro.nextEvenBoundaryConsumer (Macro.newSuccessTerminal x)
successNextEvenConsumerSurvivesCompression =
  Macro.successNextEvenConsumerPreserved

successVerdictConsumerSurvivesCompression :
  (x : Macro.SuccessEntry) →
  Macro.verdictGuardConsumer (Macro.oldSuccessTerminal x)
  ≡
  Macro.verdictGuardConsumer (Macro.newSuccessTerminal x)
successVerdictConsumerSurvivesCompression =
  Macro.successGoldbachVerdictConsumerPreserved

------------------------------------------------------------------------
-- Canonical future-observer owner.
--
-- Once the literal Goldbach machine transition carrier is reconstructed in
-- DASHI (or attached cross-prover with a same-object receipt), its declared
-- visual consumer should be routed through this existing maximal-safe future
-- refinement rather than a new local bisimulation definition.
------------------------------------------------------------------------

canonicalFutureConsumerRefinement :
  ∀ {Action : Set}
    (system : Dependency.DependentActionSystem
      {State = Signed.SignedSSPExecutionState} Action) →
  Future.MaximalSafeRefinement
    system
    Fibre369.executionLengthConsumer
canonicalFutureConsumerRefinement system =
  Future.canonicalMaximalSafeRefinement
    system
    Fibre369.executionLengthConsumer

record GoldbachVisualizationConsumerBoundary : Set where
  constructor goldbachVisualizationConsumerBoundary
  field
    fineStateMustEqualVisibleState : Bool
    adequacyIsConsumerRelative : Bool
    sameVisibleStateMayHideExecutionCost : Bool
    successNextEvenConsumerIsPreserved : Bool
    successVerdictConsumerIsPreserved : Bool
    futureSafetyHasExistingCanonicalOwner : Bool
    actualExplorerRendererSameObjectAttached : Bool

canonicalGoldbachVisualizationConsumerBoundary :
  GoldbachVisualizationConsumerBoundary
canonicalGoldbachVisualizationConsumerBoundary =
  goldbachVisualizationConsumerBoundary
    false true true true true true false
