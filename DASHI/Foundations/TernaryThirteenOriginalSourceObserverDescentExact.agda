module DASHI.Foundations.TernaryThirteenOriginalSourceObserverDescentExact where

------------------------------------------------------------------------
-- H2.01 source-axis model: non-descent on the actual
-- StageAtlasZeroToEleven / Base369.TriTruth valuation carrier.
-- This is not the 144-relation-field observer, the Monster quotient,
-- or an analytic modular/J theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.RelationalAppraisalPointedPhaseExact as Rel
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Foundations.TernaryThirteenOriginalAxisValuationBridgeExact as Bridge
import DASHI.Foundations.TernaryThirteenFibreObserverNonDescentExact as WordDescent
import Base369 as Base

centralSourceObserver :
  Rel.SourceCentralCompletionCarrier →
  Rel.SourceTwelveAxisValuation
centralSourceObserver = Rel.sourceCentralProjection

centralSourceConsumer :
  Rel.SourceCentralCompletionCarrier → Base.TriTruth
centralSourceConsumer = Rel.sourceCentralCoordinate

flatSourceValuation : Rel.SourceTwelveAxisValuation
flatSourceValuation _ = Base.tri-mid

neutralSourceState positiveSourceState :
  Rel.SourceCentralCompletionCarrier
neutralSourceState = flatSourceValuation , Base.tri-mid
positiveSourceState = flatSourceValuation , Base.tri-high

sourceSameTwelveObservation :
  centralSourceObserver neutralSourceState
  ≡ centralSourceObserver positiveSourceState
sourceSameTwelveObservation = refl

sourceDifferentCentralCoordinate :
  centralSourceConsumer neutralSourceState
  ≡ centralSourceConsumer positiveSourceState → ⊥
sourceDifferentCentralCoordinate ()

originalSourceCentralNonDescentWitness :
  Descent.ConsumerNonDescentWitness
    centralSourceObserver centralSourceConsumer
originalSourceCentralNonDescentWitness =
  Descent.consumerNonDescentWitness
    neutralSourceState positiveSourceState
    sourceSameTwelveObservation
    sourceDifferentCentralCoordinate

originalCentralPunctureObserverDescent :
  Descent.ConsumerSufficient
    centralSourceObserver centralSourceConsumer → ⊥
originalCentralPunctureObserverDescent =
  Descent.nonDescentWitnessBlocksSufficiency
    originalSourceCentralNonDescentWitness

originalCentralPunctureObserverCannotFactor :
  Descent.FactorsThrough
    centralSourceObserver centralSourceConsumer → ⊥
originalCentralPunctureObserverCannotFactor =
  Descent.nonDescentWitnessBlocksFactorization
    originalSourceCentralNonDescentWitness

-- The same witnesses commute with the word representation at the
-- actual source coordinate, including both opposite central states.
originalNeutralCentreEncodesAsNeutral :
  Bridge.sourceCentralToThirteen neutralSourceState
  ≡
  Bridge.sourceCentralToThirteen
    (Rel.sourceNeutralSection flatSourceValuation)
originalNeutralCentreEncodesAsNeutral = refl
