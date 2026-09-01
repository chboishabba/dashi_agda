module DASHI.Governance.SexedHistoricalTransportedSupportDiscriminatorExact where

------------------------------------------------------------------------
-- TRANSPORTED-SUPPORT DISCRIMINATOR SYNTHESIS
--
-- Two support histories can share the same coarse present support surface while
-- differing in the order by which repair/counterformation was transported.
-- Rather than guessing a preferred history, instantiate the canonical DASHI
-- discriminator calculus and extend the observer only with a separating probe.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.DiscriminatorSynthesisExact as Discriminator
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.SexedHistoricalTransportedAssociatorSupportExact as Transported

------------------------------------------------------------------------
-- 1. Existing observer collision.
------------------------------------------------------------------------

supportHistoryCollision :
  Discriminator.CurrentObserverCollision Transported.coarseSupportSurface
supportHistoryCollision =
  Discriminator.currentObserverCollision
    Transported.repairedThenCounterformed
    Transported.counterformedThenRepaired
    refl

------------------------------------------------------------------------
-- 2. Candidate experiment bundles.
------------------------------------------------------------------------

data SupportProbeObservation : Set where
  repairObservedFirst
  counterformationObservedFirst
  unresolvedSupportOrder
  : SupportProbeObservation

supportOrderProbe :
  Discriminator.ExperimentBundle Transported.SupportHistoryFine
supportOrderProbe =
  Discriminator.experimentBundle
    SupportProbeObservation
    observe
    1
    "support-order probe"
    "finite DASHI support-transport calibration fixture"
  where
  observe : Transported.SupportHistoryFine → SupportProbeObservation
  observe Transported.repairedThenCounterformed = repairObservedFirst
  observe Transported.counterformedThenRepaired = counterformationObservedFirst

coarseSupportProbe :
  Discriminator.ExperimentBundle Transported.SupportHistoryFine
coarseSupportProbe =
  Discriminator.experimentBundle
    Transported.CoarseSupportSurface
    Transported.coarseSupportSurface
    0
    "coarse support surface"
    "existing observer; intentionally non-separating"

------------------------------------------------------------------------
-- 3. Exact separator receipt.
------------------------------------------------------------------------

supportOrderProbeSeparates :
  Discriminator.BundleSeparates
    supportOrderProbe
    Transported.repairedThenCounterformed
    Transported.counterformedThenRepaired
supportOrderProbeSeparates =
  Discriminator.bundleSeparates (λ ())

coarseProbeDoesNotSeparate :
  Discriminator.observe coarseSupportProbe Transported.repairedThenCounterformed
  ≡ Discriminator.observe coarseSupportProbe Transported.counterformedThenRepaired
coarseProbeDoesNotSeparate = refl

supportHistoryLanguageExtension :
  Discriminator.DiscriminatingLanguageExtension
    Transported.coarseSupportSurface
supportHistoryLanguageExtension =
  Discriminator.discriminatingLanguageExtension
    supportHistoryCollision
    supportOrderProbe
    supportOrderProbeSeparates

joinedObserverSeparatesSupportHistories :
  Discriminator.joinedObservation
    Transported.coarseSupportSurface supportOrderProbe
    Transported.repairedThenCounterformed
  ≡ Discriminator.joinedObservation
    Transported.coarseSupportSurface supportOrderProbe
    Transported.counterformedThenRepaired → ⊥
joinedObserverSeparatesSupportHistories =
  Discriminator.extensionJoinSeparates supportHistoryLanguageExtension

------------------------------------------------------------------------
-- 4. Consumer-relative next measurement.
------------------------------------------------------------------------

data SupportConsumer : Set where
  recoverSupportOrder
  recoverCurrentPersistentResidual
  : SupportConsumer

data SelectedSupportProbe : Set where
  chooseSupportOrderProbe
  chooseCurrentSupportProbe
  : SelectedSupportProbe

nextSupportProbe : SupportConsumer → SelectedSupportProbe
nextSupportProbe recoverSupportOrder = chooseSupportOrderProbe
nextSupportProbe recoverCurrentPersistentResidual = chooseCurrentSupportProbe

recoverOrderSelectsSeparatingProbe :
  nextSupportProbe recoverSupportOrder ≡ chooseSupportOrderProbe
recoverOrderSelectsSeparatingProbe = refl

------------------------------------------------------------------------
-- 5. Cross-owner continuity.
------------------------------------------------------------------------

coarseSupportStillCannotRecoverHistory :
  INF.FactorsThrough
    Transported.coarseSupportSurface Transported.fineSupportHistoryCode → ⊥
coarseSupportStillCannotRecoverHistory =
  Transported.sameCoarseSupportCannotRecoverSupportHistory

canonicalDiscriminatorBoundaryStillApplies :
  Discriminator.DiscriminatorSynthesisBoundary
canonicalDiscriminatorBoundaryStillApplies =
  Discriminator.canonicalDiscriminatorSynthesisBoundary

------------------------------------------------------------------------
-- 6. No-promotion boundaries.
------------------------------------------------------------------------

data SeparatingProbeProvesEmpiricalHistoricalCause : Set where

data CheapestProbeIsBestHistoricalTheory : Set where

data PairwiseSupportSeparationClosesWholeHistoricalWorld : Set where

data SupportProbeIsYijingDivination : Set where

data ObserverExtensionChangesPastHistory : Set where

separatorDoesNotProveEmpiricalHistoricalCause :
  SeparatingProbeProvesEmpiricalHistoricalCause → ⊥
separatorDoesNotProveEmpiricalHistoricalCause ()

cheapestProbeIsNotAutomaticallyBestHistoricalTheory :
  CheapestProbeIsBestHistoricalTheory → ⊥
cheapestProbeIsNotAutomaticallyBestHistoricalTheory ()

pairwiseSeparationDoesNotCloseWholeHistoricalWorld :
  PairwiseSupportSeparationClosesWholeHistoricalWorld → ⊥
pairwiseSeparationDoesNotCloseWholeHistoricalWorld ()

supportProbeIsNotYijingDivination : SupportProbeIsYijingDivination → ⊥
supportProbeIsNotYijingDivination ()

observerExtensionDoesNotChangePastHistory : ObserverExtensionChangesPastHistory → ⊥
observerExtensionDoesNotChangePastHistory ()

record TransportedSupportDiscriminatorBoundary : Set where
  constructor transported-support-discriminator-boundary
  field
    coarseSupportCollisionExplicit : Bool
    separatingObserverExtensionConstructed : Bool
    coarseProbeSeparates : Bool
    consumerIndexesNextProbe : Bool
    separatorProvesEmpiricalCause : Bool
    pairwiseSeparationClosesWholeHistoricalWorld : Bool
    observerExtensionChangesPast : Bool

canonicalTransportedSupportDiscriminatorBoundary :
  TransportedSupportDiscriminatorBoundary
canonicalTransportedSupportDiscriminatorBoundary =
  transported-support-discriminator-boundary
    true true false true false false false
