module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseConsumerSafeFuturePromotionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.AdmissibleReachability as Reach
import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Core.FrozenProvenanceDynamicRefinementExact as Frozen
import DASHI.Core.QueryIndexedFrozenDynamicPromotionExact as Future
import DASHI.Core.ConsumerSafeFuturePromotionExact as Composite
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseConsumerSafePromotionExact as Static
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseObserverParetoExact as Pareto
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFRETObserverJoinExact as JoinFRET
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFRETThirdAxisExact as Third

------------------------------------------------------------------------
-- ADK CONSUMER-SAFE FUTURE-PROMOTION INTERFACE FIXTURE
--
-- This module instantiates the generic static+future weld over the existing AdK
-- third-axis observer problem. The static side is the source-bounded AdK repair
-- and Pareto selection already owned upstream. The future side below is a
-- deliberately repository-local no-action fixture whose only purpose is to pay
-- the composition interface.
--
-- It is NOT a model of physical adenylate-kinase kinetics. Li, Liu & Ji 2015
-- remain attributed only to the source-bounded three-CV AdK premise already
-- retained in ThirdAxisExact; they do not pay this dynamic fixture, the DASHI
-- future-safety theorem, or the generic composition theorem.
------------------------------------------------------------------------

data AdKFutureAction : Set where

adkFuturePrecondition : Third.ThirdAxisWorld → AdKFutureAction → Set
adkFuturePrecondition state ()

adkFuturePostcondition :
  Third.ThirdAxisWorld →
  AdKFutureAction →
  Third.ThirdAxisWorld →
  Set
adkFuturePostcondition before () after

adkFutureActionLabel : AdKFutureAction → String
adkFutureActionLabel ()

adkFutureSystem :
  Dependency.DependentActionSystem Third.ThirdAxisWorld AdKFutureAction
adkFutureSystem = record
  { Precondition = adkFuturePrecondition
  ; Postcondition = adkFuturePostcondition
  ; actionLabel = adkFutureActionLabel
  }

------------------------------------------------------------------------
-- The future-safe observer is the retained two-axis surface plus the third-axis
-- provenance/residual coordinate. This has exactly the information required by
-- the declared third-axis consumer, but no physical transition law is invented.
------------------------------------------------------------------------

AdKFutureSurface : Set
AdKFutureSurface =
  JoinFRET.LidNmpCoordinate × JoinFRET.LidCoreCoordinate

AdKFutureObservation : Set
AdKFutureObservation = AdKFutureSurface × Third.NmpCoreAngleCoordinate

adkFutureSurface : Third.ThirdAxisWorld → AdKFutureSurface
adkFutureSurface = Third.twoFretAxisProjection

adkFutureProvenance : Third.ThirdAxisWorld → Third.NmpCoreAngleCoordinate
adkFutureProvenance = Third.thirdCoordinate

data AdKFreezeRule : Set where
  freezeThreeAxisObserver : AdKFreezeRule

adkFrozenSelection : Frozen.FrozenSelectionReceipt AdKFreezeRule
adkFrozenSelection =
  Frozen.frozen-selection-receipt
    freezeThreeAxisObserver
    true
    true
    false
    refl
    refl
    refl

adkFrozenStaticCandidate :
  Frozen.FrozenStaticRefinementCandidate
    {Rule = AdKFreezeRule}
    adkFutureSurface
    adkFutureProvenance
adkFrozenStaticCandidate =
  Frozen.frozen-static-refinement-candidate
    (Frozen.provenanceJoinStrictRefinement
      adkFutureSurface
      adkFutureProvenance
      Third.lowThetaTwoWorld
      Third.highThetaTwoWorld
      refl
      (λ ()))
    adkFrozenSelection

------------------------------------------------------------------------
-- With no action constructor, the only executable trace is empty. Dynamic
-- safety here is therefore an interface fixture, not kinetic evidence.
------------------------------------------------------------------------

adkFutureDynamicSafety :
  Dynamic.DynamicConsumerSafety
    adkFutureSystem
    (Frozen.ProvenanceJoin adkFutureSurface adkFutureProvenance)
adkFutureDynamicSafety =
  Dynamic.dynamicConsumerSafety
    (λ { same Reach.executesNil Reach.executesNil → same })

adkFrozenDynamicPromotion :
  Frozen.FrozenProvenanceDynamicPromotion
    adkFutureSystem
    adkFutureSurface
    adkFutureProvenance
    AdKFreezeRule
adkFrozenDynamicPromotion =
  Frozen.frozen-provenance-dynamic-promotion
    adkFrozenStaticCandidate
    adkFutureDynamicSafety

thirdAnswerFromFutureObservation :
  AdKFutureObservation → Third.ThirdAxisAnswer
thirdAnswerFromFutureObservation (surface , Third.lowThetaTwo) =
  Third.lowThetaTwoAnswer
thirdAnswerFromFutureObservation (surface , Third.highThetaTwo) =
  Third.highThetaTwoAnswer

adkFutureQueryAdequacy :
  Query.AdequateFor
    (Frozen.ProvenanceJoin adkFutureSurface adkFutureProvenance)
    Third.thirdAxisSemantics
    Third.askThirdCoordinate
adkFutureQueryAdequacy =
  Query.factorsForQuery
    thirdAnswerFromFutureObservation
    (λ { Third.lowThetaTwoWorld → refl
       ; Third.highThetaTwoWorld → refl
       })

adkQueryIndexedFutureSafePromotion :
  Future.QueryIndexedFutureSafePromotion
    adkFutureSystem
    adkFutureSurface
    adkFutureProvenance
    AdKFreezeRule
    Third.thirdAxisSemantics
    Third.askThirdCoordinate
adkQueryIndexedFutureSafePromotion =
  Future.query-indexed-future-safe-promotion
    adkFrozenDynamicPromotion
    adkFutureQueryAdequacy

------------------------------------------------------------------------
-- Explicit model-to-observer realisation relation.
------------------------------------------------------------------------

data AdKObserverRealisesFuture :
  Pareto.ObserverModel →
  (Third.ThirdAxisWorld → AdKFutureObservation) →
  Set where
  threeAxisRealisesFutureJoin :
    AdKObserverRealisesFuture
      Pareto.threeAxis
      (Frozen.ProvenanceJoin adkFutureSurface adkFutureProvenance)

adkConsumerSafeFuturePromotion :
  Composite.ConsumerSafeFuturePromotion
    Static.thirdAxisCostHyperfabric
    Pareto.joinedTwo
    Pareto.threeAxis
    adkFutureSystem
    adkFutureSurface
    adkFutureProvenance
    AdKFreezeRule
    Third.thirdAxisSemantics
    Third.askThirdCoordinate
    AdKObserverRealisesFuture
adkConsumerSafeFuturePromotion =
  Composite.consumer-safe-future-promotion
    Static.adkThirdAxisConsumerSafePromotion
    adkQueryIndexedFutureSafePromotion
    threeAxisRealisesFutureJoin

adkCompositeSafeSelection :
  Composite.ConsumerSafeFuturePromotion
    Static.thirdAxisCostHyperfabric
    Pareto.joinedTwo
    Pareto.threeAxis
    adkFutureSystem
    adkFutureSurface
    adkFutureProvenance
    AdKFreezeRule
    Third.thirdAxisSemantics
    Third.askThirdCoordinate
    AdKObserverRealisesFuture
adkCompositeSafeSelection = adkConsumerSafeFuturePromotion

------------------------------------------------------------------------
-- Attribution / promotion boundary.
------------------------------------------------------------------------

thirdAxisSourceDonor : Third.ThirdAxisSourceCoordinate
thirdAxisSourceDonor = Third.liLiuJi2015ThreeCvSource

record AdKConsumerSafeFuturePromotionBoundary : Set where
  constructor adk-consumer-safe-future-promotion-boundary
  field
    genericStaticAndFuturePromotionComposed : Bool
    threeAxisModelRealisesJoinedFutureObserver : Bool
    thirdAxisQueryAdequacyRetained : Bool
    frozenSelectionRetained : Bool
    zeroActionFutureInterfaceFixture : Bool
    identityDynamicsFixtureEqualsPhysicalAdKKinetics : Bool
    liLiuJiPaysFutureSafetyTheorem : Bool
    liLiuJiPaysGenericCompositionTheorem : Bool
    futureFixtureCreatesExperimentalTransitionRates : Bool
    compositePromotionMeansCompleteProteinRecovery : Bool

canonicalAdKConsumerSafeFuturePromotionBoundary :
  AdKConsumerSafeFuturePromotionBoundary
canonicalAdKConsumerSafeFuturePromotionBoundary =
  adk-consumer-safe-future-promotion-boundary
    true
    true
    true
    true
    true
    false
    false
    false
    false
    false
