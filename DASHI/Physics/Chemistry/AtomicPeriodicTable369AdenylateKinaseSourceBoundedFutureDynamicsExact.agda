module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSourceBoundedFutureDynamicsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.AdmissibleReachability as Reach
import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Core.FrozenProvenanceDynamicRefinementExact as Frozen
import DASHI.Core.QueryIndexedFrozenDynamicPromotionExact as Future
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseWeightedNDimStateGraphExact as Graph
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFRETThirdAxisExact as Third

------------------------------------------------------------------------
-- SOURCE-BOUNDED NONTRIVIAL FUTURE DYNAMICS FOR THE ADK ROADMAP
--
-- The action constructors below are exactly the six directed edges already
-- owned by the Li-Liu-Ji weighted-state-graph formalisation.  They therefore
-- inherit only that owner's source role: computational route topology on the
-- reported landscape.  They are not experimental transition events, measured
-- rates, a calibrated Markov kernel, or a complete physical kinetic model.
--
-- The state is deliberately a product:
--
--   repository-local third-axis consumer world × source-bounded graph state.
--
-- Graph actions move only the graph-state coordinate.  The declared third-axis
-- consumer observes only the retained three-axis coordinate.  This lets us pay
-- a genuinely non-empty action system and dynamic congruence without silently
-- identifying the finite third-axis witness with any named alpha..xi state.
------------------------------------------------------------------------

AdKDynamicState : Set
AdKDynamicState = Third.ThirdAxisWorld × Graph.AdKLandscapeState

data AdKGraphAction : Set where
  stepAlphaBeta : AdKGraphAction
  stepBetaGamma : AdKGraphAction
  stepGammaDelta : AdKGraphAction
  stepDeltaXi : AdKGraphAction
  stepBetaEpsilon : AdKGraphAction
  stepEpsilonXi : AdKGraphAction

actionSource : AdKGraphAction → Graph.AdKLandscapeState
actionSource stepAlphaBeta = Graph.alpha
actionSource stepBetaGamma = Graph.beta
actionSource stepGammaDelta = Graph.gamma
actionSource stepDeltaXi = Graph.delta
actionSource stepBetaEpsilon = Graph.beta
actionSource stepEpsilonXi = Graph.epsilon

actionTarget : AdKGraphAction → Graph.AdKLandscapeState
actionTarget stepAlphaBeta = Graph.beta
actionTarget stepBetaGamma = Graph.gamma
actionTarget stepGammaDelta = Graph.delta
actionTarget stepDeltaXi = Graph.xiEquationTarget
actionTarget stepBetaEpsilon = Graph.epsilon
actionTarget stepEpsilonXi = Graph.xiEquationTarget

actionEdge : AdKGraphAction → Graph.DirectedLandscapeEdge
actionEdge stepAlphaBeta = Graph.alphaBeta
actionEdge stepBetaGamma = Graph.betaGamma
actionEdge stepGammaDelta = Graph.gammaDelta
actionEdge stepDeltaXi = Graph.deltaXi
actionEdge stepBetaEpsilon = Graph.betaEpsilon
actionEdge stepEpsilonXi = Graph.epsilonXi

adkGraphPrecondition : AdKDynamicState → AdKGraphAction → Set
adkGraphPrecondition state action = proj₂ state ≡ actionSource action

adkGraphPostcondition :
  AdKDynamicState → AdKGraphAction → AdKDynamicState → Set
adkGraphPostcondition before action after =
  proj₁ after ≡ proj₁ before × proj₂ after ≡ actionTarget action

adkGraphActionLabel : AdKGraphAction → String
adkGraphActionLabel stepAlphaBeta = "alpha->beta"
adkGraphActionLabel stepBetaGamma = "beta->gamma"
adkGraphActionLabel stepGammaDelta = "gamma->delta"
adkGraphActionLabel stepDeltaXi = "delta->xi"
adkGraphActionLabel stepBetaEpsilon = "beta->epsilon"
adkGraphActionLabel stepEpsilonXi = "epsilon->xi"

adkSourceBoundedActionSystem :
  Dependency.DependentActionSystem AdKDynamicState AdKGraphAction
adkSourceBoundedActionSystem = record
  { Precondition = adkGraphPrecondition
  ; Postcondition = adkGraphPostcondition
  ; actionLabel = adkGraphActionLabel
  }

------------------------------------------------------------------------
-- Concrete nontrivial admissible steps on both source-paid routes.
------------------------------------------------------------------------

alphaLow : AdKDynamicState
alphaLow = Third.lowThetaTwoWorld , Graph.alpha

betaLow : AdKDynamicState
betaLow = Third.lowThetaTwoWorld , Graph.beta

gammaLow : AdKDynamicState
gammaLow = Third.lowThetaTwoWorld , Graph.gamma

epsilonLow : AdKDynamicState
epsilonLow = Third.lowThetaTwoWorld , Graph.epsilon

alphaBetaAdmissible :
  Dependency.AdmissibleAction adkSourceBoundedActionSystem alphaLow stepAlphaBeta
alphaBetaAdmissible = record
  { precondition = refl
  ; after = betaLow
  ; postcondition = refl , refl
  ; dependencyReceipt = "source-bounded edge alpha->beta from Li-Liu-Ji weighted-route owner"
  }

betaGammaAdmissible :
  Dependency.AdmissibleAction adkSourceBoundedActionSystem betaLow stepBetaGamma
betaGammaAdmissible = record
  { precondition = refl
  ; after = gammaLow
  ; postcondition = refl , refl
  ; dependencyReceipt = "source-bounded edge beta->gamma from Li-Liu-Ji weighted-route owner"
  }

betaEpsilonAdmissible :
  Dependency.AdmissibleAction adkSourceBoundedActionSystem betaLow stepBetaEpsilon
betaEpsilonAdmissible = record
  { precondition = refl
  ; after = epsilonLow
  ; postcondition = refl , refl
  ; dependencyReceipt = "source-bounded edge beta->epsilon from Li-Liu-Ji weighted-route owner"
  }

primaryPrefixExecutes :
  Reach.Executes adkSourceBoundedActionSystem
    (stepAlphaBeta ∷ stepBetaGamma ∷ [])
    alphaLow
    gammaLow
primaryPrefixExecutes =
  Reach.executesCons alphaBetaAdmissible
    (Reach.executesCons betaGammaAdmissible Reach.executesNil)

alternativePrefixExecutes :
  Reach.Executes adkSourceBoundedActionSystem
    (stepAlphaBeta ∷ stepBetaEpsilon ∷ [])
    alphaLow
    epsilonLow
alternativePrefixExecutes =
  Reach.executesCons alphaBetaAdmissible
    (Reach.executesCons betaEpsilonAdmissible Reach.executesNil)

------------------------------------------------------------------------
-- The graph dynamics preserves the independent third-axis world coordinate.
------------------------------------------------------------------------

executesPreservesThirdAxisWorld :
  ∀ {actions before after} →
  Reach.Executes adkSourceBoundedActionSystem actions before after →
  proj₁ after ≡ proj₁ before
executesPreservesThirdAxisWorld Reach.executesNil = refl
executesPreservesThirdAxisWorld
  (Reach.executesCons admissible rest) =
  trans
    (executesPreservesThirdAxisWorld rest)
    (proj₁ (Dependency.postcondition admissible))

AdKFutureSurface : Set
AdKFutureSurface =
  (DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFRETObserverJoinExact.LidNmpCoordinate ×
   DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFRETObserverJoinExact.LidCoreCoordinate)

adkFutureSurface : AdKDynamicState → AdKFutureSurface
adkFutureSurface state = Third.twoFretAxisProjection (proj₁ state)

adkFutureProvenance : AdKDynamicState → Third.NmpCoreAngleCoordinate
adkFutureProvenance state = Third.thirdCoordinate (proj₁ state)

adkFutureObservation :
  AdKDynamicState → AdKFutureSurface × Third.NmpCoreAngleCoordinate
adkFutureObservation = Frozen.ProvenanceJoin adkFutureSurface adkFutureProvenance

adkFutureDynamicSafety :
  Dynamic.DynamicConsumerSafety adkSourceBoundedActionSystem adkFutureObservation
adkFutureDynamicSafety =
  Dynamic.dynamicConsumerSafety λ same leftRun rightRun →
    trans
      (cong (λ world → Third.twoFretAxisProjection world , Third.thirdCoordinate world)
        (executesPreservesThirdAxisWorld leftRun))
      (trans same
        (sym
          (cong (λ world → Third.twoFretAxisProjection world , Third.thirdCoordinate world)
            (executesPreservesThirdAxisWorld rightRun))))

------------------------------------------------------------------------
-- Frozen/query-indexed promotion over the nontrivial graph action system.
------------------------------------------------------------------------

data AdKGraphFreezeRule : Set where
  freezeThreeAxisOverSourceGraph : AdKGraphFreezeRule

adkGraphFrozenSelection : Frozen.FrozenSelectionReceipt AdKGraphFreezeRule
adkGraphFrozenSelection =
  Frozen.frozen-selection-receipt
    freezeThreeAxisOverSourceGraph
    true true false refl refl refl

lowAlpha highAlpha : AdKDynamicState
lowAlpha = Third.lowThetaTwoWorld , Graph.alpha
highAlpha = Third.highThetaTwoWorld , Graph.alpha

adkGraphFrozenStaticCandidate :
  Frozen.FrozenStaticRefinementCandidate
    {Rule = AdKGraphFreezeRule}
    adkFutureSurface
    adkFutureProvenance
adkGraphFrozenStaticCandidate =
  Frozen.frozen-static-refinement-candidate
    (Frozen.provenanceJoinStrictRefinement
      adkFutureSurface
      adkFutureProvenance
      lowAlpha
      highAlpha
      refl
      (λ ()))
    adkGraphFrozenSelection

adkGraphFrozenDynamicPromotion :
  Frozen.FrozenProvenanceDynamicPromotion
    adkSourceBoundedActionSystem
    adkFutureSurface
    adkFutureProvenance
    AdKGraphFreezeRule
adkGraphFrozenDynamicPromotion =
  Frozen.frozen-provenance-dynamic-promotion
    adkGraphFrozenStaticCandidate
    adkFutureDynamicSafety

dynamicThirdAxisAnswer :
  Third.ThirdAxisQuery → AdKDynamicState → Third.ThirdAxisAnswer
dynamicThirdAxisAnswer query state = Third.thirdAxisAnswer query (proj₁ state)

dynamicThirdAxisSemantics :
  Query.QuerySemantics AdKDynamicState Third.ThirdAxisQuery Third.ThirdAxisAnswer
dynamicThirdAxisSemantics = Query.querySemantics dynamicThirdAxisAnswer

answerFromFutureObservation :
  AdKFutureSurface × Third.NmpCoreAngleCoordinate → Third.ThirdAxisAnswer
answerFromFutureObservation (surface , Third.lowThetaTwo) = Third.lowThetaTwoAnswer
answerFromFutureObservation (surface , Third.highThetaTwo) = Third.highThetaTwoAnswer

adkGraphQueryAdequacy :
  Query.AdequateFor
    adkFutureObservation
    dynamicThirdAxisSemantics
    Third.askThirdCoordinate
adkGraphQueryAdequacy =
  Query.factorsForQuery
    answerFromFutureObservation
    (λ { (Third.lowThetaTwoWorld , graphState) → refl
       ; (Third.highThetaTwoWorld , graphState) → refl
       })

adkGraphQueryIndexedFutureSafePromotion :
  Future.QueryIndexedFutureSafePromotion
    adkSourceBoundedActionSystem
    adkFutureSurface
    adkFutureProvenance
    AdKGraphFreezeRule
    dynamicThirdAxisSemantics
    Third.askThirdCoordinate
adkGraphQueryIndexedFutureSafePromotion =
  Future.query-indexed-future-safe-promotion
    adkGraphFrozenDynamicPromotion
    adkGraphQueryAdequacy

------------------------------------------------------------------------
-- Attribution donors and firewalls.
------------------------------------------------------------------------

weightedGraphSourceDonor : Graph.WeightedGraphSourceCoordinate
weightedGraphSourceDonor = Graph.liLiuJi2015WeightedGraphSource

record AdKSourceBoundedFutureDynamicsBoundary : Set where
  constructor adk-source-bounded-future-dynamics-boundary
  field
    nontrivialSourceGraphActionsRetained : Bool
    onlyOwnedRouteEdgesAdmitted : Bool
    primaryAndAlternativePrefixesExecutable : Bool
    thirdAxisConsumerDynamicallySafeUnderGraphMoves : Bool
    routeGraphEqualsExperimentalKinetics : Bool
    pathFluxEqualsPerEdgeRate : Bool
    graphStateSilentlyIdentifiedWithThirdAxisFixtureWorld : Bool
    computationalRouteSourcePaysDASHIDynamicSafetyTheorem : Bool
    sourceGraphProvesCompletePhysicalMechanism : Bool

canonicalAdKSourceBoundedFutureDynamicsBoundary :
  AdKSourceBoundedFutureDynamicsBoundary
canonicalAdKSourceBoundedFutureDynamicsBoundary =
  adk-source-bounded-future-dynamics-boundary
    true
    true
    true
    true
    false
    false
    false
    false
    false
