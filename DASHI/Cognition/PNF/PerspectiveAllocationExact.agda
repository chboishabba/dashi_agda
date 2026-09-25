module DASHI.Cognition.PNF.PerspectiveAllocationExact where

------------------------------------------------------------------------
-- PERSPECTIVE ALLOCATION / OWN-POSITION AUTHORITY
--
-- DASHI CONTRIBUTION
--
-- The weights here are finite observation coordinates, not neural quantities.
-- They permit high monitoring of others to coexist with low own-position
-- authority and keep self-expression distinct from relational-harmony action.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent

record PerspectiveAllocationState : Set where
  constructor perspective-allocation-state
  field
    weightAA weightBB weightAB weightBA weightRelation weightSelf : Nat
    otherModelResolution : Nat
    selfResolution : Nat
    selfAuthority : Nat
    ownPositionExpression : Bool
    relationalHarmonyAction : Bool

open PerspectiveAllocationState public

highOtherLowSelfAuthority : PerspectiveAllocationState
highOtherLowSelfAuthority =
  perspective-allocation-state
    8 8 9 9 9 2
    9 8 1 false true

highOtherHighSelfAuthority : PerspectiveAllocationState
highOtherHighSelfAuthority =
  perspective-allocation-state
    8 8 9 9 9 8
    9 8 9 true true

otherResolutionObserver : PerspectiveAllocationState → Nat
otherResolutionObserver = otherModelResolution

selfAuthorityConsumer : PerspectiveAllocationState → Nat
selfAuthorityConsumer = selfAuthority

sameHighOtherResolution :
  otherResolutionObserver highOtherLowSelfAuthority
  ≡ otherResolutionObserver highOtherHighSelfAuthority
sameHighOtherResolution = refl

differentSelfAuthority :
  selfAuthorityConsumer highOtherLowSelfAuthority
  ≡ selfAuthorityConsumer highOtherHighSelfAuthority →
  ⊥
differentSelfAuthority ()

otherResolutionAuthorityWitness :
  Descent.ConsumerNonDescentWitness
    otherResolutionObserver selfAuthorityConsumer
otherResolutionAuthorityWitness =
  Descent.consumerNonDescentWitness
    highOtherLowSelfAuthority
    highOtherHighSelfAuthority
    sameHighOtherResolution
    differentSelfAuthority

selfAuthorityDoesNotFactorThroughOtherResolution :
  Descent.FactorsThrough otherResolutionObserver selfAuthorityConsumer → ⊥
selfAuthorityDoesNotFactorThroughOtherResolution =
  Descent.nonDescentWitnessBlocksFactorization
    otherResolutionAuthorityWitness

harmonyObserver : PerspectiveAllocationState → Bool
harmonyObserver = relationalHarmonyAction

selfExpressionConsumer : PerspectiveAllocationState → Bool
selfExpressionConsumer = ownPositionExpression

sameHarmonyAction :
  harmonyObserver highOtherLowSelfAuthority
  ≡ harmonyObserver highOtherHighSelfAuthority
sameHarmonyAction = refl

differentSelfExpression :
  selfExpressionConsumer highOtherLowSelfAuthority
  ≡ selfExpressionConsumer highOtherHighSelfAuthority →
  ⊥
differentSelfExpression ()

harmonyExpressionWitness :
  Descent.ConsumerNonDescentWitness harmonyObserver selfExpressionConsumer
harmonyExpressionWitness =
  Descent.consumerNonDescentWitness
    highOtherLowSelfAuthority
    highOtherHighSelfAuthority
    sameHarmonyAction
    differentSelfExpression

ownPositionExpressionDoesNotFactorThroughHarmonyAction :
  Descent.FactorsThrough harmonyObserver selfExpressionConsumer → ⊥
ownPositionExpressionDoesNotFactorThroughHarmonyAction =
  Descent.nonDescentWitnessBlocksFactorization harmonyExpressionWitness
