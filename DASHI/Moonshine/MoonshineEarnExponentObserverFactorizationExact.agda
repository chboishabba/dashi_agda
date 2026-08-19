module DASHI.Moonshine.MoonshineEarnExponentObserverFactorizationExact where

------------------------------------------------------------------------
-- HISTORICAL PR #1 ROUTING THROUGH A FINER MONSTER OBSERVER
--
-- PR #1 performs the three substitutions
--
--   23 -> 47,
--    7 -> 59,
--   11 -> 71.
--
-- MoonshineEarnOggObserverNonfactorabilityExact proves that the common coarse
-- Monster/Fricke support observer cannot determine those three distinct
-- targets.  The quantitative Monster exponent is a strictly finer observer on
-- the three historical sources:
--
--   v_23(|M|)=1,  v_7(|M|)=6,  v_11(|M|)=2.
--
-- DASHI CONTRIBUTION
--
-- The historical routing DOES factor through this source-exponent observer on
-- the three-point PR #1 carrier.  But exponent is not conserved by the routing:
-- all three targets 47,59,71 have exponent one.  Thus exponent is a source
-- discriminator here, not a proved dynamical invariant or causal explanation.
--
-- SOURCE CALIBRATION
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents",
-- arXiv:2602.09135 (2026).
-- DOI: 10.48550/arXiv.2602.09135.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Moonshine.MoonshineEarnOggObserverNonfactorabilityExact as Earn
import DASHI.Moonshine.MonsterOrderExponentCorrectionExact as Exponent
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

sourceLane : Earn.EarnSource → Lane.MonsterPrimeLane
sourceLane Earn.from23 = Lane.p23
sourceLane Earn.from7 = Lane.p7
sourceLane Earn.from11 = Lane.p11

targetLane : Earn.EarnSource → Lane.MonsterPrimeLane
targetLane Earn.from23 = Lane.p47
targetLane Earn.from7 = Lane.p59
targetLane Earn.from11 = Lane.p71

sourceExponentObserver : Earn.EarnSource → Nat
sourceExponentObserver source = Exponent.monsterOrderExponent (sourceLane source)

targetExponent : Earn.EarnSource → Nat
targetExponent source = Exponent.monsterOrderExponent (targetLane source)

source23ExponentIsOne : sourceExponentObserver Earn.from23 ≡ 1
source23ExponentIsOne = refl

source7ExponentIsSix : sourceExponentObserver Earn.from7 ≡ 6
source7ExponentIsSix = refl

source11ExponentIsTwo : sourceExponentObserver Earn.from11 ≡ 2
source11ExponentIsTwo = refl

allHistoricalTargetsHaveExponentOne :
  (source : Earn.EarnSource) → targetExponent source ≡ 1
allHistoricalTargetsHaveExponentOne Earn.from23 = refl
allHistoricalTargetsHaveExponentOne Earn.from7 = refl
allHistoricalTargetsHaveExponentOne Earn.from11 = refl

------------------------------------------------------------------------
-- The exponent observer is a strict refinement of the coarse Ogg/Monster locus
-- on the actual historical source carrier.
------------------------------------------------------------------------

source23And7ExponentDiffer :
  sourceExponentObserver Earn.from23
  ≡ sourceExponentObserver Earn.from7 → ⊥
source23And7ExponentDiffer ()

source7And11ExponentDiffer :
  sourceExponentObserver Earn.from7
  ≡ sourceExponentObserver Earn.from11 → ⊥
source7And11ExponentDiffer ()

source23And11ExponentDiffer :
  sourceExponentObserver Earn.from23
  ≡ sourceExponentObserver Earn.from11 → ⊥
source23And11ExponentDiffer ()

exponentRefinesOggLocus :
  Observer.Refines Earn.locusObserver sourceExponentObserver
exponentRefinesOggLocus left right sameExponent = refl

exponentStrictlyRefinesOggLocus :
  Observer.StrictRefinement Earn.locusObserver sourceExponentObserver
exponentStrictlyRefinesOggLocus =
  Observer.strictRefinement
    exponentRefinesOggLocus
    Earn.from23
    Earn.from7
    refl
    source23And7ExponentDiffer

sourceExponentSeparatesHistoricalSources :
  Observer.Separating sourceExponentObserver
sourceExponentSeparatesHistoricalSources Earn.from23 Earn.from23 same = refl
sourceExponentSeparatesHistoricalSources Earn.from23 Earn.from7 ()
sourceExponentSeparatesHistoricalSources Earn.from23 Earn.from11 ()
sourceExponentSeparatesHistoricalSources Earn.from7 Earn.from23 ()
sourceExponentSeparatesHistoricalSources Earn.from7 Earn.from7 same = refl
sourceExponentSeparatesHistoricalSources Earn.from7 Earn.from11 ()
sourceExponentSeparatesHistoricalSources Earn.from11 Earn.from23 ()
sourceExponentSeparatesHistoricalSources Earn.from11 Earn.from7 ()
sourceExponentSeparatesHistoricalSources Earn.from11 Earn.from11 same = refl

------------------------------------------------------------------------
-- Positive result: the historical routing factors through source exponent.
------------------------------------------------------------------------

routeBySourceExponent : Nat → Nat
routeBySourceExponent 1 = 47
routeBySourceExponent 2 = 71
routeBySourceExponent 6 = 59
routeBySourceExponent _ = 0

routeBySourceExponentFactorsHistoricalTargets :
  (source : Earn.EarnSource) →
  routeBySourceExponent (sourceExponentObserver source)
  ≡ Earn.targetPrime source
routeBySourceExponentFactorsHistoricalTargets Earn.from23 = refl
routeBySourceExponentFactorsHistoricalTargets Earn.from7 = refl
routeBySourceExponentFactorsHistoricalTargets Earn.from11 = refl

record FactorsEarnTargetThroughExponent : Set where
  constructor factorsEarnTargetThroughExponent
  field
    route : Nat → Nat
    factors :
      (source : Earn.EarnSource) →
      route (sourceExponentObserver source) ≡ Earn.targetPrime source

open FactorsEarnTargetThroughExponent public

historicalRoutingFactorsThroughSourceExponent :
  FactorsEarnTargetThroughExponent
historicalRoutingFactorsThroughSourceExponent =
  factorsEarnTargetThroughExponent
    routeBySourceExponent
    routeBySourceExponentFactorsHistoricalTargets

------------------------------------------------------------------------
-- But the substitution is not exponent-preserving.  Only 23 -> 47 preserves
-- exponent; the other two collapse to target exponent one.
------------------------------------------------------------------------

from23PreservesMonsterExponent :
  sourceExponentObserver Earn.from23 ≡ targetExponent Earn.from23
from23PreservesMonsterExponent = refl

from7DoesNotPreserveMonsterExponent :
  sourceExponentObserver Earn.from7 ≡ targetExponent Earn.from7 → ⊥
from7DoesNotPreserveMonsterExponent ()

from11DoesNotPreserveMonsterExponent :
  sourceExponentObserver Earn.from11 ≡ targetExponent Earn.from11 → ⊥
from11DoesNotPreserveMonsterExponent ()

record MoonshineEarnExponentObserverBoundary : Set where
  constructor moonshineEarnExponentObserverBoundary
  field
    exponentStrictlyRefinesOggOnHistoricalSources : Bool
    exponentSeparatesThreeHistoricalSources : Bool
    historicalRoutingFactorsThroughSourceExponent : Bool
    allThreeTargetsHaveExponentOne : Bool
    routingUniformlyPreservesMonsterExponent : Bool
    factorizationProvesMoonshineMechanism : Bool

canonicalMoonshineEarnExponentObserverBoundary :
  MoonshineEarnExponentObserverBoundary
canonicalMoonshineEarnExponentObserverBoundary =
  moonshineEarnExponentObserverBoundary
    true true true true false false
