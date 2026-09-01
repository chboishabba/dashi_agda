module DASHI.Finance.TradingPermissionConsumerQuotientExact where

open import DASHI.Core.Prelude

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Foundations.Base369BinaryTernaryRefinement as Refinement
import DASHI.Trading.PermissionKernel as Legacy
import DASHI.Finance.TradingPermissionActionRefinementExact as Action

------------------------------------------------------------------------
-- Consumer quotient for trading permissions.
--
-- Permission is the coarse observation.  Entry/reduction role and current
-- exposure are retained upstairs until an execution consumer actually asks for
-- them.  This is the trading analogue of retaining a residual world/ordering
-- fibre instead of eagerly choosing a complete state.
------------------------------------------------------------------------

data BinaryOrderRole : Set where
  exposureIncreasingRole : BinaryOrderRole
  riskReducingRole : BinaryOrderRole

data ExposureOrientation : Set where
  shortOrientation : ExposureOrientation
  flatOrientation : ExposureOrientation
  longOrientation : ExposureOrientation

record FinePermissionWorld : Set where
  constructor finePermissionWorld
  field
    permission : Legacy.Permission
    orderRole : BinaryOrderRole
    exposure : ExposureOrientation

open FinePermissionWorld public

permissionObserver : FinePermissionWorld → Legacy.Permission
permissionObserver = permission

roleObserver : FinePermissionWorld → BinaryOrderRole
roleObserver = orderRole

exposureObserver : FinePermissionWorld → ExposureOrientation
exposureObserver = exposure

roleRefinedObserver :
  FinePermissionWorld → Legacy.Permission × BinaryOrderRole
roleRefinedObserver = Observer.pairObserver permissionObserver roleObserver

exposureRefinedObserver :
  FinePermissionWorld → Legacy.Permission × ExposureOrientation
exposureRefinedObserver = Observer.pairObserver permissionObserver exposureObserver

fullObserver :
  FinePermissionWorld →
  (Legacy.Permission × BinaryOrderRole) × ExposureOrientation
fullObserver world = roleRefinedObserver world , exposureObserver world

------------------------------------------------------------------------
-- Canonical BAN fibre.
------------------------------------------------------------------------

banFlat : FinePermissionWorld
banFlat = finePermissionWorld Legacy.BAN riskReducingRole flatOrientation

banLong : FinePermissionWorld
banLong = finePermissionWorld Legacy.BAN riskReducingRole longOrientation

banShort : FinePermissionWorld
banShort = finePermissionWorld Legacy.BAN riskReducingRole shortOrientation

banPermissionCollisionFlatLong :
  permissionObserver banFlat ≡ permissionObserver banLong
banPermissionCollisionFlatLong = refl

banPermissionCollisionLongShort :
  permissionObserver banLong ≡ permissionObserver banShort
banPermissionCollisionLongShort = refl

flatLongExposureDiffer :
  exposureObserver banFlat ≡ exposureObserver banLong → ⊥
flatLongExposureDiffer ()

longShortExposureDiffer :
  exposureObserver banLong ≡ exposureObserver banShort → ⊥
longShortExposureDiffer ()

permissionToExposureStrictRefinement :
  Observer.StrictRefinement permissionObserver exposureRefinedObserver
permissionToExposureStrictRefinement =
  Observer.strictPairRefinement
    permissionObserver
    exposureObserver
    banFlat
    banLong
    refl
    flatLongExposureDiffer

------------------------------------------------------------------------
-- Execution query semantics.
--
-- The same coarse BAN observation answers the 'may I increase risk?' query,
-- but it is not sufficient to answer the concrete execution-intent query.
------------------------------------------------------------------------

data TradeConsumerQuery : Set where
  mayIncreaseRiskQuery : TradeConsumerQuery
  concreteExecutionQuery : TradeConsumerQuery

data TradeConsumerAnswer : Set where
  increaseForbidden : TradeConsumerAnswer
  keepCurrent : TradeConsumerAnswer
  reduceCurrent : TradeConsumerAnswer

consumerAnswer : TradeConsumerQuery → FinePermissionWorld → TradeConsumerAnswer
consumerAnswer mayIncreaseRiskQuery world with permission world
... | Legacy.ACT = keepCurrent
... | Legacy.HOLD = increaseForbidden
... | Legacy.BAN = increaseForbidden
consumerAnswer concreteExecutionQuery world with permission world | exposure world
... | Legacy.BAN | flatOrientation = keepCurrent
... | Legacy.BAN | longOrientation = reduceCurrent
... | Legacy.BAN | shortOrientation = reduceCurrent
... | Legacy.HOLD | orientation = keepCurrent
... | Legacy.ACT | orientation = keepCurrent

banFlatLongConcreteAnswersDiffer :
  consumerAnswer concreteExecutionQuery banFlat
  ≡ consumerAnswer concreteExecutionQuery banLong → ⊥
banFlatLongConcreteAnswersDiffer ()

permissionCannotDetermineConcreteBANExecution :
  NF.NonFactorabilityWitness
    permissionObserver
    (consumerAnswer concreteExecutionQuery)
permissionCannotDetermineConcreteBANExecution =
  NF.nonFactorabilityWitness
    banFlat
    banLong
    refl
    banFlatLongConcreteAnswersDiffer

noPermissionOnlyConcreteExecutionCompiler :
  NF.FactorsThrough
    permissionObserver
    (consumerAnswer concreteExecutionQuery) → ⊥
noPermissionOnlyConcreteExecutionCompiler =
  NF.witnessRulesOutEveryFlatFactorisation
    permissionCannotDetermineConcreteBANExecution

------------------------------------------------------------------------
-- Residual fibre: a consumer that asks only for permission legitimately sees
-- one BAN class while the unresolved exposure alternatives remain upstairs.
------------------------------------------------------------------------

BANResidualFibre : Set
BANResidualFibre = Observer.ObservationFibre permissionObserver Legacy.BAN

banFlatInResidualFibre : BANResidualFibre
banFlatInResidualFibre = banFlat , refl

banLongInResidualFibre : BANResidualFibre
banLongInResidualFibre = banLong , refl

banShortInResidualFibre : BANResidualFibre
banShortInResidualFibre = banShort , refl

------------------------------------------------------------------------
-- 3 / 6 / 9 / 18 resolution interpretation.
--
-- This imports only the existing resolution lattice.  We do NOT identify the
-- trading carriers with Base369 cyclic carriers by cardinality.
--
--   3  = permission
--   6  = permission × binary order role
--   9  = permission × ternary exposure orientation
--   18 = permission × role × exposure
------------------------------------------------------------------------

record TradingResolutionInterpretation : Set where
  constructor tradingResolutionInterpretation
  field
    permissionResolution : Refinement.Resolution23
    roleResolution : Refinement.Resolution23
    exposureResolution : Refinement.Resolution23
    fullResolution : Refinement.Resolution23
    permissionIsPhase3Shape : permissionResolution ≡ Refinement.phase3Resolution
    roleIsPhase6Shape : roleResolution ≡ Refinement.phase6Resolution
    exposureIsPhase9Shape : exposureResolution ≡ Refinement.phase9Resolution
    fullIsPhase18Shape : fullResolution ≡ Refinement.phase18Resolution
    carrierIdentityAsserted : Bool
    carrierIdentityAssertedIsFalse : carrierIdentityAsserted ≡ false

open TradingResolutionInterpretation public

canonicalTradingResolutionInterpretation : TradingResolutionInterpretation
canonicalTradingResolutionInterpretation =
  tradingResolutionInterpretation
    Refinement.phase3Resolution
    Refinement.phase6Resolution
    Refinement.phase9Resolution
    Refinement.phase18Resolution
    refl refl refl refl
    false refl

roleThenExposureResolutionCommutes :
  Refinement.ternaryRefine
    (Refinement.binaryRefine Refinement.phase3Resolution)
  ≡ Refinement.phase18Resolution
roleThenExposureResolutionCommutes = refl

exposureThenRoleResolutionCommutes :
  Refinement.binaryRefine
    (Refinement.ternaryRefine Refinement.phase3Resolution)
  ≡ Refinement.phase18Resolution
exposureThenRoleResolutionCommutes = refl

------------------------------------------------------------------------
-- Bracket principle.
------------------------------------------------------------------------

record ConsumerQuotientBoundary : Set where
  constructor consumerQuotientBoundary
  field
    permissionMustEagerlyChooseExecution : Bool
    permissionMustEagerlyChooseExecutionIsFalse :
      permissionMustEagerlyChooseExecution ≡ false
    residualAlternativesMayPersistUntilConsumerDistinguishes : Bool
    residualAlternativesMayPersistUntilConsumerDistinguishesIsTrue :
      residualAlternativesMayPersistUntilConsumerDistinguishes ≡ true
    cardinalityEqualityImpliesCarrierIdentity : Bool
    cardinalityEqualityImpliesCarrierIdentityIsFalse :
      cardinalityEqualityImpliesCarrierIdentity ≡ false

canonicalConsumerQuotientBoundary : ConsumerQuotientBoundary
canonicalConsumerQuotientBoundary =
  consumerQuotientBoundary false refl true refl false refl

boundaryStatement : String
boundaryStatement =
  "BAN is a coarse consumer quotient, not a concrete order. Flat/long/short and entry/reduction alternatives remain in the residual fibre until an execution consumer requests the distinctions needed to compile a lawful order."
