module DASHI.Economics.AICapitalObserverNonDescent20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ConsumerFibreRepairExact as Repair

------------------------------------------------------------------------
-- AI-CAPITAL HEADLINE-OBSERVER NON-DESCENT
--
-- Productive cross-pollination from the repository's canonical consumer-
-- descent / fibre-repair machinery.  The point is not merely that some
-- economic data are "missing".  A coarse headline observer can literally have
-- a fibre containing states with different capital-recovery outcomes.
-- Therefore capital recovery cannot factor through that observer, and every
-- sufficient refinement must separate the witnessed collision.
--
-- The finite worlds below are DASHI synthetic countermodels.  They are not
-- empirical claims about a named company.  Their role is to prove the logical
-- insufficiency of headline growth/usage/valuation/market-price surfaces.
------------------------------------------------------------------------

data CapitalWorld : Set where
  externalPositive : CapitalWorld
  internalPositive : CapitalWorld
  externalNegative : CapitalWorld

data HeadlineSurface : Set where
  sameHeadlineBoom : HeadlineSurface

data RecoveryOutcome : Set where
  recoversCapital : RecoveryOutcome
  doesNotRecoverCapital : RecoveryOutcome

headlineObserver : CapitalWorld → HeadlineSurface
headlineObserver externalPositive = sameHeadlineBoom
headlineObserver internalPositive = sameHeadlineBoom
headlineObserver externalNegative = sameHeadlineBoom

terminalExternalObserver : CapitalWorld → Bool
terminalExternalObserver externalPositive = true
terminalExternalObserver internalPositive = false
terminalExternalObserver externalNegative = true

positiveCapitalSpreadObserver : CapitalWorld → Bool
positiveCapitalSpreadObserver externalPositive = true
positiveCapitalSpreadObserver internalPositive = true
positiveCapitalSpreadObserver externalNegative = false

capitalRecoveryConsumer : CapitalWorld → RecoveryOutcome
capitalRecoveryConsumer externalPositive = recoversCapital
capitalRecoveryConsumer internalPositive = doesNotRecoverCapital
capitalRecoveryConsumer externalNegative = doesNotRecoverCapital

------------------------------------------------------------------------
-- Two independent collisions under the SAME headline surface.
------------------------------------------------------------------------

terminalPayerCollision :
  Descent.ConsumerNonDescentWitness headlineObserver capitalRecoveryConsumer
terminalPayerCollision =
  Descent.consumerNonDescentWitness
    externalPositive
    internalPositive
    refl
    (λ ())

capitalSpreadCollision :
  Descent.ConsumerNonDescentWitness headlineObserver capitalRecoveryConsumer
capitalSpreadCollision =
  Descent.consumerNonDescentWitness
    externalPositive
    externalNegative
    refl
    (λ ())

headlineSurfaceCannotDetermineCapitalRecovery :
  Descent.ConsumerSufficient headlineObserver capitalRecoveryConsumer → ⊥
headlineSurfaceCannotDetermineCapitalRecovery =
  Descent.nonDescentWitnessBlocksSufficiency terminalPayerCollision

headlineMetricsDoNotAutoFactorCapitalRecovery :
  Descent.FactorsThrough headlineObserver capitalRecoveryConsumer → ⊥
headlineMetricsDoNotAutoFactorCapitalRecovery =
  Descent.nonDescentWitnessBlocksFactorization terminalPayerCollision

------------------------------------------------------------------------
-- Every sufficient repair must separate the relevant witnessed states.
-- This is stronger than saying a particular hand-picked metric would help.
------------------------------------------------------------------------

everyTerminalPayerRepairMustSeparateWitness :
  ∀ {Refinement : Set}
    (refine : CapitalWorld → Refinement) →
  Repair.RefinementRepairs headlineObserver refine capitalRecoveryConsumer →
  refine externalPositive ≡ refine internalPositive →
  ⊥
everyTerminalPayerRepairMustSeparateWitness refine repaired sameRefinement =
  Repair.refinementRepairSeparatesWitness
    terminalPayerCollision repaired sameRefinement

everyCapitalSpreadRepairMustSeparateWitness :
  ∀ {Refinement : Set}
    (refine : CapitalWorld → Refinement) →
  Repair.RefinementRepairs headlineObserver refine capitalRecoveryConsumer →
  refine externalPositive ≡ refine externalNegative →
  ⊥
everyCapitalSpreadRepairMustSeparateWitness refine repaired sameRefinement =
  Repair.refinementRepairSeparatesWitness
    capitalSpreadCollision repaired sameRefinement

------------------------------------------------------------------------
-- Semantic calibration of the two hidden axes.
------------------------------------------------------------------------

terminalPayerSeparatesItsCollision :
  terminalExternalObserver externalPositive ≡ terminalExternalObserver internalPositive → ⊥
terminalPayerSeparatesItsCollision ()

capitalSpreadSeparatesItsCollision :
  positiveCapitalSpreadObserver externalPositive ≡
    positiveCapitalSpreadObserver externalNegative → ⊥
capitalSpreadSeparatesItsCollision ()

record CapitalObserverNonDescentBoundary : Set where
  constructor capitalObserverNonDescentBoundary
  field
    headlineGrowthCanBeIdentical : Bool
    headlineUsageCanBeIdentical : Bool
    headlineValuationCanBeIdentical : Bool
    headlineMarketPriceCanBeIdentical : Bool
    terminalPayerCanStillChangeRecoveryOutcome : Bool
    capitalSpreadCanStillChangeRecoveryOutcome : Bool
    headlineSurfaceSufficientForRecovery : Bool
    oneSeparatingCoordinateProvesGlobalSufficiency : Bool
    syntheticCountermodelIsNamedCompanyEvidence : Bool

open CapitalObserverNonDescentBoundary public

canonicalCapitalObserverBoundary : CapitalObserverNonDescentBoundary
canonicalCapitalObserverBoundary = capitalObserverNonDescentBoundary
  true true true true true true false false false

headlineSurfaceSufficiencyRemainsFalse :
  headlineSurfaceSufficientForRecovery canonicalCapitalObserverBoundary ≡ false
headlineSurfaceSufficiencyRemainsFalse = refl

boundary : String
boundary =
  "Capital recovery does not descend through a headline-only AI observer. DASHI owns explicit finite collisions in which revenue/usage/valuation/market-price headlines are identical while terminal-payer provenance or capital-spread sign changes the recovery outcome. The canonical fibre-repair theorem therefore forces every sufficient refinement to separate those collisions. This is a logical non-factorability result, not empirical proof that any named firm is non-viable."
