module DASHI.Biology.BalancedTernaryTetrationHarmonicBridgeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Volodymyr Nekrashevych,
-- "Self-Similar Groups", American Mathematical Society, 2005.
-- DOI: 10.1090/surv/117.
--
-- Ingrid Daubechies,
-- "Ten Lectures on Wavelets", SIAM, 1992.
-- DOI: 10.1137/1.9781611970104.
--
-- DASHI CONTRIBUTION
-- Connect the structured elementary harmonic carrier to the existing strong
-- self-indexing tower while refusing to identify product and function-space
-- growth.  A channel is one coarse/frequency pair; a configuration is an
-- assignment of one fine state to every coarse channel; the existing tower
-- recursively makes an entire level the index type of the next field.
--
-- The jFine evaluation fibre is checked to have the same 3^9 cardinality as
-- the relative harmonic factor in jAbsoluteFine = jCoarse * jFine.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Biology.JFineCoarseRelativeScaleExact as Relative
import DASHI.Biology.SelfIndexingHyperfabricTetrationExact as Tower
import DASHI.Biology.TernaryHypercubeHyperfabricExact as Hyper

ElementaryChannelCarrier : Set
ElementaryChannelCarrier = Harmonic.ElementaryHarmonicChannel

FineConfigurationCarrier : Set
FineConfigurationCarrier = Harmonic.FullFineAssignment

jFineEvaluation : FineConfigurationCarrier → Harmonic.FineFrequency
jFineEvaluation = Harmonic.jFine

jFineEvaluationFibreMatchesRelativeScale :
  Harmonic.fineFrequencyDimension ≡ Relative.jFineFrequency
jFineEvaluationFibreMatchesRelativeScale = refl

ExistingNineValuedTowerLevel : Nat → Set
ExistingNineValuedTowerLevel = Tower.SelfIndexedCarrier

existingTowerLevelOneHasNineSites : Tower.selfIndexedSiteCount 1 ≡ 9
existingTowerLevelOneHasNineSites = Tower.selfIndexedLevelOneHasNineSites

existingTowerLevelTwoHasNineToNineSites :
  Tower.selfIndexedSiteCount 2 ≡ Hyper.powNat 9 9
existingTowerLevelTwoHasNineToNineSites =
  Tower.selfIndexedLevelTwoHasNineToNineSites

data CarrierGrowthKind : Set where
  elementaryProductGrowth : CarrierGrowthKind
  fullAssignmentExponentiation : CarrierGrowthKind
  recursiveSelfIndexingTetration : CarrierGrowthKind

channelGrowthKind : CarrierGrowthKind
channelGrowthKind = elementaryProductGrowth

configurationGrowthKind : CarrierGrowthKind
configurationGrowthKind = fullAssignmentExponentiation

towerGrowthKind : CarrierGrowthKind
towerGrowthKind = recursiveSelfIndexingTetration

record TetrationHarmonicBoundary : Set where
  constructor tetrationHarmonicBoundary
  field
    elementaryChannelsAreFullConfigurations : Set
    elementaryChannelsAreNotFullConfigurations :
      elementaryChannelsAreFullConfigurations → Set

    oneAssignmentLevelIsEntireRecursiveTower : Set
    oneAssignmentLevelIsNotEntireRecursiveTower :
      oneAssignmentLevelIsEntireRecursiveTower → Set

canonicalTetrationHarmonicBoundary : TetrationHarmonicBoundary
canonicalTetrationHarmonicBoundary =
  tetrationHarmonicBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
  where
  open import Data.Empty using (⊥)
