module DASHI.Biology.FruitEmbodiedEnergyHistoryFibreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)

import DASHI.Physics.Units.SI as SI
import DASHI.Core.HistoryConditionedChoiceExact as HistoryChoice
import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Biology.FruitIntegrityAdversarialFibreExact as Fruit
import DASHI.Biology.FruitLESAdversarialConsumerBridgeExact as FruitLES

------------------------------------------------------------------------
-- PLANT PARTS AS EMBODIED-ENERGY / RESOURCE INVESTMENT CARRIERS
--
-- A fruit is not only an information-bearing surface.  It is material that the
-- plant has constructed and maintained using finite energetic/resource flows.
-- We therefore retain an SI-typed embodied-energy coordinate on the history.
--
-- This is a bookkeeping/consumer coordinate, not a claim that all plant value
-- is reducible to joules or that one measured calorific value reconstructs the
-- complete physiological cost of producing a fruit.
------------------------------------------------------------------------

EmbodiedEnergy : Set
EmbodiedEnergy = SI.Quantity SI.Energy SI.unitScale

joules : Nat → EmbodiedEnergy
joules = SI.posQ

data PlantPart : Set where
  wholePlant stem leaf flower fruitPart seedPart : PlantPart

data InvestmentHistory : Set where
  intactDevelopment
  repairedAfterDamage
  repeatedPestPressure : InvestmentHistory

data FutureVulnerability : Set where
  lowerVulnerability higherVulnerability : FutureVulnerability

data ReproductiveContinuation : Set where
  retainedReproductiveOption reducedReproductiveOption : ReproductiveContinuation

record PlantPartHistory : Set where
  constructor plant-part-history
  field
    part : PlantPart
    fruitState : FruitLES.FruitEcologicalState
    embodiedEnergy : EmbodiedEnergy
    investmentHistory : InvestmentHistory
    vulnerability : FutureVulnerability
    reproductiveContinuation : ReproductiveContinuation

open PlantPartHistory public

visibleFruitSurface : PlantPartHistory → Fruit.SurfaceIntegrity
visibleFruitSurface state =
  FruitLES.surfaceRepresentation (fruitState state)

------------------------------------------------------------------------
-- Two histories with the same present fruit surface and same present host
-- outcome, but different energetic investment and future vulnerability.
--
-- This is the trajectory-fibre case: even when the current host consumer has
-- not yet diverged, history may matter to the continuation cone.
------------------------------------------------------------------------

lowCostIntactHistory : PlantPartHistory
lowCostIntactHistory =
  plant-part-history
    fruitPart
    FruitLES.hostIntactNoPest
    (joules 10)
    intactDevelopment
    lowerVulnerability
    retainedReproductiveOption

repairLoadedIntactHistory : PlantPartHistory
repairLoadedIntactHistory =
  plant-part-history
    fruitPart
    FruitLES.hostIntactNoPest
    (joules 18)
    repairedAfterDamage
    higherVulnerability
    reducedReproductiveOption

samePresentFruitSurface :
  visibleFruitSurface lowCostIntactHistory ≡
  visibleFruitSurface repairLoadedIntactHistory
samePresentFruitSurface = refl

samePresentHostOutcome :
  FruitLES.roleOutcome FruitLES.hostPlant (fruitState lowCostIntactHistory) ≡
  FruitLES.roleOutcome FruitLES.hostPlant (fruitState repairLoadedIntactHistory)
samePresentHostOutcome = refl

embodiedEnergyDiffers :
  embodiedEnergy lowCostIntactHistory ≡
  embodiedEnergy repairLoadedIntactHistory →
  ⊥
embodiedEnergyDiffers ()

futureVulnerabilityDiffers :
  vulnerability lowCostIntactHistory ≡
  vulnerability repairLoadedIntactHistory →
  ⊥
futureVulnerabilityDiffers ()

reproductiveContinuationDiffers :
  reproductiveContinuation lowCostIntactHistory ≡
  reproductiveContinuation repairLoadedIntactHistory →
  ⊥
reproductiveContinuationDiffers ()

------------------------------------------------------------------------
-- History-conditioned continuation surface reuses the canonical core owner.
------------------------------------------------------------------------

fruitHistoryFutureConeSurface :
  HistoryChoice.HistoryConditionedFutureConeSurface
fruitHistoryFutureConeSurface =
  record
    { FutureHistory = PlantPartHistory
    ; FutureObservation = Fruit.SurfaceIntegrity
    ; FutureConeCode = FutureVulnerability
    ; observeFutureHistory = visibleFruitSurface
    ; futureCone = vulnerability
    ; futureReading =
        "The same visible fruit surface may hide different investment histories and embodied energetic costs, with different future vulnerability."
    }

fruitHistoryFutureConeWitness :
  HistoryChoice.SameObservationDifferentFutureCone
    fruitHistoryFutureConeSurface
fruitHistoryFutureConeWitness =
  record
    { futureLeftHistory = lowCostIntactHistory
    ; futureRightHistory = repairLoadedIntactHistory
    ; futureSameObservation = refl
    ; futureConesDiffer = λ ()
    }

visibleFruitSurfaceCannotDetermineFutureVulnerability :
  NonFactor.FactorsThrough visibleFruitSurface vulnerability → ⊥
visibleFruitSurfaceCannotDetermineFutureVulnerability =
  HistoryChoice.futureConeCannotDescendThroughPresentObservation
    fruitHistoryFutureConeWitness

------------------------------------------------------------------------
-- Embodied energy itself is also not recoverable from the visible surface.
------------------------------------------------------------------------

visibleFruitSurfaceCannotRecoverEmbodiedEnergy :
  NonFactor.FactorsThrough visibleFruitSurface embodiedEnergy → ⊥
visibleFruitSurfaceCannotRecoverEmbodiedEnergy =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      lowCostIntactHistory
      repairLoadedIntactHistory
      refl
      embodiedEnergyDiffers)

visibleFruitSurfaceCannotRecoverReproductiveContinuation :
  NonFactor.FactorsThrough
    visibleFruitSurface
    reproductiveContinuation →
  ⊥
visibleFruitSurfaceCannotRecoverReproductiveContinuation =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      lowCostIntactHistory
      repairLoadedIntactHistory
      refl
      reproductiveContinuationDiffers)

------------------------------------------------------------------------
-- Adversarial energetic interpretation.
--
-- Pest extraction can matter to the host in at least two independent ways:
-- direct reproductive damage and diversion/destruction of prior embodied
-- investment.  The latter does not require seed compromise in the same step.
------------------------------------------------------------------------

data EnergyCaptureRelation : Set where
  noExternalCapture hostInvestmentCaptured : EnergyCaptureRelation

record EnergeticExploitOverlay : Set where
  constructor energetic-exploit-overlay
  field
    ecologicalState : FruitLES.FruitEcologicalState
    investedEnergy : EmbodiedEnergy
    captureRelation : EnergyCaptureRelation
    hostSeedOutcome : Fruit.SeedProtection

open EnergeticExploitOverlay public

partialConsumptionCanCaptureInvestmentWithoutSeedLoss :
  EnergeticExploitOverlay
partialConsumptionCanCaptureInvestmentWithoutSeedLoss =
  energetic-exploit-overlay
    FruitLES.partialLegitimateConsumption
    (joules 14)
    hostInvestmentCaptured
    Fruit.seedProtected

concealedExploitCanCaptureInvestmentAndCompromiseSeed :
  EnergeticExploitOverlay
concealedExploitCanCaptureInvestmentAndCompromiseSeed =
  energetic-exploit-overlay
    FruitLES.concealedPestExploit
    (joules 16)
    hostInvestmentCaptured
    Fruit.seedCompromised

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data EmbodiedEnergyMeansEcologicalValuePermission : Set where

data SameSurfaceMeansSameEnergeticInvestmentPermission : Set where

data EnergyCaptureMeansSeedCompromisePermission : Set where

data HigherInvestmentMeansHigherFitnessPermission : Set where

embodiedEnergyDoesNotEqualEcologicalValue :
  EmbodiedEnergyMeansEcologicalValuePermission → ⊥
embodiedEnergyDoesNotEqualEcologicalValue ()

sameSurfaceDoesNotMeanSameEnergeticInvestment :
  SameSurfaceMeansSameEnergeticInvestmentPermission → ⊥
sameSurfaceDoesNotMeanSameEnergeticInvestment ()

energyCaptureDoesNotByItselfMeanSeedCompromise :
  EnergyCaptureMeansSeedCompromisePermission → ⊥
energyCaptureDoesNotByItselfMeanSeedCompromise ()

higherInvestmentDoesNotByItselfMeanHigherFitness :
  HigherInvestmentMeansHigherFitnessPermission → ⊥
higherInvestmentDoesNotByItselfMeanHigherFitness ()

record FruitEmbodiedEnergyHistoryBoundary : Set where
  constructor fruit-embodied-energy-history-boundary
  field
    plantPartMayCarryEmbodiedEnergyCoordinate : Bool
    fruitSurfaceMayEraseEnergeticInvestmentHistory : Bool
    sameCurrentHostOutcomeMayHideDifferentFutureVulnerability : Bool
    pestCanCaptureHostInvestmentWithoutImmediateSeedLoss : Bool
    embodiedEnergyIsIdenticalToEcologicalValue : Bool
    energeticInvestmentAloneDeterminesFitness : Bool

canonicalFruitEmbodiedEnergyHistoryBoundary :
  FruitEmbodiedEnergyHistoryBoundary
canonicalFruitEmbodiedEnergyHistoryBoundary =
  fruit-embodied-energy-history-boundary
    true true true true false false
