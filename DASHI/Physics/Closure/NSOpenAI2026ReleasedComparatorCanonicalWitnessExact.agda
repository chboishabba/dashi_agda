module DASHI.Physics.Closure.NSOpenAI2026ReleasedComparatorCanonicalWitnessExact where

------------------------------------------------------------------------
-- C/D RELEASED COMPARATOR WITNESS SHAPE -> CANONICAL DASHI WITNESS
--
-- This is the theorem-preserving adapter after the source scalar/space carrier
-- has been identified with DASHI's canonical R^3 carrier.
--
-- We retain the released comparator's space-first history orientation, define
-- source-shaped global solution records, and prove that every canonical DASHI
-- global solution induces one of those source-shaped solutions by the exact
-- argument-transposition theorems.  Therefore the released no-global-solution
-- conclusion transports to the canonical Clay C/D consumers.
--
-- The only cross-prover representation debt left OUTSIDE this file is the
-- scalar/space identity:
--
--   Mathlib Real / EuclideanSpace Real (Fin 3)
--       <-> Bishop Real / Canonical.R3Point.
--
-- No PDE theorem is reproved and no external Lean proof is silently imported.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import Real as BishopReal

import DASHI.Physics.Closure.NSClayLiteralABCDExact as Clay
import DASHI.Physics.Closure.NSCanonicalEuclideanPeriodicSemanticCarriersExact as Canonical
import DASHI.Physics.Closure.NSOpenAI2026ReleasedComparatorCanonicalShapeExact as Shape
import DASHI.Physics.Closure.NSOpenAI2026ReleasedCDCanonicalReconstructionExact as Reconstruct

------------------------------------------------------------------------
-- C / source-oriented global solution.
------------------------------------------------------------------------

record ReleasedGlobalSolutionC
    (S : Canonical.CanonicalNSSemantics)
    (viscosity : BishopReal.ℝ)
    (initial : Shape.ReleasedInitialFieldShape)
    (forcing : Shape.ReleasedVectorHistoryShape) : Set₁ where
  field
    velocity : Shape.ReleasedVectorHistoryShape
    pressure : Shape.ReleasedScalarHistoryShape

    velocitySmooth :
      Canonical.SmoothVelocityHistory S
        (Shape.releasedVectorHistoryToCanonical velocity)

    pressureSmooth :
      Canonical.SmoothPressureHistory S
        (Shape.releasedPressureHistoryToCanonical pressure)

    solvesEquation :
      Canonical.SolvesForcedNS S viscosity
        (Shape.releasedVectorHistoryToCanonical velocity)
        (Shape.releasedPressureHistoryToCanonical pressure)
        initial
        (Shape.releasedForcingToCanonical forcing)

    incompressible :
      Canonical.DivergenceFreeHistory S
        (Shape.releasedVectorHistoryToCanonical velocity)

    initialTrace :
      Canonical.AttainsInitialDatum S
        (Shape.releasedVectorHistoryToCanonical velocity)
        initial

    boundedEnergy :
      Canonical.BoundedKineticEnergy S
        (Shape.releasedVectorHistoryToCanonical velocity)

open ReleasedGlobalSolutionC public

canonicalSolutionToReleasedC :
  (S : Canonical.CanonicalNSSemantics) →
  (viscosity : BishopReal.ℝ) →
  (initial : Shape.ReleasedInitialFieldShape) →
  (forcing : Shape.ReleasedVectorHistoryShape) →
  Clay.FeffermanEuclideanForcedGlobalSolution
    (Canonical.canonicalEuclideanC S)
    viscosity initial
    (Shape.releasedForcingToCanonical forcing) →
  ReleasedGlobalSolutionC S viscosity initial forcing
canonicalSolutionToReleasedC S viscosity initial forcing solution = record
  { velocity =
      Shape.canonicalVectorHistoryToReleased
        (Clay.velocityC solution)
  ; pressure =
      Shape.canonicalPressureHistoryToReleased
        (Clay.pressureC solution)
  ; velocitySmooth = Clay.velocitySmoothC solution
  ; pressureSmooth = Clay.pressureSmoothC solution
  ; solvesEquation = Clay.solvesEquationC solution
  ; incompressible = Clay.incompressibleC solution
  ; initialTrace = Clay.initialTraceC solution
  ; boundedEnergy = Clay.boundedEnergyC solution
  }

record ReleasedComparatorCWitness
    (S : Canonical.CanonicalNSSemantics)
    (viscosity : BishopReal.ℝ) : Set₁ where
  field
    initial : Shape.ReleasedInitialFieldShape
    forcing : Shape.ReleasedVectorHistoryShape

    initialSmooth :
      Canonical.SmoothSpatialVector S initial
    initialDivergenceFree :
      Canonical.DivergenceFreeSpatial S initial
    initialRapidDecay :
      Canonical.RapidSpatialDecay S initial

    forcingSmooth :
      Canonical.SmoothForcingHistory S
        (Shape.releasedForcingToCanonical forcing)
    forcingRapidDecay :
      Canonical.RapidSpaceTimeDecay S
        (Shape.releasedForcingToCanonical forcing)

    noReleasedGlobalSolution :
      ReleasedGlobalSolutionC S viscosity initial forcing → ⊥

open ReleasedComparatorCWitness public

releasedComparatorCToCanonicalReconstruction :
  (S : Canonical.CanonicalNSSemantics) →
  (viscosity : BishopReal.ℝ) →
  ReleasedComparatorCWitness S viscosity →
  Reconstruct.ReleasedCanonicalCReconstruction S viscosity
releasedComparatorCToCanonicalReconstruction S viscosity witness = record
  { Reconstruct.initial = ReleasedComparatorCWitness.initial witness
  ; Reconstruct.forcing =
      Shape.releasedForcingToCanonical
        (ReleasedComparatorCWitness.forcing witness)
  ; Reconstruct.initialSmooth =
      ReleasedComparatorCWitness.initialSmooth witness
  ; Reconstruct.initialDivergenceFree =
      ReleasedComparatorCWitness.initialDivergenceFree witness
  ; Reconstruct.initialRapidDecay =
      ReleasedComparatorCWitness.initialRapidDecay witness
  ; Reconstruct.forcingSmooth =
      ReleasedComparatorCWitness.forcingSmooth witness
  ; Reconstruct.forcingRapidSpaceTimeDecay =
      ReleasedComparatorCWitness.forcingRapidDecay witness
  ; Reconstruct.noGlobalBoundedEnergySmoothSolution =
      λ solution →
        ReleasedComparatorCWitness.noReleasedGlobalSolution witness
          (canonicalSolutionToReleasedC
            S viscosity
            (ReleasedComparatorCWitness.initial witness)
            (ReleasedComparatorCWitness.forcing witness)
            solution)
  }

------------------------------------------------------------------------
-- D / source-oriented periodic global solution.
------------------------------------------------------------------------

record ReleasedGlobalSolutionD
    (S : Canonical.CanonicalNSSemantics)
    (viscosity : BishopReal.ℝ)
    (initial : Shape.ReleasedInitialFieldShape)
    (forcing : Shape.ReleasedVectorHistoryShape) : Set₁ where
  field
    velocity : Shape.ReleasedVectorHistoryShape
    pressure : Shape.ReleasedScalarHistoryShape

    velocitySmooth :
      Canonical.SmoothVelocityHistory S
        (Shape.releasedVectorHistoryToCanonical velocity)

    pressureSmooth :
      Canonical.SmoothPressureHistory S
        (Shape.releasedPressureHistoryToCanonical pressure)

    velocityPeriodic :
      Canonical.UnitPeriodicVelocity S
        (Shape.releasedVectorHistoryToCanonical velocity)

    pressurePeriodic :
      Canonical.UnitPeriodicPressure S
        (Shape.releasedPressureHistoryToCanonical pressure)

    solvesEquation :
      Canonical.SolvesForcedNS S viscosity
        (Shape.releasedVectorHistoryToCanonical velocity)
        (Shape.releasedPressureHistoryToCanonical pressure)
        initial
        (Shape.releasedForcingToCanonical forcing)

    incompressible :
      Canonical.DivergenceFreeHistory S
        (Shape.releasedVectorHistoryToCanonical velocity)

    initialTrace :
      Canonical.AttainsInitialDatum S
        (Shape.releasedVectorHistoryToCanonical velocity)
        initial

open ReleasedGlobalSolutionD public

canonicalSolutionToReleasedD :
  (S : Canonical.CanonicalNSSemantics) →
  (viscosity : BishopReal.ℝ) →
  (initial : Shape.ReleasedInitialFieldShape) →
  (forcing : Shape.ReleasedVectorHistoryShape) →
  Clay.FeffermanPeriodicForcedGlobalSolution
    (Canonical.canonicalPeriodicD S)
    viscosity initial
    (Shape.releasedForcingToCanonical forcing) →
  ReleasedGlobalSolutionD S viscosity initial forcing
canonicalSolutionToReleasedD S viscosity initial forcing solution = record
  { velocity =
      Shape.canonicalVectorHistoryToReleased
        (Clay.velocityD solution)
  ; pressure =
      Shape.canonicalPressureHistoryToReleased
        (Clay.pressureD solution)
  ; velocitySmooth = Clay.velocitySmoothD solution
  ; pressureSmooth = Clay.pressureSmoothD solution
  ; velocityPeriodic = Clay.velocityPeriodicD solution
  ; pressurePeriodic = Clay.pressurePeriodicD solution
  ; solvesEquation = Clay.solvesEquationD solution
  ; incompressible = Clay.incompressibleD solution
  ; initialTrace = Clay.initialTraceD solution
  }

record ReleasedComparatorDWitness
    (S : Canonical.CanonicalNSSemantics)
    (viscosity : BishopReal.ℝ) : Set₁ where
  field
    initial : Shape.ReleasedInitialFieldShape
    forcing : Shape.ReleasedVectorHistoryShape

    initialSmooth :
      Canonical.SmoothSpatialVector S initial
    initialDivergenceFree :
      Canonical.DivergenceFreeSpatial S initial
    initialPeriodic :
      Canonical.UnitPeriodicSpatialVector S initial

    forcingSmooth :
      Canonical.SmoothForcingHistory S
        (Shape.releasedForcingToCanonical forcing)
    forcingPeriodic :
      Canonical.UnitPeriodicForcing S
        (Shape.releasedForcingToCanonical forcing)
    forcingRapidTimeDecay :
      Canonical.RapidTimeDecayAllForcingDerivatives S
        (Shape.releasedForcingToCanonical forcing)

    noReleasedGlobalSolution :
      ReleasedGlobalSolutionD S viscosity initial forcing → ⊥

open ReleasedComparatorDWitness public

releasedComparatorDToCanonicalReconstruction :
  (S : Canonical.CanonicalNSSemantics) →
  (viscosity : BishopReal.ℝ) →
  ReleasedComparatorDWitness S viscosity →
  Reconstruct.ReleasedCanonicalDReconstruction S viscosity
releasedComparatorDToCanonicalReconstruction S viscosity witness = record
  { Reconstruct.initial = ReleasedComparatorDWitness.initial witness
  ; Reconstruct.forcing =
      Shape.releasedForcingToCanonical
        (ReleasedComparatorDWitness.forcing witness)
  ; Reconstruct.initialSmooth =
      ReleasedComparatorDWitness.initialSmooth witness
  ; Reconstruct.initialDivergenceFree =
      ReleasedComparatorDWitness.initialDivergenceFree witness
  ; Reconstruct.initialPeriodic =
      ReleasedComparatorDWitness.initialPeriodic witness
  ; Reconstruct.forcingSmooth =
      ReleasedComparatorDWitness.forcingSmooth witness
  ; Reconstruct.forcingPeriodic =
      ReleasedComparatorDWitness.forcingPeriodic witness
  ; Reconstruct.forcingRapidTimeDecay =
      ReleasedComparatorDWitness.forcingRapidTimeDecay witness
  ; Reconstruct.noGlobalSmoothPeriodicSolution =
      λ solution →
        ReleasedComparatorDWitness.noReleasedGlobalSolution witness
          (canonicalSolutionToReleasedD
            S viscosity
            (ReleasedComparatorDWitness.initial witness)
            (ReleasedComparatorDWitness.forcing witness)
            solution)
  }

releasedComparatorCToLiteralStatement :
  (S : Canonical.CanonicalNSSemantics) →
  ((viscosity : BishopReal.ℝ) →
    Canonical.PositiveReal S viscosity →
    ReleasedComparatorCWitness S viscosity) →
  Clay.FeffermanEuclideanClayStatementC
    (Canonical.canonicalEuclideanC S)
releasedComparatorCToLiteralStatement S theorem viscosity viscosityPositive =
  Reconstruct.compileReleasedCanonicalC S viscosity
    (releasedComparatorCToCanonicalReconstruction
      S viscosity (theorem viscosity viscosityPositive))

releasedComparatorDToLiteralStatement :
  (S : Canonical.CanonicalNSSemantics) →
  ((viscosity : BishopReal.ℝ) →
    Canonical.PositiveReal S viscosity →
    ReleasedComparatorDWitness S viscosity) →
  Clay.FeffermanPeriodicClayStatementD
    (Canonical.canonicalPeriodicD S)
releasedComparatorDToLiteralStatement S theorem viscosity viscosityPositive =
  Reconstruct.compileReleasedCanonicalD S viscosity
    (releasedComparatorDToCanonicalReconstruction
      S viscosity (theorem viscosity viscosityPositive))

spaceTimeTransposeToCanonicalConsumerClosed : Bool
spaceTimeTransposeToCanonicalConsumerClosed = true

releasedNoGlobalConsumerTransportClosed : Bool
releasedNoGlobalConsumerTransportClosed = true

mathlibScalarAndSpaceSameObjectBridgeClosedHere : Bool
mathlibScalarAndSpaceSameObjectBridgeClosedHere = false

releasedLeanProofImportedIntoAgdaHere : Bool
releasedLeanProofImportedIntoAgdaHere = false

clayPromotion : Bool
clayPromotion = false

spaceTimeTransposeToCanonicalConsumerClosedIsTrue :
  spaceTimeTransposeToCanonicalConsumerClosed ≡ true
spaceTimeTransposeToCanonicalConsumerClosedIsTrue = refl

releasedNoGlobalConsumerTransportClosedIsTrue :
  releasedNoGlobalConsumerTransportClosed ≡ true
releasedNoGlobalConsumerTransportClosedIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
