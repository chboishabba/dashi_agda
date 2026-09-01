module DASHI.Physics.Closure.NSTriadKNStandardGlobalContinuationCompilerRound366Exact where

------------------------------------------------------------------------
-- ROUND366 / BIDI: HOLE-FREE EXTRACTION OF THE ROUND85 TERMINAL COMPILER
--
-- `NSTriadKNClayProofSearchRound85` already contains the correct theorem-level
-- factorization from a finite-maximal-time contradiction to the old global
-- physical primitive record, but that proof-search root intentionally enables
-- unsolved metas and must not become production authority.
--
-- This module extracts only the fully defined, hole-free compiler.  The hard
-- analytic search functions from Round85 are NOT imported or copied.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSTriadKNPeriodicNavierStokesSubmissionTheoremExact as Legacy
import DASHI.Physics.Closure.NSTriadKNLuoGlobalPhysicalSolutionReductionExact as Global

record StandardGlobalContinuationInfrastructure
    (legacy : Legacy.PeriodicNavierStokesSubmissionCarrier)
    (initial : Legacy.SmoothPeriodicDatum legacy) : Set₁ where
  field
    FiniteMaximalTime : Set
    InfiniteMaximalTime : Set

    maximalTimeDichotomy :
      Legacy.MaximalTimeAlternative FiniteMaximalTime InfiniteMaximalTime

    velocityFromInfiniteMaximalTime :
      InfiniteMaximalTime → Legacy.GlobalVelocity legacy

    velocitySmoothFromSobolevAndParabolicBootstrap :
      (infinite : InfiniteMaximalTime) →
      Legacy.GlobalSmoothVelocity legacy
        (velocityFromInfiniteMaximalTime infinite)

    pressureFromProjectedVelocity :
      (infinite : InfiniteMaximalTime) → Legacy.GlobalPressure legacy

    pressureSmoothFromVelocity :
      (infinite : InfiniteMaximalTime) →
      Legacy.GlobalSmoothPressure legacy
        (pressureFromProjectedVelocity infinite)

    velocityPressureSolveOriginalEquation :
      (infinite : InfiniteMaximalTime) →
      Legacy.SolvesPeriodicNavierStokes legacy
        (velocityFromInfiniteMaximalTime infinite)
        (pressureFromProjectedVelocity infinite)
        initial

    initialTraceAtZero :
      (infinite : InfiniteMaximalTime) →
      Legacy.AttainsInitialDatum legacy
        (velocityFromInfiniteMaximalTime infinite)
        initial

    strongSolutionUniquenessAndPressureNormalization :
      (infinite : InfiniteMaximalTime) →
      Legacy.VelocityPressurePairUnique legacy
        (velocityFromInfiniteMaximalTime infinite)
        (pressureFromProjectedVelocity infinite)
        initial

    globalEnergyEquality :
      (infinite : InfiniteMaximalTime) →
      Legacy.GlobalEnergyEquality legacy
        (velocityFromInfiniteMaximalTime infinite)
        initial

    divergenceFreePreserved :
      (infinite : InfiniteMaximalTime) →
      Legacy.DivergenceFreePreserved legacy
        (velocityFromInfiniteMaximalTime infinite)

    meanZeroPreserved :
      (infinite : InfiniteMaximalTime) →
      Legacy.MeanZeroPreserved legacy
        (velocityFromInfiniteMaximalTime infinite)

    finiteEnergyAtEveryTime :
      (infinite : InfiniteMaximalTime) →
      Legacy.FiniteEnergyAtEveryTime legacy
        (velocityFromInfiniteMaximalTime infinite)

    HsAboveFiveHalvesEmbedsIntoC1 : Set
    hsAboveFiveHalvesEmbedsIntoC1 : HsAboveFiveHalvesEmbedsIntoC1

    ParabolicSmoothingAfterPositiveTime : Set
    parabolicSmoothingAfterPositiveTime : ParabolicSmoothingAfterPositiveTime

    HigherSobolevEnergyInduction : Set
    higherSobolevEnergyInduction : HigherSobolevEnergyInduction

    PressurePoissonEquation : Set
    pressurePoissonEquation : PressurePoissonEquation

    PressureMeanZeroNormalization : Set
    pressureMeanZeroNormalization : PressureMeanZeroNormalization

open StandardGlobalContinuationInfrastructure public

maximalTimeInputsFromFiniteContradiction :
  ∀ {legacy initial}
    (standard : StandardGlobalContinuationInfrastructure legacy initial) →
  (FiniteMaximalTime standard → ⊥) →
  Legacy.MaximalTimeDichotomyInputs
maximalTimeInputsFromFiniteContradiction standard contradiction = record
  { Legacy.MaximalTimeDichotomyInputs.FiniteMaximalTime =
      FiniteMaximalTime standard
  ; Legacy.MaximalTimeDichotomyInputs.InfiniteMaximalTime =
      InfiniteMaximalTime standard
  ; Legacy.MaximalTimeDichotomyInputs.maximalTimeDichotomy =
      maximalTimeDichotomy standard
  ; Legacy.MaximalTimeDichotomyInputs.finiteMaximalTimeContradiction =
      contradiction
  }

primitivePhysicalSolutionFromFiniteContradiction :
  ∀ {legacy initial}
    (standard : StandardGlobalContinuationInfrastructure legacy initial) →
  (finiteContradiction : FiniteMaximalTime standard → ⊥) →
  Global.GlobalPhysicalSolutionPrimitiveInputs legacy initial
primitivePhysicalSolutionFromFiniteContradiction
    {legacy} {initial} standard finiteContradiction =
  let
    maximalInputs =
      maximalTimeInputsFromFiniteContradiction standard finiteContradiction
    infinite = Legacy.maximalTimeMustBeInfinite maximalInputs
  in
  record
    { Global.GlobalPhysicalSolutionPrimitiveInputs.InfiniteMaximalTime =
        InfiniteMaximalTime standard
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.infiniteMaximalTime = infinite
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.velocityFromInfiniteMaximalTime =
        velocityFromInfiniteMaximalTime standard
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.velocitySmoothFromSobolevAndParabolicBootstrap =
        velocitySmoothFromSobolevAndParabolicBootstrap standard
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.pressureFromProjectedVelocity =
        pressureFromProjectedVelocity standard
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.pressureSmoothFromVelocity =
        pressureSmoothFromVelocity standard
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.velocityPressureSolveOriginalEquation =
        velocityPressureSolveOriginalEquation standard
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.initialTraceAtZero =
        initialTraceAtZero standard
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.strongSolutionUniquenessAndPressureNormalization =
        strongSolutionUniquenessAndPressureNormalization standard
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.globalEnergyEquality =
        globalEnergyEquality standard
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.divergenceFreePreserved =
        divergenceFreePreserved standard
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.meanZeroPreserved =
        meanZeroPreserved standard
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.finiteEnergyAtEveryTime =
        finiteEnergyAtEveryTime standard
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.HsAboveFiveHalvesEmbedsIntoC1 =
        HsAboveFiveHalvesEmbedsIntoC1 standard
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.hsAboveFiveHalvesEmbedsIntoC1 =
        hsAboveFiveHalvesEmbedsIntoC1 standard
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.ParabolicSmoothingAfterPositiveTime =
        ParabolicSmoothingAfterPositiveTime standard
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.parabolicSmoothingAfterPositiveTime =
        parabolicSmoothingAfterPositiveTime standard
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.HigherSobolevEnergyInduction =
        HigherSobolevEnergyInduction standard
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.higherSobolevEnergyInduction =
        higherSobolevEnergyInduction standard
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.PressurePoissonEquation =
        PressurePoissonEquation standard
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.pressurePoissonEquation =
        pressurePoissonEquation standard
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.PressureMeanZeroNormalization =
        PressureMeanZeroNormalization standard
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.pressureMeanZeroNormalization =
        pressureMeanZeroNormalization standard
    }

round366UnsafeProofSearchRootImported : Bool
round366UnsafeProofSearchRootImported = false

round366MaximalTimeDichotomyCompilerExtractedHoleFree : Bool
round366MaximalTimeDichotomyCompilerExtractedHoleFree = true

round366PostInfiniteTimeSmoothPressureCompilerReused : Bool
round366PostInfiniteTimeSmoothPressureCompilerReused = true

round366HardFiniteMaximalTimeContradictionProducedHere : Bool
round366HardFiniteMaximalTimeContradictionProducedHere = false

round366MaximalTimeDichotomyCompilerExtractedHoleFreeIsTrue :
  round366MaximalTimeDichotomyCompilerExtractedHoleFree ≡ true
round366MaximalTimeDichotomyCompilerExtractedHoleFreeIsTrue = refl

round366UnsafeProofSearchRootImportedIsFalse :
  round366UnsafeProofSearchRootImported ≡ false
round366UnsafeProofSearchRootImportedIsFalse = refl
