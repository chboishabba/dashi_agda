{-# OPTIONS --allow-unsolved-metas #-}
module DASHI.Physics.Closure.NSTriadKNClayProofSearchRound85 where

------------------------------------------------------------------------
-- PROOF-SEARCH ROOT, NOT AN AUTHORITY/PROMOTION MODULE
--
-- Primary sources:
--
-- Charles L. Fefferman,
-- "Existence and Smoothness of the Navier--Stokes Equation",
-- Clay Mathematics Institute Millennium Prize Problem description (2000).
-- DOI: none assigned to the official problem description.
--
-- Jean Leray,
-- "Sur le mouvement d'un liquide visqueux emplissant l'espace",
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Roger Temam,
-- "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- Xiaoyutao Luo,
-- "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization", Journal of Mathematical Fluid Mechanics 21 (2019), 1.
-- DOI: 10.1007/s00021-019-0411-z.
--
-- PURPOSE
--
-- Work backwards from the literal Fefferman periodic alternative (B) instead
-- of maintaining a prose list of frontier lemmas.  This file deliberately
-- permits unsolved metas so Agda can act as the proof-search worklist.
--
-- IMPORTANT:
--   * holes here are not postulates and are not imported as theorem authority;
--   * theorem-bearing Round85 modules remain hole-free;
--   * this module stays out of production aggregation roots;
--   * every solved producer deletes a hole here until the final term is closed.
--
-- Backward spine:
--
--   Fefferman periodic B
--   <- InRepoClayPathInputs
--   <- UniformGlobalPhysicalSolutionInputs
--   <- GlobalPhysicalSolutionPrimitiveInputs for each datum
--   <- maximal time dichotomy + (finite maximal time -> bottom)
--   <- Round85 critical barrier / occupation contradiction.
--
-- The key correction compared with a passive cutset inventory is that the
-- final theorem term is written now.  The compiler holes live inside the
-- actual records consumed by that theorem.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSTriadKNPeriodicNavierStokesSubmissionTheoremExact as Legacy
import DASHI.Physics.Closure.NSTriadKNFeffermanPeriodicClayStatementExact as Clay
import DASHI.Physics.Closure.NSTriadKNLuoLegacySubmissionToFeffermanAdapterExact as Adapter
import DASHI.Physics.Closure.NSTriadKNLuoClayEndToEndCompositionRound23Exact as EndToEnd
import DASHI.Physics.Closure.NSTriadKNLuoGlobalPhysicalSolutionReductionExact as Global

------------------------------------------------------------------------
-- Terminal infrastructure orthogonal to the current compact-transfer frontier.
------------------------------------------------------------------------

record TerminalClayInfrastructure
    (legacy : Legacy.PeriodicNavierStokesSubmissionCarrier)
    (clay : Clay.FeffermanPeriodicClayCarrier) : Set₁ where
  field
    legacyToLiteralAdapter :
      Adapter.LegacySubmissionToFeffermanAdapter legacy clay

    MeanVelocity : Set
    DatumMeanZero : Clay.SmoothPeriodicDatum clay → Set

    spatialMean : Clay.SmoothPeriodicDatum clay → MeanVelocity
    centeredDatum :
      Clay.SmoothPeriodicDatum clay → Clay.SmoothPeriodicDatum clay

    centeredDatumSmooth :
      (initial : Clay.SmoothPeriodicDatum clay) →
      Clay.DatumSmoothOnThreeTorus clay initial →
      Clay.DatumSmoothOnThreeTorus clay (centeredDatum initial)

    centeredDatumDivergenceFree :
      (initial : Clay.SmoothPeriodicDatum clay) →
      Clay.DatumDivergenceFree clay initial →
      Clay.DatumDivergenceFree clay (centeredDatum initial)

    centeredDatumPeriodic :
      (initial : Clay.SmoothPeriodicDatum clay) →
      Clay.DatumUnitPeriodicInThreeCoordinates clay initial →
      Clay.DatumUnitPeriodicInThreeCoordinates clay (centeredDatum initial)

    centeredDatumHasZeroMean :
      (initial : Clay.SmoothPeriodicDatum clay) →
      DatumMeanZero (centeredDatum initial)

    literalDivergenceFreeToLegacy :
      (initial : Clay.SmoothPeriodicDatum clay) →
      Clay.DatumDivergenceFree clay initial →
      Legacy.DivergenceFreeDatum legacy
        (Adapter.encodeDatum legacyToLiteralAdapter initial)

    literalMeanZeroToLegacy :
      (initial : Clay.SmoothPeriodicDatum clay) →
      DatumMeanZero initial →
      Legacy.MeanZeroDatum legacy
        (Adapter.encodeDatum legacyToLiteralAdapter initial)

    restoreGalileanSolution :
      (viscosity : Clay.Viscosity clay) →
      (initial : Clay.SmoothPeriodicDatum clay) →
      Clay.FeffermanPeriodicGlobalSolutionWitness clay viscosity
        (centeredDatum initial) →
      Clay.FeffermanPeriodicGlobalSolutionWitness clay viscosity initial

open TerminalClayInfrastructure public

------------------------------------------------------------------------
-- Standard post-barrier/maximal-solution infrastructure.
--
-- The hard Round85 theorem is NOT hidden in this record.  In particular the
-- contradiction of a finite maximal time is supplied separately below.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Search holes.
--
-- `standardGlobalContinuationSearch` is deliberately conventional PDE
-- infrastructure.  `finiteMaximalTimeContradictionSearch` is the hard theorem:
-- this is where the Round85 compact-transfer/occupation/critical-ratio route
-- must eventually terminate.
------------------------------------------------------------------------

standardGlobalContinuationSearch :
  (legacy : Legacy.PeriodicNavierStokesSubmissionCarrier) →
  (initial : Legacy.SmoothPeriodicDatum legacy) →
  Legacy.DivergenceFreeDatum legacy initial →
  Legacy.MeanZeroDatum legacy initial →
  StandardGlobalContinuationInfrastructure legacy initial
standardGlobalContinuationSearch legacy initial divergenceFree meanZero = {!!}

finiteMaximalTimeContradictionSearch :
  ∀ {legacy initial}
    (standard : StandardGlobalContinuationInfrastructure legacy initial) →
  FiniteMaximalTime standard → ⊥
finiteMaximalTimeContradictionSearch standard finite = {!!}

primitivePhysicalSolutionSearch :
  (legacy : Legacy.PeriodicNavierStokesSubmissionCarrier) →
  (initial : Legacy.SmoothPeriodicDatum legacy) →
  Legacy.DivergenceFreeDatum legacy initial →
  Legacy.MeanZeroDatum legacy initial →
  Global.GlobalPhysicalSolutionPrimitiveInputs legacy initial
primitivePhysicalSolutionSearch legacy initial divergenceFree meanZero =
  let
    standard =
      standardGlobalContinuationSearch legacy initial divergenceFree meanZero
  in
  primitivePhysicalSolutionFromFiniteContradiction
    standard
    (finiteMaximalTimeContradictionSearch standard)

uniformPhysicalConstructionSearch :
  (legacy : Legacy.PeriodicNavierStokesSubmissionCarrier) →
  Global.UniformGlobalPhysicalSolutionInputs legacy
uniformPhysicalConstructionSearch legacy = record
  { Global.UniformGlobalPhysicalSolutionInputs.primitiveInputsForDatum =
      primitivePhysicalSolutionSearch legacy
  }

------------------------------------------------------------------------
-- Existing end-to-end path and literal final theorem.
------------------------------------------------------------------------

inRepoClayPathSearch :
  ∀ {legacy clay} →
  TerminalClayInfrastructure legacy clay →
  EndToEnd.InRepoClayPathInputs legacy clay
inRepoClayPathSearch {legacy} terminal = record
  { EndToEnd.InRepoClayPathInputs.legacyUniformPhysicalConstruction =
      uniformPhysicalConstructionSearch legacy
  ; EndToEnd.InRepoClayPathInputs.legacyToLiteralAdapter =
      legacyToLiteralAdapter terminal
  ; EndToEnd.InRepoClayPathInputs.MeanVelocity = MeanVelocity terminal
  ; EndToEnd.InRepoClayPathInputs.DatumMeanZero = DatumMeanZero terminal
  ; EndToEnd.InRepoClayPathInputs.spatialMean = spatialMean terminal
  ; EndToEnd.InRepoClayPathInputs.centeredDatum = centeredDatum terminal
  ; EndToEnd.InRepoClayPathInputs.centeredDatumSmooth = centeredDatumSmooth terminal
  ; EndToEnd.InRepoClayPathInputs.centeredDatumDivergenceFree =
      centeredDatumDivergenceFree terminal
  ; EndToEnd.InRepoClayPathInputs.centeredDatumPeriodic = centeredDatumPeriodic terminal
  ; EndToEnd.InRepoClayPathInputs.centeredDatumHasZeroMean =
      centeredDatumHasZeroMean terminal
  ; EndToEnd.InRepoClayPathInputs.literalDivergenceFreeToLegacy =
      literalDivergenceFreeToLegacy terminal
  ; EndToEnd.InRepoClayPathInputs.literalMeanZeroToLegacy =
      literalMeanZeroToLegacy terminal
  ; EndToEnd.InRepoClayPathInputs.restoreGalileanSolution =
      restoreGalileanSolution terminal
  }

periodic3DNavierStokesClayProofSearch :
  ∀ {legacy clay} →
  TerminalClayInfrastructure legacy clay →
  Clay.FeffermanPeriodicClayStatementB clay
periodic3DNavierStokesClayProofSearch terminal =
  EndToEnd.inRepoPathClosesLiteralFeffermanPeriodicB
    (inRepoClayPathSearch terminal)
