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
--   * this module should stay out of production aggregation roots;
--   * every solved producer deletes a hole here until the final term is closed.
--
-- The first expansion is already the repository's genuine end-to-end theorem:
--
--   InRepoClayPathInputs
--      -> FeffermanPeriodicClayStatementB.
--
-- We then expand the only hard field, `legacyUniformPhysicalConstruction`,
-- into `UniformGlobalPhysicalSolutionInputs`, and then into the actual
-- `GlobalPhysicalSolutionPrimitiveInputs` record for each initial datum.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)

import DASHI.Physics.Closure.NSTriadKNPeriodicNavierStokesSubmissionTheoremExact as Legacy
import DASHI.Physics.Closure.NSTriadKNFeffermanPeriodicClayStatementExact as Clay
import DASHI.Physics.Closure.NSTriadKNLuoLegacySubmissionToFeffermanAdapterExact as Adapter
import DASHI.Physics.Closure.NSTriadKNLuoClayEndToEndCompositionRound23Exact as EndToEnd
import DASHI.Physics.Closure.NSTriadKNLuoGlobalPhysicalSolutionReductionExact as Global

------------------------------------------------------------------------
-- Terminal infrastructure that is orthogonal to the current compact-transfer
-- analytic frontier.  This merely factors the already-existing end-to-end
-- record so the proof-search hole is concentrated in the global physical
-- construction rather than duplicated mean/Galilean/adapter bookkeeping.
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
-- Expand the hard end-to-end field instead of accepting it as one black box.
------------------------------------------------------------------------

primitivePhysicalSolutionSearch :
  (legacy : Legacy.PeriodicNavierStokesSubmissionCarrier) →
  (initial : Legacy.SmoothPeriodicDatum legacy) →
  Legacy.DivergenceFreeDatum legacy initial →
  Legacy.MeanZeroDatum legacy initial →
  Global.GlobalPhysicalSolutionPrimitiveInputs legacy initial
primitivePhysicalSolutionSearch legacy initial divergenceFree meanZero =
  record
    { Global.GlobalPhysicalSolutionPrimitiveInputs.InfiniteMaximalTime = {!!}
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.infiniteMaximalTime = {!!}
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.velocityFromInfiniteMaximalTime = {!!}
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.velocitySmoothFromSobolevAndParabolicBootstrap = {!!}
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.pressureFromProjectedVelocity = {!!}
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.pressureSmoothFromVelocity = {!!}
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.velocityPressureSolveOriginalEquation = {!!}
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.initialTraceAtZero = {!!}
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.strongSolutionUniquenessAndPressureNormalization = {!!}
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.globalEnergyEquality = {!!}
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.divergenceFreePreserved = {!!}
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.meanZeroPreserved = {!!}
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.finiteEnergyAtEveryTime = {!!}
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.HsAboveFiveHalvesEmbedsIntoC1 = {!!}
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.hsAboveFiveHalvesEmbedsIntoC1 = {!!}
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.ParabolicSmoothingAfterPositiveTime = {!!}
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.parabolicSmoothingAfterPositiveTime = {!!}
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.HigherSobolevEnergyInduction = {!!}
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.higherSobolevEnergyInduction = {!!}
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.PressurePoissonEquation = {!!}
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.pressurePoissonEquation = {!!}
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.PressureMeanZeroNormalization = {!!}
    ; Global.GlobalPhysicalSolutionPrimitiveInputs.pressureMeanZeroNormalization = {!!}
    }

uniformPhysicalConstructionSearch :
  (legacy : Legacy.PeriodicNavierStokesSubmissionCarrier) →
  Global.UniformGlobalPhysicalSolutionInputs legacy
uniformPhysicalConstructionSearch legacy = record
  { Global.UniformGlobalPhysicalSolutionInputs.primitiveInputsForDatum =
      primitivePhysicalSolutionSearch legacy
  }

------------------------------------------------------------------------
-- Actual end-to-end path term.  Once the primitive record above is closed,
-- this declaration is already the full physical path consumed by the existing
-- Fefferman theorem composition.
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

------------------------------------------------------------------------
-- FINAL GOAL.
--
-- This is not a Bool/status receipt.  Its codomain is exactly Fefferman's
-- periodic alternative (B) theorem type already represented in the repo.
------------------------------------------------------------------------

periodic3DNavierStokesClayProofSearch :
  ∀ {legacy clay} →
  TerminalClayInfrastructure legacy clay →
  Clay.FeffermanPeriodicClayStatementB clay
periodic3DNavierStokesClayProofSearch terminal =
  EndToEnd.inRepoPathClosesLiteralFeffermanPeriodicB
    (inRepoClayPathSearch terminal)
