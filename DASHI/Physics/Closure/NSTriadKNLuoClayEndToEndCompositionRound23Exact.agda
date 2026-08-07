module DASHI.Physics.Closure.NSTriadKNLuoClayEndToEndCompositionRound23Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Charles L. Fefferman.
-- Title: "Existence and Smoothness of the Navier--Stokes Equation".
-- Clay Mathematics Institute Millennium Prize Problem description, 2000.
-- DOI: not assigned to the official problem description.
--
-- Author: Tosio Kato.
-- Title: "Strong Lp-Solutions of the Navier-Stokes Equation in Rm, with
-- Applications to Weak Solutions".
-- DOI: 10.1007/BF01174182.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- PURPOSE
--
-- Exhibit the exact end-to-end composition already available in the repository
-- once the remaining physical producers are inhabited:
--
--   uniform global physical construction for centered data
--     -> legacy global solution witness
--     -> literal Fefferman witness
--     -> Galilean restoration for arbitrary periodic data
--     -> Fefferman periodic alternative (B).
--
-- This is the unification step.  It proves that no additional terminal receipt
-- or theorem wrapper is needed after the analytic frontier closes.  It does not
-- manufacture the uniform physical construction, the continuum spatial mean,
-- the Galilean PDE invariance proof, or the carrier adapter.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNPeriodicNavierStokesSubmissionTheoremExact as Legacy
import DASHI.Physics.Closure.NSTriadKNLuoGlobalPhysicalSolutionReductionExact as Global
import DASHI.Physics.Closure.NSTriadKNFeffermanPeriodicClayStatementExact as Clay
import DASHI.Physics.Closure.NSTriadKNLuoLegacySubmissionToFeffermanAdapterExact as Adapter
import DASHI.Physics.Closure.NSTriadKNLuoPeriodicMeanZeroGalileanReductionExact as Galilean

record InRepoClayPathInputs
    (legacy : Legacy.PeriodicNavierStokesSubmissionCarrier)
    (clay : Clay.FeffermanPeriodicClayCarrier) : Set₁ where
  field
    legacyUniformPhysicalConstruction :
      Global.UniformGlobalPhysicalSolutionInputs legacy

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

open InRepoClayPathInputs public

centeredLiteralSolutionFromLegacyPhysicalConstruction :
  ∀ {legacy clay}
    (inputs : InRepoClayPathInputs legacy clay)
    (viscosity : Clay.Viscosity clay)
    (initial : Clay.SmoothPeriodicDatum clay) →
  Clay.DatumSmoothOnThreeTorus clay initial →
  Clay.DatumDivergenceFree clay initial →
  Clay.DatumUnitPeriodicInThreeCoordinates clay initial →
  DatumMeanZero inputs initial →
  Clay.FeffermanPeriodicGlobalSolutionWitness clay viscosity initial
centeredLiteralSolutionFromLegacyPhysicalConstruction
  inputs viscosity initial initialSmooth initialDivergence initialPeriodic initialMeanZero =
  Adapter.legacyWitnessGivesLiteralFeffermanWitness
    (legacyToLiteralAdapter inputs)
    viscosity
    initial
    (Global.globalPhysicalSolutionWitness
      (Global.primitiveInputsForDatum
        (legacyUniformPhysicalConstruction inputs)
        (Adapter.encodeDatum (legacyToLiteralAdapter inputs) initial)
        (literalDivergenceFreeToLegacy inputs initial initialDivergence)
        (literalMeanZeroToLegacy inputs initial initialMeanZero)))

meanZeroGalileanInputsFromInRepoPath :
  ∀ {legacy clay} →
  InRepoClayPathInputs legacy clay →
  Galilean.PeriodicMeanZeroGalileanInputs clay
meanZeroGalileanInputsFromInRepoPath inputs = record
  { MeanVelocity = MeanVelocity inputs
  ; DatumMeanZero = DatumMeanZero inputs
  ; spatialMean = spatialMean inputs
  ; centeredDatum = centeredDatum inputs
  ; centeredDatumSmooth = centeredDatumSmooth inputs
  ; centeredDatumDivergenceFree = centeredDatumDivergenceFree inputs
  ; centeredDatumPeriodic = centeredDatumPeriodic inputs
  ; centeredDatumHasZeroMean = centeredDatumHasZeroMean inputs
  ; centeredGlobalSolver =
      centeredLiteralSolutionFromLegacyPhysicalConstruction inputs
  ; restoreGalileanSolution = restoreGalileanSolution inputs
  }

inRepoPathClosesLiteralFeffermanPeriodicB :
  ∀ {legacy clay} →
  InRepoClayPathInputs legacy clay →
  Clay.FeffermanPeriodicClayStatementB clay
inRepoPathClosesLiteralFeffermanPeriodicB {clay = clay} inputs =
  Galilean.meanZeroSolverAndGalileanRestorationGiveClayB
    clay
    (meanZeroGalileanInputsFromInRepoPath inputs)

record ClayEndToEndAuthorityBoundary : Set where
  constructor clayEndToEndAuthorityBoundary
  field
    literalFeffermanBTargetConnected : Bool
    existingGlobalPhysicalReducerReused : Bool
    legacyExtraPostconditionsSafelyForgotten : Bool
    meanZeroRestrictionRemovedByTypedReduction : Bool
    terminalCompositionCompleteAfterProducers : Bool
    uniformPhysicalConstructionInhabited : Bool
    continuumMeanAndGalileanInvarianceInhabited : Bool
    physicalCarrierAdapterInhabited : Bool
    unconditionalClayTheoremPromoted : Bool

open ClayEndToEndAuthorityBoundary public

canonicalClayEndToEndAuthorityBoundary : ClayEndToEndAuthorityBoundary
canonicalClayEndToEndAuthorityBoundary =
  clayEndToEndAuthorityBoundary
    true true true true true false false false false

endToEndClayCompositionConstructed : Bool
endToEndClayCompositionConstructed = true

endToEndClayCompositionConstructedIsTrue :
  endToEndClayCompositionConstructed ≡ true
endToEndClayCompositionConstructedIsTrue = refl

unconditionalClayTheoremStillFalse :
  unconditionalClayTheoremPromoted canonicalClayEndToEndAuthorityBoundary
  ≡ false
unconditionalClayTheoremStillFalse = refl
