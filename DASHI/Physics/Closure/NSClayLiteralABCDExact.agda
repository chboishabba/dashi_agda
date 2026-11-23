module DASHI.Physics.Closure.NSClayLiteralABCDExact where

------------------------------------------------------------------------
-- LITERAL FEFFERMAN / CLAY NAVIER--STOKES A/B/C/D CAPSTONE
--
-- This module removes the last abstraction leak in the four-lane coordinator:
-- the four "payments" are the literal mathematical propositions themselves,
-- not empty tokens, Boolean status coordinates, provenance receipts, or
-- conditional compiler labels.
--
-- Source authority:
--   Charles L. Fefferman,
--   "Existence and Smoothness of the Navier--Stokes Equation",
--   Clay Mathematics Institute Millennium Prize Problem description (2000).
--
-- Existing in-repo owners reused rather than duplicated:
--   * B: NSTriadKNFeffermanPeriodicClayStatementExact
--   * C/D source-coordinate audit:
--       NSTriadKNClayForcedBreakdownFormulationRound523Exact
--
-- IMPORTANT:
--   Constructing these theorem TYPES does not inhabit them.  A checked proof
--   of any one of A/B/C/D is an AnyOneClayResolution; a checked proof of all
--   four is a LiteralFourAlternativeCompletion.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSTriadKNFeffermanPeriodicClayStatementExact as B
import DASHI.Physics.Closure.NSTriadKNClayForcedBreakdownFormulationRound523Exact as CD

------------------------------------------------------------------------
-- A. Unforced whole-space R^3 global existence and smoothness.
------------------------------------------------------------------------

record FeffermanEuclideanClayCarrier : Set₁ where
  field
    Viscosity : Set
    PositiveViscosity : Viscosity → Set

    SmoothEuclideanDatum : Set
    DatumSmoothOnR3 : SmoothEuclideanDatum → Set
    DatumDivergenceFree : SmoothEuclideanDatum → Set
    DatumRapidSpatialDecay : SmoothEuclideanDatum → Set

    GlobalVelocity : Set
    GlobalPressure : Set

    VelocitySmoothOnR3TimesNonnegativeTime : GlobalVelocity → Set
    PressureSmoothOnR3TimesNonnegativeTime : GlobalPressure → Set

    SolvesThreeDimensionalMomentumEquationWithZeroForce :
      Viscosity →
      GlobalVelocity →
      GlobalPressure →
      SmoothEuclideanDatum →
      Set

    IncompressibleAtEveryNonnegativeTime : GlobalVelocity → Set

    AttainsInitialDatumAtTimeZero :
      GlobalVelocity → SmoothEuclideanDatum → Set

    BoundedKineticEnergyAtEveryNonnegativeTime : GlobalVelocity → Set

open FeffermanEuclideanClayCarrier public

record FeffermanEuclideanGlobalSolutionWitness
    (carrier : FeffermanEuclideanClayCarrier)
    (viscosity : Viscosity carrier)
    (initial : SmoothEuclideanDatum carrier) : Set₁ where
  field
    velocity : GlobalVelocity carrier
    pressure : GlobalPressure carrier

    velocitySmooth :
      VelocitySmoothOnR3TimesNonnegativeTime carrier velocity
    pressureSmooth :
      PressureSmoothOnR3TimesNonnegativeTime carrier pressure

    solvesMomentumEquation :
      SolvesThreeDimensionalMomentumEquationWithZeroForce carrier
        viscosity velocity pressure initial

    incompressible :
      IncompressibleAtEveryNonnegativeTime carrier velocity

    initialTrace :
      AttainsInitialDatumAtTimeZero carrier velocity initial

    boundedEnergy :
      BoundedKineticEnergyAtEveryNonnegativeTime carrier velocity

open FeffermanEuclideanGlobalSolutionWitness public

FeffermanEuclideanClayStatementA :
  FeffermanEuclideanClayCarrier → Set₁
FeffermanEuclideanClayStatementA carrier =
  (viscosity : Viscosity carrier) →
  PositiveViscosity carrier viscosity →
  (initial : SmoothEuclideanDatum carrier) →
  DatumSmoothOnR3 carrier initial →
  DatumDivergenceFree carrier initial →
  DatumRapidSpatialDecay carrier initial →
  FeffermanEuclideanGlobalSolutionWitness carrier viscosity initial

------------------------------------------------------------------------
-- B. Unforced periodic T^3 global existence and smoothness.
--
-- Do not restate the periodic theorem: the existing literal Fefferman owner is
-- canonical and already records the pressure-periodicity erratum and the
-- absence of extra mean-zero / uniqueness / energy hypotheses.
------------------------------------------------------------------------

FeffermanPeriodicClayCarrier : Set₁
FeffermanPeriodicClayCarrier = B.FeffermanPeriodicClayCarrier

FeffermanPeriodicClayStatementB :
  FeffermanPeriodicClayCarrier → Set₁
FeffermanPeriodicClayStatementB = B.FeffermanPeriodicClayStatementB

------------------------------------------------------------------------
-- C. Smooth forced whole-space R^3 breakdown.
------------------------------------------------------------------------

record FeffermanEuclideanForcedBreakdownCarrier : Set₁ where
  field
    ViscosityC : Set
    PositiveViscosityC : ViscosityC → Set

    InitialDatumC : Set
    DatumSmoothC : InitialDatumC → Set
    DatumDivergenceFreeC : InitialDatumC → Set
    DatumRapidSpatialDecayC : InitialDatumC → Set

    ForcingC : Set
    ForcingSmoothC : ForcingC → Set
    ForcingRapidSpaceTimeDecayC : ForcingC → Set

    GlobalVelocityC : Set
    GlobalPressureC : Set

    VelocitySmoothPredicateC : GlobalVelocityC → Set
    PressureSmoothPredicateC : GlobalPressureC → Set

    SolvesForcedNavierStokesC :
      ViscosityC →
      GlobalVelocityC →
      GlobalPressureC →
      InitialDatumC →
      ForcingC →
      Set

    IncompressiblePredicateC : GlobalVelocityC → Set
    AttainsInitialDatumPredicateC : GlobalVelocityC → InitialDatumC → Set
    BoundedEnergyPredicateC : GlobalVelocityC → Set

open FeffermanEuclideanForcedBreakdownCarrier public

record FeffermanEuclideanForcedGlobalSolution
    (carrier : FeffermanEuclideanForcedBreakdownCarrier)
    (viscosity : ViscosityC carrier)
    (initial : InitialDatumC carrier)
    (forcing : ForcingC carrier) : Set₁ where
  field
    velocityC : GlobalVelocityC carrier
    pressureC : GlobalPressureC carrier
    velocitySmoothC : VelocitySmoothPredicateC carrier velocityC
    pressureSmoothC : PressureSmoothPredicateC carrier pressureC
    solvesEquationC :
      SolvesForcedNavierStokesC carrier
        viscosity velocityC pressureC initial forcing
    incompressibleC : IncompressiblePredicateC carrier velocityC
    initialTraceC : AttainsInitialDatumPredicateC carrier velocityC initial
    boundedEnergyC : BoundedEnergyPredicateC carrier velocityC

open FeffermanEuclideanForcedGlobalSolution public

record FeffermanEuclideanForcedBreakdownWitness
    (carrier : FeffermanEuclideanForcedBreakdownCarrier)
    (viscosity : ViscosityC carrier) : Set₁ where
  field
    initialC : InitialDatumC carrier
    forcingC : ForcingC carrier

    initialSmoothC : DatumSmoothC carrier initialC
    initialDivergenceFreeC : DatumDivergenceFreeC carrier initialC
    initialRapidDecayC : DatumRapidSpatialDecayC carrier initialC

    forcingSmoothC : ForcingSmoothC carrier forcingC
    forcingRapidDecayC : ForcingRapidSpaceTimeDecayC carrier forcingC

    noGlobalBoundedEnergySmoothSolutionC :
      FeffermanEuclideanForcedGlobalSolution
        carrier viscosity initialC forcingC → ⊥

open FeffermanEuclideanForcedBreakdownWitness public

FeffermanEuclideanClayStatementC :
  FeffermanEuclideanForcedBreakdownCarrier → Set₁
FeffermanEuclideanClayStatementC carrier =
  (viscosity : ViscosityC carrier) →
  PositiveViscosityC carrier viscosity →
  FeffermanEuclideanForcedBreakdownWitness carrier viscosity

------------------------------------------------------------------------
-- D. Smooth forced periodic T^3 breakdown.
------------------------------------------------------------------------

record FeffermanPeriodicForcedBreakdownCarrier : Set₁ where
  field
    ViscosityD : Set
    PositiveViscosityD : ViscosityD → Set

    InitialDatumD : Set
    DatumSmoothD : InitialDatumD → Set
    DatumDivergenceFreeD : InitialDatumD → Set
    DatumUnitPeriodicD : InitialDatumD → Set

    ForcingD : Set
    ForcingSmoothD : ForcingD → Set
    ForcingUnitPeriodicD : ForcingD → Set
    ForcingRapidTimeDecayOfAllDerivativesD : ForcingD → Set

    GlobalVelocityD : Set
    GlobalPressureD : Set

    VelocitySmoothPredicateD : GlobalVelocityD → Set
    PressureSmoothPredicateD : GlobalPressureD → Set
    VelocityUnitPeriodicPredicateD : GlobalVelocityD → Set
    PressureUnitPeriodicPredicateD : GlobalPressureD → Set

    SolvesForcedNavierStokesD :
      ViscosityD →
      GlobalVelocityD →
      GlobalPressureD →
      InitialDatumD →
      ForcingD →
      Set

    IncompressiblePredicateD : GlobalVelocityD → Set
    AttainsInitialDatumPredicateD : GlobalVelocityD → InitialDatumD → Set

open FeffermanPeriodicForcedBreakdownCarrier public

record FeffermanPeriodicForcedGlobalSolution
    (carrier : FeffermanPeriodicForcedBreakdownCarrier)
    (viscosity : ViscosityD carrier)
    (initial : InitialDatumD carrier)
    (forcing : ForcingD carrier) : Set₁ where
  field
    velocityD : GlobalVelocityD carrier
    pressureD : GlobalPressureD carrier
    velocitySmoothD : VelocitySmoothPredicateD carrier velocityD
    pressureSmoothD : PressureSmoothPredicateD carrier pressureD
    velocityPeriodicD : VelocityUnitPeriodicPredicateD carrier velocityD
    pressurePeriodicD : PressureUnitPeriodicPredicateD carrier pressureD
    solvesEquationD :
      SolvesForcedNavierStokesD carrier
        viscosity velocityD pressureD initial forcing
    incompressibleD : IncompressiblePredicateD carrier velocityD
    initialTraceD : AttainsInitialDatumPredicateD carrier velocityD initial

open FeffermanPeriodicForcedGlobalSolution public

record FeffermanPeriodicForcedBreakdownWitness
    (carrier : FeffermanPeriodicForcedBreakdownCarrier)
    (viscosity : ViscosityD carrier) : Set₁ where
  field
    initialD : InitialDatumD carrier
    forcingD : ForcingD carrier

    initialSmoothD : DatumSmoothD carrier initialD
    initialDivergenceFreeD : DatumDivergenceFreeD carrier initialD
    initialPeriodicD : DatumUnitPeriodicD carrier initialD

    forcingSmoothD : ForcingSmoothD carrier forcingD
    forcingPeriodicD : ForcingUnitPeriodicD carrier forcingD
    forcingRapidTimeDecayD :
      ForcingRapidTimeDecayOfAllDerivativesD carrier forcingD

    noGlobalSmoothPeriodicSolutionD :
      FeffermanPeriodicForcedGlobalSolution
        carrier viscosity initialD forcingD → ⊥

open FeffermanPeriodicForcedBreakdownWitness public

FeffermanPeriodicClayStatementD :
  FeffermanPeriodicForcedBreakdownCarrier → Set₁
FeffermanPeriodicClayStatementD carrier =
  (viscosity : ViscosityD carrier) →
  PositiveViscosityD carrier viscosity →
  FeffermanPeriodicForcedBreakdownWitness carrier viscosity

------------------------------------------------------------------------
-- One literal four-lane instance and the actual proof obligations.
------------------------------------------------------------------------

record LiteralClayABCDInstance : Set₂ where
  field
    carrierA : FeffermanEuclideanClayCarrier
    carrierB : FeffermanPeriodicClayCarrier
    carrierC : FeffermanEuclideanForcedBreakdownCarrier
    carrierD : FeffermanPeriodicForcedBreakdownCarrier

open LiteralClayABCDInstance public

record LiteralFourAlternativeCompletion
    (instance : LiteralClayABCDInstance) : Set₂ where
  field
    proofA : FeffermanEuclideanClayStatementA (carrierA instance)
    proofB : FeffermanPeriodicClayStatementB (carrierB instance)
    proofC : FeffermanEuclideanClayStatementC (carrierC instance)
    proofD : FeffermanPeriodicClayStatementD (carrierD instance)

open LiteralFourAlternativeCompletion public

data AnyOneClayResolution (instance : LiteralClayABCDInstance) : Set₂ where
  resolvedA :
    FeffermanEuclideanClayStatementA (carrierA instance) →
    AnyOneClayResolution instance
  resolvedB :
    FeffermanPeriodicClayStatementB (carrierB instance) →
    AnyOneClayResolution instance
  resolvedC :
    FeffermanEuclideanClayStatementC (carrierC instance) →
    AnyOneClayResolution instance
  resolvedD :
    FeffermanPeriodicClayStatementD (carrierD instance) →
    AnyOneClayResolution instance

literalAllFourImpliesAnyOne :
  ∀ {instance} →
  LiteralFourAlternativeCompletion instance →
  AnyOneClayResolution instance
literalAllFourImpliesAnyOne completion =
  resolvedA (proofA completion)

------------------------------------------------------------------------
-- Exact C/D source-coordinate weld.
--
-- These equalities do NOT prove C or D.  They state that the literal C/D
-- theorem types above retain the exact coordinate distinctions already audited
-- by Round523 instead of silently collapsing to "smooth forced blowup".
------------------------------------------------------------------------

cRequiresPositiveViscosity :
  CD.requiredByC523 CD.positiveViscosity523 ≡ true
cRequiresPositiveViscosity = refl

cRequiresRapidInitialSpatialDecay :
  CD.requiredByC523 CD.rapidInitialSpatialDecay523 ≡ true
cRequiresRapidInitialSpatialDecay = refl

cRequiresRapidForcingSpaceTimeDecay :
  CD.requiredByC523 CD.rapidForcingSpaceTimeDecay523 ≡ true
cRequiresRapidForcingSpaceTimeDecay = refl

cRequiresBoundedEnergy :
  CD.requiredByC523 CD.boundedEnergyRequirement523 ≡ true
cRequiresBoundedEnergy = refl

dRequiresPositiveViscosity :
  CD.requiredByD523 CD.positiveViscosity523 ≡ true
dRequiresPositiveViscosity = refl

dRequiresPeriodicInitialDatum :
  CD.requiredByD523 CD.periodicInitialDatum523 ≡ true
dRequiresPeriodicInitialDatum = refl

dRequiresRapidForcingTimeDecay :
  CD.requiredByD523 CD.rapidForcingTimeDecay523 ≡ true
dRequiresRapidForcingTimeDecay = refl

dRequiresPeriodicSolution :
  CD.requiredByD523 CD.periodicSolutionRequirement523 ≡ true
dRequiresPeriodicSolution = refl

------------------------------------------------------------------------
-- Construction status: statement construction only, never theorem promotion.
------------------------------------------------------------------------

literalFeffermanStatementAConstructed : Bool
literalFeffermanStatementAConstructed = true

literalFeffermanStatementBReused : Bool
literalFeffermanStatementBReused =
  B.literalFeffermanPeriodicStatementConstructed

literalFeffermanStatementCConstructed : Bool
literalFeffermanStatementCConstructed = true

literalFeffermanStatementDConstructed : Bool
literalFeffermanStatementDConstructed = true

literalABCDCapstoneConstructed : Bool
literalABCDCapstoneConstructed = true

literalABCDProofsInhabitedHere : Bool
literalABCDProofsInhabitedHere = false
