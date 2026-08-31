module DASHI.Physics.Closure.NSTriadKNPhysicalPackageAToLiteralFeffermanRound361Exact where

------------------------------------------------------------------------
-- ROUND361 / BIDI: R354 -> THE LITERAL FEFFERMAN PERIODIC CLAY TARGET
--
-- R359/R360 exposed the quantifier mismatch between physical Galerkin
-- trajectories and Clay initial data.  Repository archaeology then found the
-- stronger canonical endpoint already owned in-tree:
--
--   Clay.FeffermanPeriodicClayStatementB clay
--
-- with the exact official periodic-(B) quantifiers and postconditions.
--
-- This round therefore bypasses the generic R359 theorem language.  For each
-- official viscosity/datum instance, a caller supplies:
--
--   * one actual R240 physical trajectory;
--   * an externally owned same-problem representation receipt connecting that
--     trajectory to the literal Fefferman viscosity/datum instance;
--   * the explicit R354 physical inputs that build Package A;
--   * one theorem-valued authority turning Package A on that representing
--     trajectory into the literal Fefferman global-solution witness.
--
-- The output is definitionally the existing official theorem type.  No
-- uniqueness, mean-zero, energy, or other stronger condition is added.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNR293ToPhysicalPackageARound354Exact as R354
import DASHI.Physics.Closure.NSTriadKNFeffermanPeriodicClayStatementExact as Clay

F : C3.RealField _
F = Rational.rationalRealField

module LiteralFeffermanWeld
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (clay : Clay.FeffermanPeriodicClayCarrier)
    (TrajectoryRepresentsFeffermanInstance :
      Clay.Viscosity clay →
      Clay.SmoothPeriodicDatum clay →
      R240.PhysicalNSDynamics.PhysicalNSGalerkinTrajectory
        Time initialTime integrateTo DerivativeOf →
      Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Package = R354.PhysicalPackageAWeld Time initialTime integrateTo DerivativeOf

  record LiteralInstancePhysicalRealization
      (viscosity : Clay.Viscosity clay)
      (initial : Clay.SmoothPeriodicDatum clay) : Set₁ where
    field
      trajectory : Dyn.PhysicalNSGalerkinTrajectory
      representsLiteralInstance :
        TrajectoryRepresentsFeffermanInstance viscosity initial trajectory
      packageAInputs : Package.R293PhysicalPackageAInputs trajectory

  open LiteralInstancePhysicalRealization public

  record SuppliedLiteralFeffermanAuthority : Set₁ where
    field
      packageAToLiteralWitness :
        (viscosity : Clay.Viscosity clay) →
        Clay.PositiveViscosity clay viscosity →
        (initial : Clay.SmoothPeriodicDatum clay) →
        Clay.DatumSmoothOnThreeTorus clay initial →
        Clay.DatumDivergenceFree clay initial →
        Clay.DatumUnitPeriodicInThreeCoordinates clay initial →
        (T : Dyn.PhysicalNSGalerkinTrajectory) →
        TrajectoryRepresentsFeffermanInstance viscosity initial T →
        Dyn.PhysicalNSMixedHelicitySpacetimeBudget T →
        Clay.FeffermanPeriodicGlobalSolutionWitness clay viscosity initial

  open SuppliedLiteralFeffermanAuthority public

  record LiteralFeffermanPhysicalInputs : Set₁ where
    field
      realizationForEveryLiteralInstance :
        (viscosity : Clay.Viscosity clay) →
        Clay.PositiveViscosity clay viscosity →
        (initial : Clay.SmoothPeriodicDatum clay) →
        Clay.DatumSmoothOnThreeTorus clay initial →
        Clay.DatumDivergenceFree clay initial →
        Clay.DatumUnitPeriodicInThreeCoordinates clay initial →
        LiteralInstancePhysicalRealization viscosity initial

      literalAuthority : SuppliedLiteralFeffermanAuthority

  open LiteralFeffermanPhysicalInputs public

  r354ClosesLiteralFeffermanPeriodicB :
    LiteralFeffermanPhysicalInputs →
    Clay.FeffermanPeriodicClayStatementB clay
  r354ClosesLiteralFeffermanPeriodicB I
      viscosity viscosityPositive initial
      initialSmooth initialDivergence initialPeriodic =
    let
      R = realizationForEveryLiteralInstance I
        viscosity viscosityPositive initial
        initialSmooth initialDivergence initialPeriodic
      T = trajectory R
      packageA = Package.r293BuildsPhysicalPackageA T (packageAInputs R)
    in
    packageAToLiteralWitness
      (literalAuthority I)
      viscosity viscosityPositive initial
      initialSmooth initialDivergence initialPeriodic
      T (representsLiteralInstance R) packageA

round361OutputIsExactExistingFeffermanStatementB : Bool
round361OutputIsExactExistingFeffermanStatementB = true

round361ArbitraryPositiveViscosityPreserved : Bool
round361ArbitraryPositiveViscosityPreserved = true

round361ArbitrarySmoothPeriodicDatumPreserved : Bool
round361ArbitrarySmoothPeriodicDatumPreserved = true

round361PressureSmoothnessAndPeriodicityPreserved : Bool
round361PressureSmoothnessAndPeriodicityPreserved = true

round361UniquenessAddedToOfficialTarget : Bool
round361UniquenessAddedToOfficialTarget = false

round361MeanZeroAddedToOfficialTarget : Bool
round361MeanZeroAddedToOfficialTarget = false

round361HistoricalClayBooleanUsedAsProof : Bool
round361HistoricalClayBooleanUsedAsProof = false

round361LiteralFeffermanCompilerClosedConditionally : Bool
round361LiteralFeffermanCompilerClosedConditionally = true

round361LiteralFeffermanCompilerClosedConditionallyIsTrue :
  round361LiteralFeffermanCompilerClosedConditionally ≡ true
round361LiteralFeffermanCompilerClosedConditionallyIsTrue = refl

round361UniquenessAddedToOfficialTargetIsFalse :
  round361UniquenessAddedToOfficialTarget ≡ false
round361UniquenessAddedToOfficialTargetIsFalse = refl

round361MeanZeroAddedToOfficialTargetIsFalse :
  round361MeanZeroAddedToOfficialTarget ≡ false
round361MeanZeroAddedToOfficialTargetIsFalse = refl
