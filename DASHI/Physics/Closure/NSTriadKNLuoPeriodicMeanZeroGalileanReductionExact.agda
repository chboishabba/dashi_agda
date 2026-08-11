module DASHI.Physics.Closure.NSTriadKNLuoPeriodicMeanZeroGalileanReductionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Charles L. Fefferman.
-- Title: "Existence and Smoothness of the Navier--Stokes Equation".
-- Clay Mathematics Institute Millennium Prize Problem description, 2000.
-- DOI: not assigned to the official problem description.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- The older submission carrier required mean-zero periodic data.  Fefferman's
-- periodic alternative does not.  For zero forcing, an arbitrary periodic
-- datum can be centered by subtracting its constant spatial mean.  A solution
-- of the centered problem can then be restored by the Galilean transform
--
--   u(x,t) = v(x - m t,t) + m,
--   p(x,t) = q(x - m t,t).
--
-- This module states exactly the producers needed for that reduction and
-- proves the quantifier transport from a mean-zero solver to Fefferman's
-- all-periodic-data theorem.  The continuum mean integral and the analytic
-- verification of the displayed Galilean formulas remain explicit inputs;
-- they are not hidden behind a new mean-zero Clay hypothesis.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNFeffermanPeriodicClayStatementExact as Clay

record PeriodicMeanZeroGalileanInputs
    (carrier : Clay.FeffermanPeriodicClayCarrier) : Set₁ where
  field
    MeanVelocity : Set
    DatumMeanZero : Clay.SmoothPeriodicDatum carrier → Set

    spatialMean :
      Clay.SmoothPeriodicDatum carrier → MeanVelocity

    centeredDatum :
      Clay.SmoothPeriodicDatum carrier → Clay.SmoothPeriodicDatum carrier

    centeredDatumSmooth :
      (initial : Clay.SmoothPeriodicDatum carrier) →
      Clay.DatumSmoothOnThreeTorus carrier initial →
      Clay.DatumSmoothOnThreeTorus carrier (centeredDatum initial)

    centeredDatumDivergenceFree :
      (initial : Clay.SmoothPeriodicDatum carrier) →
      Clay.DatumDivergenceFree carrier initial →
      Clay.DatumDivergenceFree carrier (centeredDatum initial)

    centeredDatumPeriodic :
      (initial : Clay.SmoothPeriodicDatum carrier) →
      Clay.DatumUnitPeriodicInThreeCoordinates carrier initial →
      Clay.DatumUnitPeriodicInThreeCoordinates carrier (centeredDatum initial)

    centeredDatumHasZeroMean :
      (initial : Clay.SmoothPeriodicDatum carrier) →
      DatumMeanZero (centeredDatum initial)

    centeredGlobalSolver :
      (viscosity : Clay.Viscosity carrier) →
      Clay.PositiveViscosity carrier viscosity →
      (initial : Clay.SmoothPeriodicDatum carrier) →
      Clay.DatumSmoothOnThreeTorus carrier initial →
      Clay.DatumDivergenceFree carrier initial →
      Clay.DatumUnitPeriodicInThreeCoordinates carrier initial →
      DatumMeanZero initial →
      Clay.FeffermanPeriodicGlobalSolutionWitness carrier viscosity initial

    restoreGalileanSolution :
      (viscosity : Clay.Viscosity carrier) →
      (initial : Clay.SmoothPeriodicDatum carrier) →
      (centered :
        Clay.FeffermanPeriodicGlobalSolutionWitness carrier viscosity
          (centeredDatum initial)) →
      Clay.FeffermanPeriodicGlobalSolutionWitness carrier viscosity initial

open PeriodicMeanZeroGalileanInputs public

meanZeroSolverAndGalileanRestorationGiveClayB :
  (carrier : Clay.FeffermanPeriodicClayCarrier) →
  PeriodicMeanZeroGalileanInputs carrier →
  Clay.FeffermanPeriodicClayStatementB carrier
meanZeroSolverAndGalileanRestorationGiveClayB carrier inputs
  viscosity viscosityPositive initial initialSmooth initialDivergence initialPeriodic =
  restoreGalileanSolution inputs viscosity initial
    (centeredGlobalSolver inputs
      viscosity viscosityPositive
      (centeredDatum inputs initial)
      (centeredDatumSmooth inputs initial initialSmooth)
      (centeredDatumDivergenceFree inputs initial initialDivergence)
      (centeredDatumPeriodic inputs initial initialPeriodic)
      (centeredDatumHasZeroMean inputs initial))

record MeanZeroReductionAuthorityBoundary : Set where
  constructor meanZeroReductionAuthorityBoundary
  field
    correctClayQuantifierTransportProved : Bool
    meanZeroRemovedAsClayPrecondition : Bool
    galileanRestorationInterfaceExplicit : Bool
    continuumSpatialMeanConstructed : Bool
    galileanPDEInvarianceProvedAnalytically : Bool

open MeanZeroReductionAuthorityBoundary public

canonicalMeanZeroReductionAuthorityBoundary :
  MeanZeroReductionAuthorityBoundary
canonicalMeanZeroReductionAuthorityBoundary =
  meanZeroReductionAuthorityBoundary true true true false false

meanZeroQuantifierRepairConstructed : Bool
meanZeroQuantifierRepairConstructed = true

meanZeroQuantifierRepairConstructedIsTrue :
  meanZeroQuantifierRepairConstructed ≡ true
meanZeroQuantifierRepairConstructedIsTrue = refl
