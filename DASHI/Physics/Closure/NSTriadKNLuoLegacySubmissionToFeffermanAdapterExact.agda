module DASHI.Physics.Closure.NSTriadKNLuoLegacySubmissionToFeffermanAdapterExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Author: Charles L. Fefferman.
-- Title: "Existence and Smoothness of the Navier--Stokes Equation".
-- Clay Mathematics Institute Millennium Prize Problem description, 2000.
-- DOI: not assigned to the official problem description.
--
-- PURPOSE
--
-- Connect the repository's older, stronger submission witness to the literal
-- Fefferman periodic witness without pretending the two carriers are
-- definitionally identical.  The adapter must explicitly transport:
--
-- * the datum, velocity and pressure carriers;
-- * global smoothness;
-- * velocity periodicity;
-- * pressure periodicity from Fefferman's erratum;
-- * the zero-force three-dimensional momentum equation at the selected
--   positive viscosity;
-- * incompressibility and the initial trace.
--
-- Legacy uniqueness, mean-zero preservation and energy equality are not Clay
-- postconditions and are deliberately discarded by the adapter.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNPeriodicNavierStokesSubmissionTheoremExact as Legacy
import DASHI.Physics.Closure.NSTriadKNFeffermanPeriodicClayStatementExact as Clay

record LegacySubmissionToFeffermanAdapter
    (legacy : Legacy.PeriodicNavierStokesSubmissionCarrier)
    (clay : Clay.FeffermanPeriodicClayCarrier) : Set₁ where
  field
    encodeDatum :
      Clay.SmoothPeriodicDatum clay → Legacy.SmoothPeriodicDatum legacy

    decodeVelocity :
      Legacy.GlobalVelocity legacy → Clay.GlobalVelocity clay
    decodePressure :
      Legacy.GlobalPressure legacy → Clay.GlobalPressure clay

    transportVelocitySmooth :
      (legacyVelocity : Legacy.GlobalVelocity legacy) →
      Legacy.GlobalSmoothVelocity legacy legacyVelocity →
      Clay.VelocitySmoothOnThreeTorusTimesNonnegativeTime clay
        (decodeVelocity legacyVelocity)

    transportPressureSmooth :
      (legacyPressure : Legacy.GlobalPressure legacy) →
      Legacy.GlobalSmoothPressure legacy legacyPressure →
      Clay.PressureSmoothOnThreeTorusTimesNonnegativeTime clay
        (decodePressure legacyPressure)

    transportVelocityPeriodicity :
      (legacyVelocity : Legacy.GlobalVelocity legacy) →
      Clay.VelocityUnitPeriodicInThreeCoordinates clay
        (decodeVelocity legacyVelocity)

    transportPressurePeriodicityErratum :
      (legacyPressure : Legacy.GlobalPressure legacy) →
      Clay.PressureUnitPeriodicInThreeCoordinates clay
        (decodePressure legacyPressure)

    transportMomentumEquation :
      (viscosity : Clay.Viscosity clay) →
      (initial : Clay.SmoothPeriodicDatum clay) →
      (legacyVelocity : Legacy.GlobalVelocity legacy) →
      (legacyPressure : Legacy.GlobalPressure legacy) →
      Legacy.SolvesPeriodicNavierStokes legacy
        legacyVelocity legacyPressure (encodeDatum initial) →
      Clay.SolvesThreeDimensionalMomentumEquationWithZeroForce clay
        viscosity
        (decodeVelocity legacyVelocity)
        (decodePressure legacyPressure)
        initial

    transportIncompressibility :
      (legacyVelocity : Legacy.GlobalVelocity legacy) →
      Legacy.DivergenceFreePreserved legacy legacyVelocity →
      Clay.IncompressibleAtEveryNonnegativeTime clay
        (decodeVelocity legacyVelocity)

    transportInitialTrace :
      (initial : Clay.SmoothPeriodicDatum clay) →
      (legacyVelocity : Legacy.GlobalVelocity legacy) →
      Legacy.AttainsInitialDatum legacy legacyVelocity (encodeDatum initial) →
      Clay.AttainsInitialDatumAtTimeZero clay
        (decodeVelocity legacyVelocity) initial

open LegacySubmissionToFeffermanAdapter public

legacyWitnessGivesLiteralFeffermanWitness :
  ∀ {legacy clay}
    (adapter : LegacySubmissionToFeffermanAdapter legacy clay)
    (viscosity : Clay.Viscosity clay)
    (initial : Clay.SmoothPeriodicDatum clay) →
  Legacy.PeriodicGlobalSolutionWitness legacy
    (encodeDatum adapter initial) →
  Clay.FeffermanPeriodicGlobalSolutionWitness clay viscosity initial
legacyWitnessGivesLiteralFeffermanWitness adapter viscosity initial witness =
  record
    { velocity =
        decodeVelocity adapter (Legacy.velocity witness)
    ; pressure =
        decodePressure adapter (Legacy.pressure witness)
    ; velocitySmooth =
        transportVelocitySmooth adapter
          (Legacy.velocity witness)
          (Legacy.velocitySmooth witness)
    ; pressureSmooth =
        transportPressureSmooth adapter
          (Legacy.pressure witness)
          (Legacy.pressureSmooth witness)
    ; velocityPeriodic =
        transportVelocityPeriodicity adapter
          (Legacy.velocity witness)
    ; pressurePeriodic =
        transportPressurePeriodicityErratum adapter
          (Legacy.pressure witness)
    ; solvesMomentumEquation =
        transportMomentumEquation adapter
          viscosity initial
          (Legacy.velocity witness)
          (Legacy.pressure witness)
          (Legacy.solvesEquation witness)
    ; incompressible =
        transportIncompressibility adapter
          (Legacy.velocity witness)
          (Legacy.divergenceFree witness)
    ; initialTrace =
        transportInitialTrace adapter
          initial
          (Legacy.velocity witness)
          (Legacy.initialTrace witness)
    }

record LegacyAdapterAuthorityBoundary : Set where
  constructor legacyAdapterAuthorityBoundary
  field
    strongerLegacyWitnessCanBeForgottenSafely : Bool
    uniquenessAndEnergyNotRequiredByClay : Bool
    pressurePeriodicityTransportExplicit : Bool
    viscosityTransportExplicit : Bool
    physicalCarrierAdapterInhabited : Bool

open LegacyAdapterAuthorityBoundary public

canonicalLegacyAdapterAuthorityBoundary : LegacyAdapterAuthorityBoundary
canonicalLegacyAdapterAuthorityBoundary =
  legacyAdapterAuthorityBoundary true true true true false

legacyToFeffermanWitnessReducerConstructed : Bool
legacyToFeffermanWitnessReducerConstructed = true

legacyToFeffermanWitnessReducerConstructedIsTrue :
  legacyToFeffermanWitnessReducerConstructed ≡ true
legacyToFeffermanWitnessReducerConstructedIsTrue = refl
