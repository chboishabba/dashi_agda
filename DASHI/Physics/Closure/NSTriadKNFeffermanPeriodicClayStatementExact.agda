module DASHI.Physics.Closure.NSTriadKNFeffermanPeriodicClayStatementExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Author: Charles L. Fefferman.
-- Title: "Existence and Smoothness of the Navier--Stokes Equation".
-- Clay Mathematics Institute Millennium Prize Problem description, 2000.
-- DOI: not assigned to the official problem description.
-- Official statement used here: periodic alternative (B), including the
-- published erratum that pressure is spatially periodic as well as velocity.
--
-- PURPOSE
--
-- State the actual periodic Clay alternative without strengthening or
-- weakening its quantifiers.  In particular:
--
-- * viscosity is arbitrary and positive;
-- * space dimension is fixed to three and the spatial domain is R^3/Z^3;
-- * external force is identically zero;
-- * every smooth, divergence-free, unit-periodic datum is admitted;
-- * no mean-zero hypothesis is added;
-- * no uniqueness requirement is added;
-- * no finite-energy requirement is added in the periodic alternative;
-- * both velocity and pressure are smooth for all nonnegative time;
-- * both velocity and pressure are unit-periodic in each spatial coordinate;
-- * the momentum equation, incompressibility and initial trace are separate
--   postconditions.
--
-- This module constructs the exact theorem type.  It does not inhabit that
-- theorem type for the physical Navier--Stokes carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record FeffermanPeriodicClayCarrier : Set₁ where
  field
    Viscosity : Set
    PositiveViscosity : Viscosity → Set

    SmoothPeriodicDatum : Set
    DatumSmoothOnThreeTorus : SmoothPeriodicDatum → Set
    DatumDivergenceFree : SmoothPeriodicDatum → Set
    DatumUnitPeriodicInThreeCoordinates : SmoothPeriodicDatum → Set

    GlobalVelocity : Set
    GlobalPressure : Set

    VelocitySmoothOnThreeTorusTimesNonnegativeTime :
      GlobalVelocity → Set
    PressureSmoothOnThreeTorusTimesNonnegativeTime :
      GlobalPressure → Set

    VelocityUnitPeriodicInThreeCoordinates : GlobalVelocity → Set
    PressureUnitPeriodicInThreeCoordinates : GlobalPressure → Set

    SolvesThreeDimensionalMomentumEquationWithZeroForce :
      Viscosity →
      GlobalVelocity →
      GlobalPressure →
      SmoothPeriodicDatum →
      Set

    IncompressibleAtEveryNonnegativeTime : GlobalVelocity → Set

    AttainsInitialDatumAtTimeZero :
      GlobalVelocity → SmoothPeriodicDatum → Set

open FeffermanPeriodicClayCarrier public

record FeffermanPeriodicGlobalSolutionWitness
    (carrier : FeffermanPeriodicClayCarrier)
    (viscosity : Viscosity carrier)
    (initial : SmoothPeriodicDatum carrier) : Set₁ where
  field
    velocity : GlobalVelocity carrier
    pressure : GlobalPressure carrier

    velocitySmooth :
      VelocitySmoothOnThreeTorusTimesNonnegativeTime carrier velocity
    pressureSmooth :
      PressureSmoothOnThreeTorusTimesNonnegativeTime carrier pressure

    velocityPeriodic :
      VelocityUnitPeriodicInThreeCoordinates carrier velocity
    pressurePeriodic :
      PressureUnitPeriodicInThreeCoordinates carrier pressure

    solvesMomentumEquation :
      SolvesThreeDimensionalMomentumEquationWithZeroForce carrier
        viscosity velocity pressure initial

    incompressible :
      IncompressibleAtEveryNonnegativeTime carrier velocity

    initialTrace :
      AttainsInitialDatumAtTimeZero carrier velocity initial

open FeffermanPeriodicGlobalSolutionWitness public

FeffermanPeriodicClayStatementB :
  FeffermanPeriodicClayCarrier → Set₁
FeffermanPeriodicClayStatementB carrier =
  (viscosity : Viscosity carrier) →
  PositiveViscosity carrier viscosity →
  (initial : SmoothPeriodicDatum carrier) →
  DatumSmoothOnThreeTorus carrier initial →
  DatumDivergenceFree carrier initial →
  DatumUnitPeriodicInThreeCoordinates carrier initial →
  FeffermanPeriodicGlobalSolutionWitness carrier viscosity initial

record FeffermanPeriodicRequirementAudit : Set where
  constructor feffermanPeriodicRequirementAudit
  field
    arbitraryPositiveViscosityQuantified : Bool
    threeDimensionalUnitTorusFixed : Bool
    zeroExternalForceLiteral : Bool
    arbitrarySmoothPeriodicDatumQuantified : Bool
    divergenceFreeDatumRequired : Bool
    meanZeroDatumNotRequired : Bool
    globalVelocitySmoothnessRequired : Bool
    globalPressureSmoothnessRequired : Bool
    velocityPeriodicityRequired : Bool
    pressurePeriodicityErratumRequired : Bool
    momentumEquationRequired : Bool
    incompressibilityRequired : Bool
    initialTraceRequired : Bool
    uniquenessNotAdded : Bool
    periodicEnergyBoundNotAdded : Bool
    physicalTheoremInhabited : Bool

open FeffermanPeriodicRequirementAudit public

canonicalFeffermanPeriodicRequirementAudit :
  FeffermanPeriodicRequirementAudit
canonicalFeffermanPeriodicRequirementAudit =
  feffermanPeriodicRequirementAudit
    true true true true true true true true true true true true true true true
    false

literalFeffermanPeriodicStatementConstructed : Bool
literalFeffermanPeriodicStatementConstructed = true

literalFeffermanPeriodicStatementConstructedIsTrue :
  literalFeffermanPeriodicStatementConstructed ≡ true
literalFeffermanPeriodicStatementConstructedIsTrue = refl

physicalFeffermanPeriodicTheoremNotPromoted :
  physicalTheoremInhabited canonicalFeffermanPeriodicRequirementAudit ≡ false
physicalFeffermanPeriodicTheoremNotPromoted = refl
