{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTPositiveDensityExteriorRepulsionNoGoExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; _/_)

import DASHI.Physics.Foundations.GRQFTFiniteRationalTOVSystemExact as TOV
import DASHI.Physics.Foundations.GRQFTFiniteRationalTOVExteriorMassCollisionExact as Collision

------------------------------------------------------------------------
-- POSITIVE-DENSITY STATIC-SPHERICAL EXTERIOR NO-GO
--
-- In the ordinary spherical Einstein/TOV mass equation
--
--   m'(r) = 4*pi*r^2*rho(r),
--
-- a regular center m(0)=0 and nonnegative rho imply nondecreasing m(r).
-- Therefore a compact positive-density source cannot acquire a negative
-- Schwarzschild exterior mass merely by making pressure negative.
--
-- We encode the sign compiler separately from the exact rational fixture.
------------------------------------------------------------------------

data MetricMassSign : Set where
  negativeMetricMass : MetricMassSign
  zeroMetricMass : MetricMassSign
  positiveMetricMass : MetricMassSign

data DensityShellSign : Set where
  zeroDensityShell : DensityShellSign
  positiveDensityShell : DensityShellSign

accumulateShell :
  MetricMassSign → DensityShellSign → MetricMassSign
accumulateShell negativeMetricMass zeroDensityShell = negativeMetricMass
accumulateShell negativeMetricMass positiveDensityShell = negativeMetricMass
accumulateShell zeroMetricMass zeroDensityShell = zeroMetricMass
accumulateShell zeroMetricMass positiveDensityShell = positiveMetricMass
accumulateShell positiveMetricMass shell = positiveMetricMass

regularCenterMassSign : MetricMassSign
regularCenterMassSign = zeroMetricMass

onePositiveShellFromRegularCenterIsPositive :
  accumulateShell regularCenterMassSign positiveDensityShell
    ≡ positiveMetricMass
onePositiveShellFromRegularCenterIsPositive = refl

twoPositiveShellsFromRegularCenterArePositive :
  accumulateShell
    (accumulateShell regularCenterMassSign positiveDensityShell)
    positiveDensityShell
  ≡ positiveMetricMass
twoPositiveShellsFromRegularCenterArePositive = refl

positiveMassCannotBeNegative :
  positiveMetricMass ≡ negativeMetricMass → ⊥
positiveMassCannotBeNegative ()

------------------------------------------------------------------------
-- EXACT FIXTURE INSTANCE
------------------------------------------------------------------------

finiteSurfaceMetricMass : ℚ
finiteSurfaceMetricMass = TOV.outerMassTarget

finiteSurfaceMetricMassIsPositiveQuarter :
  finiteSurfaceMetricMass ≡ Int.+ 1 / 4
finiteSurfaceMetricMassIsPositiveQuarter = refl

finitePressureWeightedActiveStressIsNegative :
  TOV.finiteIntegratedActiveMass ≡ - (Int.+ 11 / 12)
finitePressureWeightedActiveStressIsNegative =
  TOV.finiteIntegratedActiveMassIsNegativeElevenTwelfths

finiteNegativeActiveStressDoesNotFlipMetricMass :
  finiteSurfaceMetricMass ≡ TOV.finiteIntegratedActiveMass → ⊥
finiteNegativeActiveStressDoesNotFlipMetricMass ()

------------------------------------------------------------------------
-- ROUTE CLASSIFICATION FOR TRUE EXTERIOR REPULSION
------------------------------------------------------------------------

data ExteriorRepulsionEscapeRoute : Set where
  negativeEnergyDensityContribution : ExteriorRepulsionEscapeRoute
  negativeSurfaceEnergyJunction : ExteriorRepulsionEscapeRoute
  nonVacuumExteriorStress : ExteriorRepulsionEscapeRoute
  modifiedGravityOrEffectiveCoupling : ExteriorRepulsionEscapeRoute
  timeDependentOrNonStaticGeometry : ExteriorRepulsionEscapeRoute
  nonSphericalOrTopologicalRoute : ExteriorRepulsionEscapeRoute

record StandardStaticPositiveDensityExteriorAssumptions : Set where
  constructor standard-static-positive-density-exterior-assumptions
  field
    regularCenter : Bool
    nonnegativeDensity : Bool
    ordinaryEinsteinMassEquation : Bool
    staticSphericalSource : Bool
    vacuumSchwarzschildExterior : Bool
    positiveNewtonCoupling : Bool

open StandardStaticPositiveDensityExteriorAssumptions public

canonicalStandardStaticPositiveDensityExteriorAssumptions :
  StandardStaticPositiveDensityExteriorAssumptions
canonicalStandardStaticPositiveDensityExteriorAssumptions =
  standard-static-positive-density-exterior-assumptions
    true true true true true true

record PositiveDensityExteriorRepulsionNoGoBoundary : Set where
  constructor positive-density-exterior-repulsion-no-go-boundary
  field
    negativePressureCanGiveLocalDefocusing : Bool
    negativePressureAloneCanMakeMetricMassNegative : Bool
    regularPositiveDensityMassAccumulationStaysNonnegative : Bool
    finiteLiteralTOVSurfaceMassPositive : Bool
    finiteLiteralTOVStandardExteriorRepulsive : Bool
    trueExteriorRepulsionNeedsEscapeRoute : Bool
    activeStressDiagnosticEqualsSchwarzschildMassByDefault : Bool

canonicalPositiveDensityExteriorRepulsionNoGoBoundary :
  PositiveDensityExteriorRepulsionNoGoBoundary
canonicalPositiveDensityExteriorRepulsionNoGoBoundary =
  positive-density-exterior-repulsion-no-go-boundary
    true false true true false true false
