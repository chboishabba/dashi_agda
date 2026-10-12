module DASHI.Physics.Closure.E6HyperformIntrinsicRadiationVacuumStressExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.E6HyperformIntrinsicQuadraticLaplacianExact as Intrinsic

------------------------------------------------------------------------
-- INTRINSIC-METRIC LOCAL RADIATION + VACUUM STRESS TARGET
--
-- For the symmetry-repaired quadratic-class Laplacian, phi = rho/27.
-- At the chart origin phi=0 and grad phi=0.  Choosing epsilon=-alpha with
-- alpha>0 in Omega=1+epsilon*phi gives the exact local Einstein tensor shape
--
--   G = (alpha/27) [[12,0,0,0],
--                   [0,-8,0,1],
--                   [0,0,-8,0],
--                   [0,1,0,-8]].
--
-- This decomposes exactly as
--
--   G = R_rad - (alpha/3) g,
--
-- where
--
--   R_rad = (alpha/27) [[3,0,0,0],
--                       [0,1,0,1],
--                       [0,0,1,0],
--                       [0,1,0,1]].
--
-- R_rad is traceless and is exactly the sum of two zero-net-momentum null
-- radiation pairs: intensity alpha/27 along y and intensity 2alpha/27 along
-- (x+z)/sqrt(2).  The second term has the standard cosmological/vacuum shape.
--
-- This is a local algebraic decomposition of the required stress SHAPE. It
-- does not prove that repository gauge fields or the CMP119 vacuum source
-- dynamically realize the amplitudes on this same state.
------------------------------------------------------------------------

originEinsteinShape : String
originEinsteinShape =
  "(alpha/27)*[[12,0,0,0],[0,-8,0,1],[0,0,-8,0],[0,1,0,-8]]"

originRadiationShape : String
originRadiationShape =
  "(alpha/27)*[[3,0,0,0],[0,1,0,1],[0,0,1,0],[0,1,0,1]]"

originVacuumShape : String
originVacuumShape = "-(alpha/3)*g_mu_nu"

radiationPairYIntensity : String
radiationPairYIntensity = "alpha/27"

radiationPairXZIntensity : String
radiationPairXZIntensity = "2*alpha/27"

record IntrinsicRadiationVacuumLocalReceipt : Set where
  constructor intrinsic-radiation-vacuum-local-receipt
  field
    intrinsicQuadraticLaplacianUsed : Bool
    originStationaryPotentialUsed : Bool
    negativeWeakAmplitudeOrientationUsed : Bool
    exactEinsteinShapeComputed : Bool
    exactVacuumPlusRadiationDecompositionChecked : Bool
    radiationTraceZeroChecked : Bool
    radiationEnergyDensityPositiveForAlphaPositive : Bool
    twoCounterpropagatingNullPairDecompositionChecked : Bool
    vacuumShapeMatchesCosmologicalTensorShape : Bool
    cmp119SameStateVacuumAmplitudePaid : Bool
    trinificationGaugeFieldSameStateRealizationPaid : Bool
    globalStressConservationPaid : Bool
    einsteinMatterEquationPaid : Bool
    boundary : String
open IntrinsicRadiationVacuumLocalReceipt public

canonicalIntrinsicRadiationVacuumLocalReceipt : IntrinsicRadiationVacuumLocalReceipt
canonicalIntrinsicRadiationVacuumLocalReceipt =
  intrinsic-radiation-vacuum-local-receipt
    true true true true true true true true true
    false false false false
    "After replacing the coordinate torus Laplacian by the intrinsic quadratic-class Laplacian, the origin Einstein tensor admits an exact positive null-radiation plus vacuum decomposition. This removes the old pure-gauge local no-go for the repaired metric and supplies a sharp matter target. It does not identify the radiation with the trinification gauge fields or the vacuum coefficient with CMP119 until same-state amplitude/dynamics/conservation receipts are paid."

record IntrinsicMatterRealisationWeld : Set₁ where
  field
    MatterState : Set
    GaugeConfiguration : Set
    VacuumSource : Set
    selectedMatterState : MatterState
    selectedGaugeConfiguration : GaugeConfiguration
    selectedVacuumSource : VacuumSource
    gaugeStressEqualsRadiationReceipt : Set
    vacuumStressEqualsMinusAlphaOverThreeMetricReceipt : Set
    sameStateReceipt : Set
    covariantConservationReceipt : Set
    calibratedAmplitudeReceipt : Set
open IntrinsicMatterRealisationWeld public

data StressShapeCreatesMatterDynamics : Set where

data RadiationDecompositionCreatesGaugeIdentification : Set where

stressShapeDoesNotCreateDynamics : StressShapeCreatesMatterDynamics → {A : Set} → A
stressShapeDoesNotCreateDynamics ()

radiationShapeDoesNotCreateGaugeIdentification :
  RadiationDecompositionCreatesGaugeIdentification → {A : Set} → A
radiationShapeDoesNotCreateGaugeIdentification ()
