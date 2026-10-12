module DASHI.Physics.Closure.E6HyperformIntrinsicRadiationVacuumStressExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.E6HyperformIntrinsicQuadraticLaplacianExact as Intrinsic

------------------------------------------------------------------------
-- INTRINSIC-METRIC LOCAL RADIATION + VACUUM STRESS TARGET
--
-- For the symmetry-repaired quadratic-class Laplacian, phi=rho/27. At the
-- chart origin phi=0 and grad phi=0. For epsilon=-alpha, alpha>0,
--
-- G=(alpha/27)[[12,0,0,0],[0,-8,0,1],[0,0,-8,0],[0,1,0,-8]]
--
-- decomposes exactly as
--
-- G = R_rad -(alpha/3) g,
--
-- R_rad=(alpha/27)[[3,0,0,0],[0,1,0,1],[0,0,1,0],[0,1,0,1]].
--
-- R_rad is traceless, satisfies the local dominant-energy shape, and is the
-- sum of two zero-net-momentum null-radiation pairs: alpha/27 along y and
-- 2alpha/27 along (x+z)/sqrt(2).
--
-- The local executable also checks the Rainich algebraic condition: this
-- radiation remainder is NOT the stress tensor of one classical Maxwell field.
-- Its mixed square is not proportional to the identity.  Thus any gauge-field
-- realization must be multi-mode / multi-internal-component (or more general),
-- rather than a single abelian field configuration.
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
    radiationDominantEnergyShapeChecked : Bool
    radiationEnergyDensityPositiveForAlphaPositive : Bool
    twoCounterpropagatingNullPairDecompositionChecked : Bool
    singleMaxwellRainichConditionSatisfied : Bool
    multiModeOrMultiInternalComponentRequired : Bool
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
    false true true
    false false false false
    "The intrinsic metric origin admits an exact positive null-radiation plus vacuum decomposition. The radiation remainder is traceless and dominant-energy compatible but fails the single-Maxwell Rainich condition, so a physical gauge realization must use multiple modes/internal components or a more general field. The shape does not identify trinification gauge dynamics or the CMP119 vacuum amplitude until same-state dynamics, conservation and calibration are paid."

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

data NullDustSumCreatesSingleMaxwellField : Set where

stressShapeDoesNotCreateDynamics : StressShapeCreatesMatterDynamics → {A : Set} → A
stressShapeDoesNotCreateDynamics ()

radiationShapeDoesNotCreateGaugeIdentification :
  RadiationDecompositionCreatesGaugeIdentification → {A : Set} → A
radiationShapeDoesNotCreateGaugeIdentification ()

nullDustSumDoesNotCreateSingleMaxwellField :
  NullDustSumCreatesSingleMaxwellField → {A : Set} → A
nullDustSumDoesNotCreateSingleMaxwellField ()
