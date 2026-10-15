module DASHI.Physics.Closure.EntropyGravityIntertwinerBoundaryExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as Geometry
import DASHI.Physics.Closure.MonsterGravityAuthorityAndDimensionExact as Authority
import DASHI.Physics.Closure.MonsterC3EntropyStateCountingExact as StateCount

------------------------------------------------------------------------
-- Canonical entropy -> geometry/gravity promotion surface.
--
-- The key repo-native fact is already in KernelGeometryEmergenceObligations:
-- scalar density alone does not determine relativistic tensor-source data.
-- This module threads explicit entropy observables through the additional
-- causal, area/measure, temperature/flux and geometry obligations needed by
-- named emergent-gravity routes.
------------------------------------------------------------------------

data EntropyGravityRoute : Set where
  jacobson1995LocalHorizonRoute : EntropyGravityRoute
  jacobson2015EntanglementEquilibriumRoute : EntropyGravityRoute
  padmanabhanNullEntropyDensityRoute : EntropyGravityRoute
  moonshineAdS3GravityRoute : EntropyGravityRoute
  monstrousMTheorySpectrumRoute : EntropyGravityRoute

data EntropyCarrierKind : Set where
  microstateCountCarrier : EntropyCarrierKind
  shannonCarrier : EntropyCarrierKind
  vonNeumannCarrier : EntropyCarrierKind
  relativeEntropyCarrier : EntropyCarrierKind
  horizonAreaEntropyCarrier : EntropyCarrierKind
  nullSurfaceEntropyDensityCarrier : EntropyCarrierKind

record EntropyGravityIntertwiner : Set₁ where
  constructor entropyGravityIntertwiner
  field
    Route : EntropyGravityRoute
    EntropyState : Set
    LocalRegion : Set
    BoundarySurface : Set
    Temperature : Set
    HeatFlux : Set
    TensorSource : Set
    LorentzianGeometry : Set
    CurvatureObservable : Set
    CorrectionTerm : Set

    entropyCarrierKind : EntropyCarrierKind
    entropyObservable : EntropyState → Set
    regionMeasureOrArea : LocalRegion → Set
    causalHorizonOrBall : LocalRegion → Set
    temperatureIdentification : Temperature → Set
    heatFluxIdentification : HeatFlux → Set
    tensorSourceIdentification : TensorSource → Set
    lorentzianGeometryIdentification : LorentzianGeometry → Set

    entropyVariationLaw : Set
    bianchiCompatibility : Set
    covariantConservation : Set
    einsteinLimit : Set
    weakFieldConsistency : Set
    horizonConsistency : Set
    correctionBound : Set
    sameObjectPhysicalIdentification : Set

record EntropyGravityRouteRequirements : Set where
  constructor entropyGravityRouteRequirements
  field
    route : EntropyGravityRoute
    authorityRoute : Authority.GravityRouteDescriptor
    requiresLocalCausalStructure : Bool
    requiresAreaOrMeasure : Bool
    requiresTemperatureOrModularState : Bool
    requiresEnergyOrHeatFlux : Bool
    requiresTensorSource : Bool
    requiresLorentzianGeometry : Bool
    requiresEinsteinLimit : Bool
    requiresControlledCorrection : Bool

jacobson1995Requirements : EntropyGravityRouteRequirements
jacobson1995Requirements =
  entropyGravityRouteRequirements
    jacobson1995LocalHorizonRoute
    Authority.jacobson1995LocalHorizonRoute
    true true true true true true true true

jacobson2015Requirements : EntropyGravityRouteRequirements
jacobson2015Requirements =
  entropyGravityRouteRequirements
    jacobson2015EntanglementEquilibriumRoute
    Authority.jacobson2015EntanglementRoute
    true true true true true true true true

padmanabhanRequirements : EntropyGravityRouteRequirements
padmanabhanRequirements =
  entropyGravityRouteRequirements
    padmanabhanNullEntropyDensityRoute
    Authority.padmanabhanNullEntropyRoute
    true true false true true true true true

moonshineAdS3Requirements : EntropyGravityRouteRequirements
moonshineAdS3Requirements =
  entropyGravityRouteRequirements
    moonshineAdS3GravityRoute
    Authority.wittenAdS3MonsterRoute
    true true true true true true true true

monstrousMTheoryRequirements : EntropyGravityRouteRequirements
monstrousMTheoryRequirements =
  entropyGravityRouteRequirements
    monstrousMTheorySpectrumRoute
    Authority.monstrousMTheoryRoute
    false false false false true true true true

record EntropyGravityPromotionBoundary : Set where
  constructor entropyGravityPromotionBoundary
  field
    scalarEntropyDensityDeterminesStressTensor : Bool
    scalarEntropyDensityDeterminesStressTensorIsFalse :
      scalarEntropyDensityDeterminesStressTensor ≡ false

    entropyObservableAloneDerivesEinsteinDynamics : Bool
    entropyObservableAloneDerivesEinsteinDynamicsIsFalse :
      entropyObservableAloneDerivesEinsteinDynamics ≡ false

    monsterStateCountAloneIsPhysicalEntropy : Bool
    monsterStateCountAloneIsPhysicalEntropyIsFalse :
      monsterStateCountAloneIsPhysicalEntropy ≡ false

    monsterStateCountAloneDerivesMetric : Bool
    monsterStateCountAloneDerivesMetricIsFalse :
      monsterStateCountAloneDerivesMetric ≡ false

    horizonAreaEntropyEqualsVolumeEntropyDensityWithoutAdapter : Bool
    horizonAreaEntropyEqualsVolumeEntropyDensityWithoutAdapterIsFalse :
      horizonAreaEntropyEqualsVolumeEntropyDensityWithoutAdapter ≡ false

    namedRoutesRemainDimensionAndAssumptionScoped : Bool
    namedRoutesRemainDimensionAndAssumptionScopedIsTrue :
      namedRoutesRemainDimensionAndAssumptionScoped ≡ true

    kernelGeometryBoundaryReused : Bool
    kernelGeometryBoundaryReusedIsTrue :
      kernelGeometryBoundaryReused ≡ true

canonicalEntropyGravityPromotionBoundary : EntropyGravityPromotionBoundary
canonicalEntropyGravityPromotionBoundary =
  entropyGravityPromotionBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl

existingKernelGeometryBoundary : Geometry.KernelGeometryBoundary
existingKernelGeometryBoundary = Geometry.canonicalKernelGeometryBoundary

existingMonsterStateCountingBoundary : StateCount.StateCountingEntropyBoundary
existingMonsterStateCountingBoundary = StateCount.canonicalStateCountingEntropyBoundary

------------------------------------------------------------------------
-- Terminal adapter receipt: construction of this record would be the payment
-- needed to move a chosen entropy route toward a physical GR claim.
------------------------------------------------------------------------

record EntropyGravityPhysicalPayment : Set₁ where
  constructor entropyGravityPhysicalPayment
  field
    intertwiner : EntropyGravityIntertwiner
    geometryAdapter : Geometry.KernelGeometryAdapter
    continuumManifoldPaid : Set
    lorentzianMetricPaid : Set
    tensorSourcePaid : Set
    bianchiPaid : Set
    covariantConservationPaid : Set
    equivalencePrinciplePaid : Set
    geodesicLimitPaid : Set
    gravitationalRadiationPaid : Set
    einsteinDynamicsPaid : Set
    controlledCorrectionPaid : Set
    empiricalOrSameObjectValidation : Set
