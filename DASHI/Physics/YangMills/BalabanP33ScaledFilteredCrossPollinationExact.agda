module DASHI.Physics.YangMills.BalabanP33ScaledFilteredCrossPollinationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John Cardy,
-- "Scaling and Renormalization in Statistical Physics".
-- DOI: 10.1017/CBO9781316036440.
--
-- Tadeusz Balaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. II".
-- DOI: 10.1007/BF01240221.
--
-- J. Dimock,
-- "The Renormalization Group According to Balaban III. Convergence".
-- DOI: 10.1007/s00023-013-0303-3.
--
-- DASHI CONTRIBUTION
-- Compile the already-checked lattice-gap/spacing representation into the
-- shared scale representation.  Exact dyadic scaling becomes common rescaling;
-- the physical transfer/Hessian compatibility needed to instantiate it at
-- every RG step remains conditional.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (_*_)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Common.ScaledFilteredEstimateExact as Shared
import DASHI.Physics.Common.FiniteRingScaleDualityExact as Scale
import DASHI.Physics.YangMills.BalabanP33PhysicalGapScaleInvarianceExact as Physical

physicalStateAsSharedScale :
  (state : Physical.LatticeScaleState) →
  (physicalGap : ℚ) →
  Physical.PhysicalGapAt state physicalGap →
  Shared.ScaleRepresentation
physicalStateAsSharedScale state physicalGap witness =
  Shared.scaleRepresentation
    (Physical.latticeGap state)
    (Physical.latticeSpacing state)
    physicalGap
    witness

dyadicPhysicalStateAsSharedScale :
  (state : Physical.LatticeScaleState) →
  (physicalGap : ℚ) →
  Physical.PhysicalGapAt state physicalGap →
  Shared.ScaleRepresentation
dyadicPhysicalStateAsSharedScale state physicalGap witness =
  physicalStateAsSharedScale
    (Physical.dyadicScale state)
    physicalGap
    (Physical.physicalGapPreservedByExactDyadicStep
      (Physical.dyadicScaleStep state) witness)

dyadicSharedPhysicalQuantityStable :
  (state : Physical.LatticeScaleState) →
  (physicalGap : ℚ) →
  (witness : Physical.PhysicalGapAt state physicalGap) →
  Shared.physicalQuantity
    (dyadicPhysicalStateAsSharedScale state physicalGap witness)
  ≡ physicalGap
dyadicSharedPhysicalQuantityStable state physicalGap witness = refl

dyadicSpatialFrequencyScale : Scale.SpatialFrequencyScale
dyadicSpatialFrequencyScale = Scale.dyadicOneStep

dyadicSpatialFrequencyDualityExact :
  Scale.spatialNumerator dyadicSpatialFrequencyScale
    * Scale.frequencyNumerator dyadicSpatialFrequencyScale
  ≡ Scale.spatialDenominator dyadicSpatialFrequencyScale
    * Scale.frequencyDenominator dyadicSpatialFrequencyScale
dyadicSpatialFrequencyDualityExact =
  Scale.dualProductIsOne dyadicSpatialFrequencyScale

record ScaledFilteredYMBoundary : Set where
  constructor scaledFilteredYMBoundary
  field
    commonRescalingProvesPhysicalRGCompatibility : Set
    commonRescalingDoesNotProvePhysicalRGCompatibility :
      commonRescalingProvesPhysicalRGCompatibility → Set
    commonRescalingProvesInfiniteVolumeGap : Set
    commonRescalingDoesNotProveInfiniteVolumeGap :
      commonRescalingProvesInfiniteVolumeGap → Set

canonicalScaledFilteredYMBoundary : ScaledFilteredYMBoundary
canonicalScaledFilteredYMBoundary =
  scaledFilteredYMBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
  where
  open import Data.Empty using (⊥)
