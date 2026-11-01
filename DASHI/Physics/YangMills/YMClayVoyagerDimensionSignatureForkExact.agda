{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayVoyagerDimensionSignatureForkExact where

-- FINITE CLASSIFICATION FOR VIDEO'S 2D/3D/4D/5D COMPARISON.
--
-- d is the dimension of *physical spacetime* in the selected Euclidean or
-- Lorentzian YM model. Its numerical value is not a proof of equivalence
-- between a lattice Euclidean model, stochastic algorithm time, and a
-- dynamical Kaluza--Klein fifth coordinate.
--
-- Standard engineering/mass-dimension identity:
-- [g_d] = (4-d)/2 for standard YM action normalization.
-- Stored below as twice the exponent, avoiding division/real analysis.
--
-- The 5D phase-transition result of Creutz (1979) is SU(2) *Euclidean*
-- lattice dynamics with five lattice axes, not a compactification or a
-- theorem about 5D gravity.  The d=4 continuum target needs 3+1 Lorentz
-- reconstruction from a 4D Euclidean OS measure, not just dimension count.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

data PhysicalDimension : Set where
  two : PhysicalDimension
  three : PhysicalDimension
  four : PhysicalDimension
  five : PhysicalDimension

data TwiceCouplingMassDimension : Set where
  positiveTwo : TwiceCouplingMassDimension
  positiveOne : TwiceCouplingMassDimension
  zero : TwiceCouplingMassDimension
  negativeOne : TwiceCouplingMassDimension

ymTwiceCouplingDimension :
  PhysicalDimension → TwiceCouplingMassDimension
ymTwiceCouplingDimension two = positiveTwo
ymTwiceCouplingDimension three = positiveOne
ymTwiceCouplingDimension four = zero
ymTwiceCouplingDimension five = negativeOne

twoDimensionalSuperrenormalizable :
  ymTwiceCouplingDimension two ≡ positiveTwo
twoDimensionalSuperrenormalizable = refl

threeDimensionalSuperrenormalizable :
  ymTwiceCouplingDimension three ≡ positiveOne
threeDimensionalSuperrenormalizable = refl

fourDimensionalMarginal :
  ymTwiceCouplingDimension four ≡ zero
fourDimensionalMarginal = refl

fiveDimensionalNegativeCouplingDimension :
  ymTwiceCouplingDimension five ≡ negativeOne
fiveDimensionalNegativeCouplingDimension = refl

data FiveDimensionalSource : Set where
  creutzFiveEuclideanLattice : FiveDimensionalSource
  kkFourLorentzPlusCircle : FiveDimensionalSource
  stochasticThreePlusArtificialTime : FiveDimensionalSource

creutzIsNotKK :
  creutzFiveEuclideanLattice ≡ kkFourLorentzPlusCircle → ⊥
creutzIsNotKK ()

kkIsNotStochasticTime :
  kkFourLorentzPlusCircle ≡ stochasticThreePlusArtificialTime → ⊥
kkIsNotStochasticTime ()

data FourDimensionalGeometry : Set where
  euclideanFourForOS : FourDimensionalGeometry
  lorentzianThreePlusOne : FourDimensionalGeometry

euclideanFourIsNotLorentzThreePlusOneByType :
  euclideanFourForOS ≡ lorentzianThreePlusOne → ⊥
euclideanFourIsNotLorentzThreePlusOneByType ()

-- The typed object necessary for an ACTUAL model-specific dimensional
-- reduction. Merely choosing both carriers does NOT inhabit the relations.
record SelectedKKReduction : Set₁ where
  field
    Gauge5D Metric5D Gauge4D Metric4D : Set
    reduceGauge : Gauge5D → Gauge4D
    reduceMetric : Metric5D → Metric4D
    SameSelectedAction : Gauge5D → Metric5D → Set
    FourDimensionalAction : Gauge4D → Metric4D → Set
    actionDescends : ∀ gauge metric →
      SameSelectedAction gauge metric →
      FourDimensionalAction (reduceGauge gauge) (reduceMetric metric)

    PhysicalMaxwellPhoton : Gauge4D → Set
    GaugeReductionPreservesPhoton : Set
    photonWitness : GaugeReductionPreservesPhoton

    -- Full spacetime metric signature, radion stabilisation, gauge-orbit
    -- semantics, anomaly/global quotient and spectra are still separate.
    MetricSignatureReconstruction : Set
    RadionAndPhotonStability : Set
    GaugeOrbitAndSpectralTransport : Set
    SelectedPhysicalBoundarySource : Set

-- The actual source-written, model-specific missing data live in the
-- KK LARES-2/E6 source owners; this abstract record provides no values.
