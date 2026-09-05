module DASHI.Physics.ExoticGravity.LiTorrStandardGRRotatingSourceKernelExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- STANDARD-GR ROTATING-SOURCE KERNEL FOR THE LI/TORR LANE
--
-- This owner deliberately stops short of claiming a same-apparatus numerical
-- prediction.  The 1993 Torr/Li paper gives an illustrative coherent volume
-- (~0.1 m^3) and laboratory-scale reasoning, but not a unique fully specified
-- source/probe geometry from which one literal apparatus field can be rebuilt.
--
-- What we can own now is the weak-field GR scaling kernel: ordinary
-- gravitomagnetism is sourced by mass-current / angular momentum and is
-- suppressed by G/c^2.  Convention-dependent numerical factors remain an
-- explicit coordinate rather than being silently fixed.
------------------------------------------------------------------------

record RotatingSourceGeometry : Set₁ where
  constructor rotating-source-geometry
  field
    Mass Radius AngularVelocity ProbeDistance : Set
    geometryLabel : String

open RotatingSourceGeometry public

record WeakFieldGRKernel (g : RotatingSourceGeometry) : Set₁ where
  constructor weak-field-gr-kernel
  field
    NewtonG SpeedOfLight ConventionFactor AngularMomentum : Set
    angularMomentumExpression : String
    gravitomagneticScalingExpression : String
    sourceReference : String

open WeakFieldGRKernel public

------------------------------------------------------------------------
-- For a ring-like source the ordinary mechanical angular momentum scales as
-- J ~ M R^2 omega.  Far from a localized rotating source the gravitomagnetic
-- field scales as G J / (c^2 r^3), modulo convention / geometry factors.
------------------------------------------------------------------------

canonicalRotatingRingKernel :
  (g : RotatingSourceGeometry) → WeakFieldGRKernel g
canonicalRotatingRingKernel g = weak-field-gr-kernel
  Set
  Set
  Set
  Set
  "J = M R^2 omega for an ideal thin ring"
  "|B_g| = kappa_G * G * |J| / (c^2 r^3) in the far-field rotating-source limit"
  "weak-field GR / Lense-Thirring gravitomagnetic scaling"

------------------------------------------------------------------------
-- BIDI geometry firewall.
------------------------------------------------------------------------

record GeometryInstantiationBoundary : Set where
  constructor geometry-instantiation-boundary
  field
    illustrativeVolumeDeterminesUniqueGeometry : Bool
    illustrativeVolumeDeterminesUniqueGeometryIsFalse :
      illustrativeVolumeDeterminesUniqueGeometry ≡ false

    laboratoryScaleDeterminesProbeLocation : Bool
    laboratoryScaleDeterminesProbeLocationIsFalse :
      laboratoryScaleDeterminesProbeLocation ≡ false

    genericGRKernelEqualsSameApparatusPrediction : Bool
    genericGRKernelEqualsSameApparatusPredictionIsFalse :
      genericGRKernelEqualsSameApparatusPrediction ≡ false

    exactGeometryRequiredForLiteralMagnitudeComparison : Bool
    exactGeometryRequiredForLiteralMagnitudeComparisonIsTrue :
      exactGeometryRequiredForLiteralMagnitudeComparison ≡ true

canonicalGeometryInstantiationBoundary : GeometryInstantiationBoundary
canonicalGeometryInstantiationBoundary =
  geometry-instantiation-boundary false refl false refl false refl true refl

------------------------------------------------------------------------
-- Scaling discriminator.
--
-- A proposed new coherent enhancement is not needed to obtain a nonzero
-- gravitomagnetic field: ordinary GR already predicts one from angular
-- momentum.  The scientific question is whether an observed field exceeds
-- that ordinary source prediction with a phase-correlated residual.
------------------------------------------------------------------------

record OrdinaryVsCoherentScalingBoundary : Set where
  constructor ordinary-vs-coherent-scaling-boundary
  field
    ordinaryRotationProducesNonzeroGravitomagnetism : Bool
    ordinaryRotationProducesNonzeroGravitomagnetismIsTrue :
      ordinaryRotationProducesNonzeroGravitomagnetism ≡ true

    superconductingCoherenceRequiredForOrdinaryGRField : Bool
    superconductingCoherenceRequiredForOrdinaryGRFieldIsFalse :
      superconductingCoherenceRequiredForOrdinaryGRField ≡ false

    nonzeroGRFieldImpliesLiTorrEnhancement : Bool
    nonzeroGRFieldImpliesLiTorrEnhancementIsFalse :
      nonzeroGRFieldImpliesLiTorrEnhancement ≡ false

    phaseCorrelatedExcessOverGRIsRelevantResidual : Bool
    phaseCorrelatedExcessOverGRIsRelevantResidualIsTrue :
      phaseCorrelatedExcessOverGRIsRelevantResidual ≡ true

canonicalOrdinaryVsCoherentScalingBoundary : OrdinaryVsCoherentScalingBoundary
canonicalOrdinaryVsCoherentScalingBoundary =
  ordinary-vs-coherent-scaling-boundary true refl false refl false refl true refl
