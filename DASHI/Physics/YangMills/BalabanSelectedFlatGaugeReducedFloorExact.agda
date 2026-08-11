module DASHI.Physics.YangMills.BalabanSelectedFlatGaugeReducedFloorExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Identify a concrete reduced multiplier sector at the identity background.
-- A gauge multiplier is a three-component scalar field on the side-four
-- periodic torus.  Removing exactly its three constant components gives
-- componentwise global mean zero.  The already machine-checked side-four
-- Poincare theorem then yields, with no rank inference and no deleted matrix
-- rows,
--
--   (1/16) ||lambda||^2 <= sum_{a,mu} ||d_mu lambda^a||^2.
--
-- This is the first strict multiplier-space floor used by the physical
-- constraint Gram programme.  It is deliberately a flat-background theorem:
-- a later background theorem must prove which redundancy fibre survives the
-- covariant transport before this floor may be promoted to K_A.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanPath4GeneratedLDLCertificate as LDL
import DASHI.Physics.YangMills.BalabanPath4PhysicalVarianceDecompositionExact as Variance
import DASHI.Physics.YangMills.BalabanPath4GlobalPoincareExact as Poincare
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalFlatGaugeDivergenceIdentificationExact as FlatGauge

GaugeMultiplier : Set
GaugeMultiplier = FlatGauge.GaugeCoordinate4 → ℚ

gaugeMultiplierField :
  GaugeMultiplier → Coordinates.LieCoordinate3 → Periodic.ScalarField
gaugeMultiplierField multiplier coordinate site =
  multiplier (pair coordinate site)

gaugeMultiplierNormSq : GaugeMultiplier → ℚ
gaugeMultiplierNormSq multiplier =
  Variance.globalNormSq
    (gaugeMultiplierField multiplier Coordinates.coordinateX)
  + Variance.globalNormSq
    (gaugeMultiplierField multiplier Coordinates.coordinateY)
  + Variance.globalNormSq
    (gaugeMultiplierField multiplier Coordinates.coordinateZ)

gaugeMultiplierGradientEnergy : GaugeMultiplier → ℚ
gaugeMultiplierGradientEnergy multiplier =
  Poincare.globalDirectionalEnergy
    (gaugeMultiplierField multiplier Coordinates.coordinateX)
  + Poincare.globalDirectionalEnergy
    (gaugeMultiplierField multiplier Coordinates.coordinateY)
  + Poincare.globalDirectionalEnergy
    (gaugeMultiplierField multiplier Coordinates.coordinateZ)

record FlatGaugeReducedMultiplier (multiplier : GaugeMultiplier) : Set where
  field
    coordinateXMeanZero :
      Variance.GlobalMeanZero4
        (gaugeMultiplierField multiplier Coordinates.coordinateX)
    coordinateYMeanZero :
      Variance.GlobalMeanZero4
        (gaugeMultiplierField multiplier Coordinates.coordinateY)
    coordinateZMeanZero :
      Variance.GlobalMeanZero4
        (gaugeMultiplierField multiplier Coordinates.coordinateZ)
open FlatGaugeReducedMultiplier public

flatGaugeReducedPoincare :
  ∀ multiplier →
  FlatGaugeReducedMultiplier multiplier →
  LDL.oneSixteenth * gaugeMultiplierNormSq multiplier
  ≤ gaugeMultiplierGradientEnergy multiplier
flatGaugeReducedPoincare multiplier reduced =
  let
    xBound =
      Poincare.path4GlobalPoincare
        (gaugeMultiplierField multiplier Coordinates.coordinateX)
        (coordinateXMeanZero reduced)

    yBound =
      Poincare.path4GlobalPoincare
        (gaugeMultiplierField multiplier Coordinates.coordinateY)
        (coordinateYMeanZero reduced)

    zBound =
      Poincare.path4GlobalPoincare
        (gaugeMultiplierField multiplier Coordinates.coordinateZ)
        (coordinateZMeanZero reduced)

    summed :
      (LDL.oneSixteenth
        * Variance.globalNormSq
            (gaugeMultiplierField multiplier Coordinates.coordinateX)
      + LDL.oneSixteenth
        * Variance.globalNormSq
            (gaugeMultiplierField multiplier Coordinates.coordinateY))
      + LDL.oneSixteenth
        * Variance.globalNormSq
            (gaugeMultiplierField multiplier Coordinates.coordinateZ)
      ≤ gaugeMultiplierGradientEnergy multiplier
    summed = ℚP.+-mono-≤ (ℚP.+-mono-≤ xBound yBound) zBound

    lowerExact :
      LDL.oneSixteenth * gaugeMultiplierNormSq multiplier
      ≡
      (LDL.oneSixteenth
        * Variance.globalNormSq
            (gaugeMultiplierField multiplier Coordinates.coordinateX)
      + LDL.oneSixteenth
        * Variance.globalNormSq
            (gaugeMultiplierField multiplier Coordinates.coordinateY))
      + LDL.oneSixteenth
        * Variance.globalNormSq
            (gaugeMultiplierField multiplier Coordinates.coordinateZ)
    lowerExact =
      ℚRing.solve-∀
        LDL.oneSixteenth
        (Variance.globalNormSq
          (gaugeMultiplierField multiplier Coordinates.coordinateX))
        (Variance.globalNormSq
          (gaugeMultiplierField multiplier Coordinates.coordinateY))
        (Variance.globalNormSq
          (gaugeMultiplierField multiplier Coordinates.coordinateZ))
  in
  subst
    (λ lower → lower ≤ gaugeMultiplierGradientEnergy multiplier)
    (sym lowerExact)
    summed

flatGaugeReducedMultiplierFloorLevel : ProofLevel
flatGaugeReducedMultiplierFloorLevel = machineChecked
