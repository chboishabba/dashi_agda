module DASHI.Physics.YangMills.YMClayR445Base2SIPhysicalRateBIDIExact where

------------------------------------------------------------------------
-- P0 original native R445 side-four 2-step block x canonical SI units.
--
-- SOURCE OWNERS (REUSE, NO NEW MEASURE OR SI SYSTEM):
--   YMClayR445Base2ThreeAxis369FibreBIDIExact:
--       1024 source bonds <-> original 128 native addresses x 8 bits
--   YMClayR445OriginalAxialBondParityInjectiveExact:
--       the actual original pair of positive fine Wilson bonds
--   BalabanPhysicalClusteringScaleAlgebraExact:
--       rational physical inverse length from dimensionless lattice rate
--   YangMillsSIScalingEndpointExact:
--       SI-indexed inverse correlation length and hbar/c conversion boundary
--   DASHI.Physics.Units.SI and SIMetrologyBridge:
--       BIPM dimensional semantics and measured-vs-model authority
--
-- Pure two-step SI arithmetic is proved here; the original all-cutoff
-- physical small+large W1/W3 rate and matching with the actual Wilson
-- differentiated cluster activity are NOT provided.
-- SOURCE-WRITTEN; local Agda 2.9 kernel receipt not available.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Units.SI as SI
import DASHI.Physics.Units.SIMetrologyBridge as Metrology
import DASHI.Physics.Units.MechanicalDimensionExact as Mechanical
import DASHI.Physics.YangMills.YangMillsSIScalingEndpointExact as Scaling
import DASHI.Physics.YangMills.BalabanPhysicalClusteringScaleAlgebraExact as Physical
import DASHI.Physics.YangMills.YMClayR445OriginalAxialBondParityInjectiveExact as R445
import DASHI.Physics.YangMills.YMClayR445Base2ThreeAxis369FibreBIDIExact as Base2

-- This is the original Wilson native selected *fine bond*, with its
-- extra transverse three-bit source address fixed to 000. No new map.
originalSelectedBinarySIIndex : (C : R445.CoarseBond) (p : R445.Bit) →
  Base2.encodeOriginalFine
    (Base2.originalAddress C p Base2.zeroTransverse)
    ≡ R445.originalR445SelectedFineBond C p
originalSelectedBinarySIIndex = Base2.selectedZeroSheetIsOriginalR445

-- Typed physical LENGTH: two original adjacent fine links per R445
-- native axial pair. This is only a geometry/dimension construction.
fineSpacingSI :
  Physical.PhysicalScaleData → Scaling.SIIndexedQuantity ℚ SI.Length
fineSpacingSI scale = Scaling.siQuantity (Physical.latticeSpacing scale)

r445NativeAxialTwoLinkLengthSI :
  Physical.PhysicalScaleData → Scaling.SIIndexedQuantity ℚ SI.Length
r445NativeAxialTwoLinkLengthSI scale =
  Scaling.siQuantity
    (Physical.latticeSpacing scale + Physical.latticeSpacing scale)

originalR445PairLengthIsTwoFineLengths :
  (scale : Physical.PhysicalScaleData) →
  Scaling.magnitude (r445NativeAxialTwoLinkLengthSI scale) ≡
    Scaling.magnitude (fineSpacingSI scale) +
    Scaling.magnitude (fineSpacingSI scale)
originalR445PairLengthIsTwoFineLengths scale = refl

-- Reuse the existing YangMills SI dimension map for inverse length;
-- never label a bare inverse correlation length as an SI kilogram.
InverseLengthSI : Set
InverseLengthSI =
  Scaling.SIIndexedQuantity ℚ
    (Scaling.mechanicalToSI Mechanical.inverseLengthDimension)

fineInverseCorrelationLengthSI :
  Physical.PhysicalScaleData → InverseLengthSI
fineInverseCorrelationLengthSI scale =
  Scaling.siQuantity
    (Physical.latticeExponent scale * Physical.inverseSpacing scale)

-- 2 fine Wilson links per native R445 link, not 8 transverse parity
-- sheets per link: 8 indexes *alternatives*, never physical distance.
-- For a coarse dimensionless exponent lambda_c = 2 lambda_f, the
-- coarse inverse spacing MUST obey 2 a_c^-1 = a_f^-1.
-- This equality is the physically calibrated inverse-spacing input;
-- do not assume it merely from the cardinality 128*8.
record OriginalR445TwoStepSICalibration
    (scale : Physical.PhysicalScaleData) : Set where
  field
    coarseInverseSpacing : ℚ
    inverseCoarseSpacingIsHalfFine :
      coarseInverseSpacing + coarseInverseSpacing
        ≡ Physical.inverseSpacing scale

open OriginalR445TwoStepSICalibration public

coarseDimensionlessExponent :
  Physical.PhysicalScaleData → ℚ
coarseDimensionlessExponent scale =
  Physical.latticeExponent scale + Physical.latticeExponent scale

coarseInverseCorrelationLengthSI :
  (scale : Physical.PhysicalScaleData) →
  OriginalR445TwoStepSICalibration scale → InverseLengthSI
coarseInverseCorrelationLengthSI scale calibrated =
  Scaling.siQuantity
    (coarseDimensionlessExponent scale
      * coarseInverseSpacing calibrated)

-- A derived exact rational identity; not an analytic estimate.
--   (lambda+lambda)*invCoarse
--     = lambda*(invCoarse+invCoarse)
--     = lambda*invFine.
originalR445FineAndCoarseSIPhysicalRatesAgree :
  (scale : Physical.PhysicalScaleData) →
  (calibrated : OriginalR445TwoStepSICalibration scale) →
  coarseInverseCorrelationLengthSI scale calibrated
    ≡ fineInverseCorrelationLengthSI scale
originalR445FineAndCoarseSIPhysicalRatesAgree scale calibrated =
  cong Scaling.siQuantity
    (trans
      (ℚRing.solve-∀
        (Physical.latticeExponent scale)
        (coarseInverseSpacing calibrated))
      (cong
        (λ spacing → Physical.latticeExponent scale * spacing)
        (inverseCoarseSpacingIsHalfFine calibrated)))

-- The original SI owner, not this finite codec, owns conversion to kg/J.
-- A caller must provide calibrated hbar/c and hbar*c conversion laws.
originalR445SIPhysicalMass :
  Scaling.NaturalUnitConversion ℚ → InverseLengthSI →
  Scaling.SIIndexedQuantity ℚ SI.Mass
originalR445SIPhysicalMass conversion lengthRate =
  Scaling.inverseLengthToMass conversion lengthRate

originalR445SIPhysicalEnergy :
  Scaling.NaturalUnitConversion ℚ → InverseLengthSI →
  Scaling.SIIndexedQuantity ℚ SI.Energy
originalR445SIPhysicalEnergy conversion lengthRate =
  Scaling.inverseLengthToEnergy conversion lengthRate

-- A source measurement with uncertainty/version metadata is different
-- from the exact dimension carrier or a selected theoretical lattice
-- spacing. Any actual measured physical input must keep this authority.
record OriginalR445SIInputMetrology : Set₁ where
  field
    measuredSpacing : Metrology.AnySIMeasurement
    measuredSpacingDimensionIsLength :
      Metrology.AnySIMeasurement.dimension measuredSpacing ≡ SI.Length
    -- Matching the measured original length to the theoretical
    -- rational physical scale is a separate calibration witness.
    metrologyMatchesR445Scale : Set
    metrologyMatchesR445ScaleEvidence : metrologyMatchesR445Scale

-- DO NOT identify binary 000 with zero trit or presume lattice
-- lambda / a has a nontrivial, positive continuum limit.
-- A SI-typed rate equality does not inhabit full original Gibbs
-- D1.OriginalSmallLargePhysicalSource or W3 rooted-shell payment.
