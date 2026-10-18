{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116SelectedMarkedExpansionScaleCalibrationRound416Exact where

------------------------------------------------------------------------
-- ROUND416 / R415 SELECTED SOURCE DECAY -> PINNED REAL B-ENV CALIBRATION
--
-- R415 already proves the quantitative inequality
--
--   |selectedBoundary|
--     <= sourceAmplitude * selectedDecayWeight.
--
-- The preferred pinned CMP119 B lane does not need a second decay theorem.
-- It only needs to identify, on the SAME selected source pair:
--
--   (1) CMP116.sourceEnvelope = |R415 selectedBoundary|,
--   (2) R415 sourceAmplitude = one cutoff-uniform source amplitude,
--   (3) R415 selected decay weight
--         = exp(- mu * d_lattice(physicalDistance)).
--
-- Once those same-object coordinates are supplied, the existing scale
-- calibration owner transports the lattice exponential to the physical
-- exponential and the existing real-CMP119 owner passes the resulting bound
-- to the continuum covariance.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (cong₂; subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _*ℝ_; -ℝ_; absℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as CMP116
import DASHI.Physics.YangMills.BalabanCMP116SelectedSupportConnectionRound411Exact as R411
import DASHI.Physics.YangMills.BalabanCMP116ConnectingOuterSumRound414Exact as R414
import DASHI.Physics.YangMills.BalabanCMP116SelectedMarkedExpansionRound415Exact as R415
import DASHI.Physics.YangMills.BalabanPhysicalClusteringScaleAlgebraExact as Scale
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCMP116ScaleCalibrationExact as ScaleCal

record SelectedR415EnvelopeCalibration
    (ScaleCarrier Volume Root SourceDirection Index Domain Term Operator : Set)
    (source :
      CMP116.PublishedCMP116DifferentiatedLocalization
        ScaleCarrier Volume Root SourceDirection ℝ)
    (sourceLeft sourceRight : Index → SourceDirection)
    (scaleAt : Nat → ScaleCarrier)
    (volumeAt : Nat → Volume)
    (expReal : ℝ → ℝ)
    (embedding : Embed.OrderedRationalRealEmbedding) : Set₂ where
  field
    scaleData : Scale.PhysicalScaleData

    physicalDistance : Index → ℚ
    physicalDistanceNonnegative :
      ∀ index → 0ℚ ≤ physicalDistance index

    sourceAmplitude physicalAmplitude : ℝ
    sourceAmplitudeNonnegative : 0ℝ ≤ℝ sourceAmplitude
    sourceAmplitudeBelowPhysicalAmplitude :
      sourceAmplitude ≤ℝ physicalAmplitude

    exponentialOrder : ScaleCal.RealNegativeExponentialOrder expReal

    expansionAt :
      Nat → Index → R415.SelectedCMP116MarkedExpansion Domain Term Operator

    -- Same source-envelope object: no new inequality.
    sourceEnvelopeIsSelectedBoundaryMagnitude :
      ∀ cutoff index →
      CMP116.sourceEnvelope source
        (scaleAt cutoff)
        (volumeAt cutoff)
        (CMP116.sourceRoot source
          (scaleAt cutoff)
          (volumeAt cutoff)
          (sourceLeft index)
          (sourceRight index))
        (CMP116.sourceDistance source
          (sourceLeft index)
          (sourceRight index))
      ≡
      absℝ
        (R415.selectedBoundaryIntegrand
          (expansionAt cutoff index))

    -- R415's outer amplitude is the cutoff-uniform amplitude consumed by the
    -- physical scale calibration.
    selectedExpansionAmplitudeIsUniform :
      ∀ cutoff index →
      R415.sourceAmplitude (expansionAt cutoff index)
      ≡ sourceAmplitude

    -- R415's abstract antitone selected weight is the concrete lattice
    -- exponential already used by the pinned physical scale theorem.
    selectedExpansionDecayIsLatticeExponential :
      ∀ cutoff index →
      R414.weight
        (R415.decay (expansionAt cutoff index))
        (R411.selectedConnectingDistance
          (R415.geometry (expansionAt cutoff index)))
      ≡
      expReal
        (-ℝ
          ScaleCal.embedQ embedding
            (Scale.latticeExponent scaleData
              * Scale.latticeDistance scaleData
                  (physicalDistance index)))

open SelectedR415EnvelopeCalibration public

selectedSourceEnvelopeBelowLatticeExponential :
  ∀ {ScaleCarrier Volume Root SourceDirection Index Domain Term Operator
      source sourceLeft sourceRight scaleAt volumeAt expReal embedding}
    (calibration :
      SelectedR415EnvelopeCalibration
        ScaleCarrier Volume Root SourceDirection Index Domain Term Operator
        source sourceLeft sourceRight scaleAt volumeAt expReal embedding)
    cutoff index →
  CMP116.sourceEnvelope source
    (scaleAt cutoff)
    (volumeAt cutoff)
    (CMP116.sourceRoot source
      (scaleAt cutoff)
      (volumeAt cutoff)
      (sourceLeft index)
      (sourceRight index))
    (CMP116.sourceDistance source
      (sourceLeft index)
      (sourceRight index))
  ≤ℝ
  sourceAmplitude calibration *ℝ
    expReal
      (-ℝ
        ScaleCal.embedQ embedding
          (Scale.latticeExponent (scaleData calibration)
            * Scale.latticeDistance (scaleData calibration)
                (physicalDistance calibration index)))
selectedSourceEnvelopeBelowLatticeExponential
    {expReal = expReal} {embedding = embedding}
    calibration cutoff index =
  let
    expansion = expansionAt calibration cutoff index

    r415Bound =
      R415.selectedBoundaryBelowSourceDecay expansion

    upperEquality :
      R415.sourceAmplitude expansion *ℝ
        R414.weight
          (R415.decay expansion)
          (R411.selectedConnectingDistance (R415.geometry expansion))
      ≡
      sourceAmplitude calibration *ℝ
        expReal
          (-ℝ
            ScaleCal.embedQ embedding
              (Scale.latticeExponent (scaleData calibration)
                * Scale.latticeDistance (scaleData calibration)
                    (physicalDistance calibration index)))
    upperEquality =
      cong₂ _*ℝ_
        (selectedExpansionAmplitudeIsUniform calibration cutoff index)
        (selectedExpansionDecayIsLatticeExponential
          calibration cutoff index)

    boundaryBelowTarget =
      subst
        (λ upper →
          absℝ (R415.selectedBoundaryIntegrand expansion) ≤ℝ upper)
        upperEquality
        r415Bound
  in
  subst
    (λ lower →
      lower ≤ℝ
        sourceAmplitude calibration *ℝ
          expReal
            (-ℝ
              ScaleCal.embedQ embedding
                (Scale.latticeExponent (scaleData calibration)
                  * Scale.latticeDistance (scaleData calibration)
                      (physicalDistance calibration index))))
    (sym
      (sourceEnvelopeIsSelectedBoundaryMagnitude
        calibration cutoff index))
    boundaryBelowTarget

asLiteralRealCMP116ScaleCalibration :
  ∀ {ScaleCarrier Volume Root SourceDirection Index Domain Term Operator
      source sourceLeft sourceRight scaleAt volumeAt expReal embedding} →
  SelectedR415EnvelopeCalibration
    ScaleCarrier Volume Root SourceDirection Index Domain Term Operator
    source sourceLeft sourceRight scaleAt volumeAt expReal embedding →
  ScaleCal.LiteralRealCMP116ScaleCalibration
    ScaleCarrier Volume Root SourceDirection Index
    source sourceLeft sourceRight scaleAt volumeAt expReal embedding
asLiteralRealCMP116ScaleCalibration calibration = record
  { ScaleCal.LiteralRealCMP116ScaleCalibration.scaleData =
      scaleData calibration
  ; ScaleCal.LiteralRealCMP116ScaleCalibration.physicalDistance =
      physicalDistance calibration
  ; ScaleCal.LiteralRealCMP116ScaleCalibration.physicalDistanceNonnegative =
      physicalDistanceNonnegative calibration
  ; ScaleCal.LiteralRealCMP116ScaleCalibration.sourceAmplitude =
      sourceAmplitude calibration
  ; ScaleCal.LiteralRealCMP116ScaleCalibration.physicalAmplitude =
      physicalAmplitude calibration
  ; ScaleCal.LiteralRealCMP116ScaleCalibration.sourceAmplitudeNonnegative =
      sourceAmplitudeNonnegative calibration
  ; ScaleCal.LiteralRealCMP116ScaleCalibration.sourceAmplitudeBelowPhysicalAmplitude =
      sourceAmplitudeBelowPhysicalAmplitude calibration
  ; ScaleCal.LiteralRealCMP116ScaleCalibration.exponentialOrder =
      exponentialOrder calibration
  ; ScaleCal.LiteralRealCMP116ScaleCalibration.selectedSourceEnvelopeBelowExponential =
      selectedSourceEnvelopeBelowLatticeExponential calibration
  }

round416R415ToBEnvCompilerLevel : ProofLevel
round416R415ToBEnvCompilerLevel = machineChecked

-- B-env is no longer a second free pointwise inequality after R415.
-- The remaining physical work is the literal R415 instantiation represented by
-- the three same-object fields above (boundary, uniform amplitude, decay weight).
round416AdditionalDecayInequalityRequired : Bool
round416AdditionalDecayInequalityRequired = false
