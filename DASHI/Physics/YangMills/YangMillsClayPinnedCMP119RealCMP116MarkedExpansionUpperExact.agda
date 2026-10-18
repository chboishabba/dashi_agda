{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCMP116MarkedExpansionUpperExact where

------------------------------------------------------------------------
-- B / ONE-SIDED R415 -> REAL CMP116 SOURCE ATTACHMENT
--
-- Equality between sourceEnvelope and the selected R415 boundary is stronger
-- than the downstream clustering consumer needs.  It suffices to prove
--
--   sourceEnvelope <= |selectedBoundary|.
--
-- R415 then supplies the boundary decay and the existing physical-scale
-- calibration transports it to the real exponential upper.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_; _*_)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; absℝ; _≤ℝ_; _*ℝ_; -ℝ_; ≤ℝ-trans)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as CMP116
import DASHI.Physics.YangMills.BalabanCMP116SelectedMarkedExpansionRound415Exact as R415
import DASHI.Physics.YangMills.BalabanCMP116SelectedSupportConnectionRound411Exact as R411
import DASHI.Physics.YangMills.BalabanCMP116ConnectingOuterSumRound414Exact as R414
import DASHI.Physics.YangMills.BalabanPhysicalClusteringScaleAlgebraExact as Scale
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCMP116ScaleCalibrationExact as Calibration

record R415OneSidedRealScaleInputs
    (Domain Term Operator ScaleCarrier Volume Root SourceDirection Index : Set)
    (source :
      CMP116.PublishedCMP116DifferentiatedLocalization
        ScaleCarrier Volume Root SourceDirection ℝ)
    (sourceLeft sourceRight : Index → SourceDirection)
    (scaleAt : Nat → ScaleCarrier)
    (volumeAt : Nat → Volume)
    (expReal : ℝ → ℝ)
    (embedding : Embed.OrderedRationalRealEmbedding)
    (expansion : Index → R415.SelectedCMP116MarkedExpansion Domain Term Operator)
    : Set₂ where
  field
    scaleData : Scale.PhysicalScaleData
    physicalDistance : Index → ℚ
    physicalDistanceNonnegative :
      ∀ index → 0ℚ ≤ physicalDistance index

    physicalAmplitude : ℝ
    sourceAmplitudeNonnegative :
      ∀ index → 0ℝ ≤ℝ R415.sourceAmplitude (expansion index)
    sourceAmplitudeUniform :
      ∀ index →
      R415.sourceAmplitude (expansion index) ≤ℝ physicalAmplitude

    exponentialOrder :
      Calibration.RealNegativeExponentialOrder expReal

    sourceEnvelopeBelowSelectedBoundary :
      ∀ cutoff index →
      CMP116.sourceEnvelope source
        (scaleAt cutoff)
        (volumeAt cutoff)
        (CMP116.sourceRoot source
          (scaleAt cutoff) (volumeAt cutoff)
          (sourceLeft index) (sourceRight index))
        (CMP116.sourceDistance source
          (sourceLeft index) (sourceRight index))
      ≤ℝ
      absℝ (R415.selectedBoundaryIntegrand (expansion index))

    selectedWeightIsSourceExponential :
      ∀ index →
      R414.weight (R415.decay (expansion index))
        (R411.selectedConnectingDistance
          (R415.geometry (expansion index)))
      ≡
      expReal
        (-ℝ
          Calibration.embedQ embedding
            (Scale.latticeExponent scaleData
              * Scale.latticeDistance scaleData
                  (physicalDistance index)))

open R415OneSidedRealScaleInputs public

sourceEnvelopeBelowLatticeExponential :
  ∀ {Domain Term Operator ScaleCarrier Volume Root SourceDirection Index
      source sourceLeft sourceRight scaleAt volumeAt expReal embedding expansion}
    (inputs :
      R415OneSidedRealScaleInputs
        Domain Term Operator ScaleCarrier Volume Root SourceDirection Index
        source sourceLeft sourceRight scaleAt volumeAt expReal embedding expansion)
    cutoff index →
  CMP116.sourceEnvelope source
    (scaleAt cutoff)
    (volumeAt cutoff)
    (CMP116.sourceRoot source
      (scaleAt cutoff) (volumeAt cutoff)
      (sourceLeft index) (sourceRight index))
    (CMP116.sourceDistance source
      (sourceLeft index) (sourceRight index))
  ≤ℝ
  R415.sourceAmplitude (expansion index) *ℝ
    expReal
      (-ℝ
        Calibration.embedQ embedding
          (Scale.latticeExponent (scaleData inputs)
            * Scale.latticeDistance (scaleData inputs)
                (physicalDistance inputs index)))
sourceEnvelopeBelowLatticeExponential
    {embedding = embedding} {expansion = expansion} inputs cutoff index =
  ≤ℝ-trans
    (sourceEnvelopeBelowSelectedBoundary inputs cutoff index)
    (substUpper
      (selectedWeightIsSourceExponential inputs index)
      (R415.selectedBoundaryBelowSourceDecay (expansion index)))
  where
  substUpper :
    ∀ {left weightValue exponential : ℝ} →
    weightValue ≡ exponential →
    left ≤ℝ R415.sourceAmplitude (expansion index) *ℝ weightValue →
    left ≤ℝ R415.sourceAmplitude (expansion index) *ℝ exponential
  substUpper refl proof = proof

physicalExponentialUpper :
  ∀ {Domain Term Operator ScaleCarrier Volume Root SourceDirection Index
      source sourceLeft sourceRight scaleAt volumeAt expReal embedding expansion} →
  R415OneSidedRealScaleInputs
    Domain Term Operator ScaleCarrier Volume Root SourceDirection Index
    source sourceLeft sourceRight scaleAt volumeAt expReal embedding expansion →
  Index → ℝ
physicalExponentialUpper {expReal = expReal} {embedding = embedding} inputs index =
  physicalAmplitude inputs *ℝ
    expReal
      (-ℝ
        Calibration.embedQ embedding
          (Scale.physicalMass (scaleData inputs)
            * physicalDistance inputs index))

sourceEnvelopeBelowPhysicalExponential :
  ∀ {Domain Term Operator ScaleCarrier Volume Root SourceDirection Index
      source sourceLeft sourceRight scaleAt volumeAt expReal embedding expansion}
    (inputs :
      R415OneSidedRealScaleInputs
        Domain Term Operator ScaleCarrier Volume Root SourceDirection Index
        source sourceLeft sourceRight scaleAt volumeAt expReal embedding expansion)
    cutoff index →
  CMP116.sourceEnvelope source
    (scaleAt cutoff)
    (volumeAt cutoff)
    (CMP116.sourceRoot source
      (scaleAt cutoff) (volumeAt cutoff)
      (sourceLeft index) (sourceRight index))
    (CMP116.sourceDistance source
      (sourceLeft index) (sourceRight index))
  ≤ℝ physicalExponentialUpper inputs index
sourceEnvelopeBelowPhysicalExponential
    {expReal = expReal} {embedding = embedding} {expansion = expansion}
    inputs cutoff index =
  let
    order = exponentialOrder inputs
    d = physicalDistance inputs index

    exponentOrder =
      Calibration.embeddedPhysicalExponentBelowLatticeExponent
        embedding (scaleData inputs) d
        (physicalDistanceNonnegative inputs index)

    decayOrder =
      Calibration.negativeExpAntitone order exponentOrder

    sourceAmplitudeDecayOrder =
      Calibration.leftScaleNonnegative order
        (sourceAmplitudeNonnegative inputs index)
        decayOrder

    amplitudeOrder =
      Calibration.rightScaleNonnegative order
        (Calibration.expNonnegative order
          (-ℝ
            Calibration.embedQ embedding
              (Scale.physicalMass (scaleData inputs) * d)))
        (sourceAmplitudeUniform inputs index)
  in
  Calibration.transitive order
    (sourceEnvelopeBelowLatticeExponential inputs cutoff index)
    (Calibration.transitive order sourceAmplitudeDecayOrder amplitudeOrder)

r415OneSidedSourceAttachmentCompilerLevel : ProofLevel
r415OneSidedSourceAttachmentCompilerLevel = machineChecked

r415OneSidedPhysicalScaleCompilerLevel : ProofLevel
r415OneSidedPhysicalScaleCompilerLevel = machineChecked

literalR415OneSidedSourceAttachmentLevel : ProofLevel
literalR415OneSidedSourceAttachmentLevel = conditional
