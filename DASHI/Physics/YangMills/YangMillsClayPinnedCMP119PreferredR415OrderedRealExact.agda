{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119PreferredR415OrderedRealExact where

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; absℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as CMP116
import DASHI.Physics.YangMills.BalabanCMP116PreferredR415SourceExact as Preferred
import DASHI.Physics.YangMills.BalabanCMP116SelectedMarkedExpansionRound415Exact as R415
import DASHI.Physics.YangMills.BalabanCMP116SelectedSupportConnectionRound411Exact as R411
import DASHI.Physics.YangMills.BalabanCMP116ConnectingOuterSumRound414Exact as R414
import DASHI.Physics.YangMills.BalabanPhysicalClusteringScaleAlgebraExact as Scale
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCMP116ScaleCalibrationExact as Calibration
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCMP116MarkedExpansionOrderedUpperExact as Ordered

record PreferredR415OrderedRealCalibration
    (Domain Term Operator ScaleCarrier Volume Root SourceDirection Index : Set)
    (source :
      CMP116.PublishedCMP116DifferentiatedLocalization
        ScaleCarrier Volume Root SourceDirection ℝ)
    (sourceLeft sourceRight : Index → SourceDirection)
    (scaleAt : Nat → ScaleCarrier)
    (volumeAt : Nat → Volume)
    (expReal : ℝ → ℝ)
    (embedding : Embed.OrderedRationalRealEmbedding)
    (preferred : Index → Preferred.PreferredR415Source Domain Term Operator)
    : Set₂ where
  field
    scaleData : Scale.PhysicalScaleData
    physicalDistance : Index → ℚ
    physicalDistanceNonnegative :
      ∀ index → 0ℚ ≤ physicalDistance index

    physicalAmplitude : ℝ
    sourceAmplitudeNonnegative :
      ∀ index → 0ℝ ≤ℝ Preferred.sourceAmplitude (preferred index)
    sourceAmplitudeUniform :
      ∀ index →
      Preferred.sourceAmplitude (preferred index) ≤ℝ physicalAmplitude

    exponentialOrder :
      Calibration.RealNegativeExponentialOrder expReal

    sourceEnvelopeBelowSelectedBoundary :
      ∀ cutoff index →
      CMP116.sourceEnvelope source
        (scaleAt cutoff) (volumeAt cutoff)
        (CMP116.sourceRoot source
          (scaleAt cutoff) (volumeAt cutoff)
          (sourceLeft index) (sourceRight index))
        (CMP116.sourceDistance source
          (sourceLeft index) (sourceRight index))
      ≤ℝ absℝ (Preferred.selectedBoundaryIntegrand (preferred index))

    selectedWeightBelowSourceExponential :
      ∀ index →
      R414.weight
        (Preferred.decay (preferred index))
        (R411.selectedConnectingDistance
          (Preferred.geometry (preferred index)))
      ≤ℝ
      expReal
        (DASHI.Foundations.RealAnalysisAxioms.-ℝ
          Calibration.embedQ embedding
            (Scale.latticeExponent scaleData
              Data.Rational.Base.*
              Scale.latticeDistance scaleData (physicalDistance index)))

open PreferredR415OrderedRealCalibration public

compiledExpansion :
  ∀ {Domain Term Operator ScaleCarrier Volume Root SourceDirection Index
      source sourceLeft sourceRight scaleAt volumeAt expReal embedding preferred} →
  PreferredR415OrderedRealCalibration
    Domain Term Operator ScaleCarrier Volume Root SourceDirection Index
    source sourceLeft sourceRight scaleAt volumeAt expReal embedding preferred →
  Index → R415.SelectedCMP116MarkedExpansion Domain Term Operator
compiledExpansion {preferred = preferred} calibration index =
  Preferred.compilePreferredR415 (preferred index)

asOrderedInputs :
  ∀ {Domain Term Operator ScaleCarrier Volume Root SourceDirection Index
      source sourceLeft sourceRight scaleAt volumeAt expReal embedding preferred}
    (calibration :
      PreferredR415OrderedRealCalibration
        Domain Term Operator ScaleCarrier Volume Root SourceDirection Index
        source sourceLeft sourceRight scaleAt volumeAt expReal embedding preferred) →
  Ordered.R415OrderedRealScaleInputs
    Domain Term Operator ScaleCarrier Volume Root SourceDirection Index
    source sourceLeft sourceRight scaleAt volumeAt expReal embedding
    (compiledExpansion calibration)
asOrderedInputs calibration = record
  { Ordered.R415OrderedRealScaleInputs.scaleData = scaleData calibration
  ; Ordered.R415OrderedRealScaleInputs.physicalDistance =
      physicalDistance calibration
  ; Ordered.R415OrderedRealScaleInputs.physicalDistanceNonnegative =
      physicalDistanceNonnegative calibration
  ; Ordered.R415OrderedRealScaleInputs.physicalAmplitude =
      physicalAmplitude calibration
  ; Ordered.R415OrderedRealScaleInputs.sourceAmplitudeNonnegative =
      sourceAmplitudeNonnegative calibration
  ; Ordered.R415OrderedRealScaleInputs.sourceAmplitudeUniform =
      sourceAmplitudeUniform calibration
  ; Ordered.R415OrderedRealScaleInputs.exponentialOrder =
      exponentialOrder calibration
  ; Ordered.R415OrderedRealScaleInputs.sourceEnvelopeBelowSelectedBoundary =
      sourceEnvelopeBelowSelectedBoundary calibration
  ; Ordered.R415OrderedRealScaleInputs.selectedWeightBelowSourceExponential =
      selectedWeightBelowSourceExponential calibration
  }

preferredR415OrderedPhysicalUpper :
  ∀ {Domain Term Operator ScaleCarrier Volume Root SourceDirection Index
      source sourceLeft sourceRight scaleAt volumeAt expReal embedding preferred}
    (calibration :
      PreferredR415OrderedRealCalibration
        Domain Term Operator ScaleCarrier Volume Root SourceDirection Index
        source sourceLeft sourceRight scaleAt volumeAt expReal embedding preferred) →
  ∀ cutoff index →
  CMP116.sourceEnvelope source
    (scaleAt cutoff) (volumeAt cutoff)
    (CMP116.sourceRoot source
      (scaleAt cutoff) (volumeAt cutoff)
      (sourceLeft index) (sourceRight index))
    (CMP116.sourceDistance source
      (sourceLeft index) (sourceRight index))
  ≤ℝ Ordered.physicalExponentialUpper (asOrderedInputs calibration) index
preferredR415OrderedPhysicalUpper calibration =
  Ordered.sourceEnvelopeBelowOrderedPhysicalExponential
    (asOrderedInputs calibration)

preferredR415OrderedRealCompilerLevel : ProofLevel
preferredR415OrderedRealCompilerLevel = machineChecked

literalPreferredR415OrderedRealAttachmentLevel : ProofLevel
literalPreferredR415OrderedRealAttachmentLevel = conditional
