{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119PreferredR415ToRealExact where

------------------------------------------------------------------------
-- B / PREFERRED R415 SOURCE -> REAL PHYSICAL-SCALE CALIBRATION
--
-- All term enumeration, R410 bounds, fixed-Y charging and outer summation live
-- inside PreferredR415Source (and can be produced by Round418).  This adapter
-- retains only the final source/physical-coordinate attachments needed by the
-- real CMP119 clustering lane.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_; _*_)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; absℝ; _≤ℝ_; _*ℝ_; -ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as CMP116
import DASHI.Physics.YangMills.BalabanCMP116PreferredR415SourceExact as Preferred
import DASHI.Physics.YangMills.BalabanCMP116SelectedMarkedExpansionRound415Exact as R415
import DASHI.Physics.YangMills.BalabanCMP116SelectedSupportConnectionRound411Exact as R411
import DASHI.Physics.YangMills.BalabanCMP116ConnectingOuterSumRound414Exact as R414
import DASHI.Physics.YangMills.BalabanPhysicalClusteringScaleAlgebraExact as Scale
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCMP116ScaleCalibrationExact as Calibration
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCMP116MarkedExpansionUpperExact as Upper

record PreferredR415RealCalibration
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
      ∀ index →
      0ℝ ≤ℝ
        Preferred.sourceAmplitude (preferred index)

    sourceAmplitudeUniform :
      ∀ index →
      Preferred.sourceAmplitude (preferred index)
      ≤ℝ physicalAmplitude

    exponentialOrder :
      Calibration.RealNegativeExponentialOrder expReal

    -- Only one-sided source attachment is needed.
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
      absℝ
        (Preferred.selectedBoundaryIntegrand (preferred index))

    -- Final metric/rate same-object identification.
    selectedWeightIsSourceExponential :
      ∀ index →
      R414.weight
        (Preferred.decay (preferred index))
        (R411.selectedConnectingDistance
          (Preferred.geometry (preferred index)))
      ≡
      expReal
        (-ℝ
          Calibration.embedQ embedding
            (Scale.latticeExponent scaleData
              * Scale.latticeDistance scaleData
                  (physicalDistance index)))

open PreferredR415RealCalibration public

compiledExpansion :
  ∀ {Domain Term Operator ScaleCarrier Volume Root SourceDirection Index
      source sourceLeft sourceRight scaleAt volumeAt expReal embedding preferred} →
  PreferredR415RealCalibration
    Domain Term Operator ScaleCarrier Volume Root SourceDirection Index
    source sourceLeft sourceRight scaleAt volumeAt expReal embedding preferred →
  Index → R415.SelectedCMP116MarkedExpansion Domain Term Operator
compiledExpansion {preferred = preferred} calibration index =
  Preferred.compilePreferredR415 (preferred index)

asOneSidedRealScaleInputs :
  ∀ {Domain Term Operator ScaleCarrier Volume Root SourceDirection Index
      source sourceLeft sourceRight scaleAt volumeAt expReal embedding preferred}
    (calibration :
      PreferredR415RealCalibration
        Domain Term Operator ScaleCarrier Volume Root SourceDirection Index
        source sourceLeft sourceRight scaleAt volumeAt expReal embedding preferred) →
  Upper.R415OneSidedRealScaleInputs
    Domain Term Operator ScaleCarrier Volume Root SourceDirection Index
    source sourceLeft sourceRight scaleAt volumeAt expReal embedding
    (compiledExpansion calibration)
asOneSidedRealScaleInputs calibration = record
  { Upper.R415OneSidedRealScaleInputs.scaleData =
      scaleData calibration
  ; Upper.R415OneSidedRealScaleInputs.physicalDistance =
      physicalDistance calibration
  ; Upper.R415OneSidedRealScaleInputs.physicalDistanceNonnegative =
      physicalDistanceNonnegative calibration
  ; Upper.R415OneSidedRealScaleInputs.physicalAmplitude =
      physicalAmplitude calibration
  ; Upper.R415OneSidedRealScaleInputs.sourceAmplitudeNonnegative =
      sourceAmplitudeNonnegative calibration
  ; Upper.R415OneSidedRealScaleInputs.sourceAmplitudeUniform =
      sourceAmplitudeUniform calibration
  ; Upper.R415OneSidedRealScaleInputs.exponentialOrder =
      exponentialOrder calibration
  ; Upper.R415OneSidedRealScaleInputs.sourceEnvelopeBelowSelectedBoundary =
      sourceEnvelopeBelowSelectedBoundary calibration
  ; Upper.R415OneSidedRealScaleInputs.selectedWeightIsSourceExponential =
      selectedWeightIsSourceExponential calibration
  }

sourceEnvelopeBelowPhysicalExponential :
  ∀ {Domain Term Operator ScaleCarrier Volume Root SourceDirection Index
      source sourceLeft sourceRight scaleAt volumeAt expReal embedding preferred}
    (calibration :
      PreferredR415RealCalibration
        Domain Term Operator ScaleCarrier Volume Root SourceDirection Index
        source sourceLeft sourceRight scaleAt volumeAt expReal embedding preferred) →
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
  Upper.physicalExponentialUpper
    (asOneSidedRealScaleInputs calibration) index
sourceEnvelopeBelowPhysicalExponential calibration =
  Upper.sourceEnvelopeBelowPhysicalExponential
    (asOneSidedRealScaleInputs calibration)

preferredR415ToRealScaleCompilerLevel : ProofLevel
preferredR415ToRealScaleCompilerLevel = machineChecked

-- After Round418/PreferredR415 is inhabited, B's remaining real-scale payment is
-- only sourceEnvelope<=selectedBoundary plus physical distance/rate/amplitude
-- identification.
literalPreferredR415RealAttachmentLevel : ProofLevel
literalPreferredR415RealAttachmentLevel = conditional
