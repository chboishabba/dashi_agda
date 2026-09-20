{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCMP116ScaleCalibrationExact where

------------------------------------------------------------------------
-- LITERAL REAL CMP116 L5: SOURCE EXPONENTIAL -> PHYSICAL EUCLIDEAN RATE
--
-- This removes the opaque pointwise L5 payment
--
--   sourceEnvelope <= desiredPhysicalUpper
--
-- from the preferred real CMP119/CMP116 route.
--
-- The physical exponent comparison is compiler-owned: reuse the existing
-- machine-checked rational spacing theorem
--
--   m d_phys <= mu d_latt
--
-- and transport it through the ordered Q -> R embedding.  Standard real
-- exponential antitonicity then gives
--
--   exp (- mu d_latt) <= exp (- m d_phys).
--
-- What remains genuinely source/physics specific is only:
--   * the selected CMP116 envelope really has the declared exponential form;
--   * its selected source/tree coordinate is the physical lattice distance;
--   * its amplitude is uniformly controlled.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _≤ℝ_; _*ℝ_; -ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanPhysicalClusteringScaleAlgebraExact as Scale
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as Ring
import DASHI.Physics.YangMills.BalabanA2RationalSensitivityToRealContractionRound104Exact as Add
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed

import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as A
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCovarianceExact as Cov
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealTwoJSourceExact as TwoJ
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCMP116ApplicationExact as App
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCMP116ClusteringExact as Cluster
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCMP116PhysicalUpperExact as Upper
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as CMP116
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

embedQ : Ring.RationalRealRingEmbedding → ℚ → ℝ
embedQ embedding =
  Embed.embed (Add.base (Ring.additive embedding))

------------------------------------------------------------------------
-- Standard ordered-real exponential authority.
------------------------------------------------------------------------

record RealNegativeExponentialOrder
    (expReal : ℝ → ℝ) : Set₁ where
  field
    transitive :
      ∀ {a b c} → a ≤ℝ b → b ≤ℝ c → a ≤ℝ c

    expNonnegative :
      ∀ x → 0ℝ ≤ℝ expReal x

    negativeExpAntitone :
      ∀ {x y} →
      x ≤ℝ y →
      expReal (-ℝ y) ≤ℝ expReal (-ℝ x)

    leftScaleNonnegative :
      ∀ {a b factor} →
      0ℝ ≤ℝ factor →
      a ≤ℝ b →
      factor *ℝ a ≤ℝ factor *ℝ b

    rightScaleNonnegative :
      ∀ {a b factor} →
      0ℝ ≤ℝ factor →
      a ≤ℝ b →
      a *ℝ factor ≤ℝ b *ℝ factor

open RealNegativeExponentialOrder public

------------------------------------------------------------------------
-- The existing physical scale theorem transported into the literal real
-- scalar carrier.  No new YM estimate occurs here.
------------------------------------------------------------------------

embeddedPhysicalExponentBelowLatticeExponent :
  (embedding : Ring.RationalRealRingEmbedding) →
  (scales : Scale.PhysicalScaleData) →
  (physicalDistance : ℚ) →
  0ℚ ≤ physicalDistance →
  embedQ embedding
    (Scale.physicalMass scales * physicalDistance)
  ≤ℝ
  embedQ embedding
    (Scale.latticeExponent scales
      * Scale.latticeDistance scales physicalDistance)
embeddedPhysicalExponentBelowLatticeExponent
    embedding scales physicalDistance distanceNN =
  Embed.orderPreserving
    (Add.base (Ring.additive embedding))
    (Scale.physicalExponentDominatedByLatticeExponent
      scales physicalDistance distanceNN)

------------------------------------------------------------------------
-- Structural L5 data.
--
-- Unlike the old field, this record never asks for the final target inequality.
-- It asks for the source envelope's actual exponential presentation and the
-- amplitude control.  Physical rate conversion is then proved below.
------------------------------------------------------------------------

record LiteralRealCMP116ScaleCalibration
    (ScaleCarrier Volume Root SourceDirection Index : Set)
    (source :
      CMP116.PublishedCMP116DifferentiatedLocalization
        ScaleCarrier Volume Root SourceDirection ℝ)
    (sourceLeft sourceRight : Index → SourceDirection)
    (scaleAt : Nat → ScaleCarrier)
    (volumeAt : Nat → Volume)
    (expReal : ℝ → ℝ)
    (embedding : Ring.RationalRealRingEmbedding) : Set₂ where
  field
    scaleData : Scale.PhysicalScaleData

    physicalDistance : Index → ℚ
    physicalDistanceNonnegative :
      ∀ index → 0ℚ ≤ physicalDistance index

    sourceAmplitude physicalAmplitude : ℝ
    sourceAmplitudeNonnegative : 0ℝ ≤ℝ sourceAmplitude
    sourceAmplitudeBelowPhysicalAmplitude :
      sourceAmplitude ≤ℝ physicalAmplitude

    exponentialOrder : RealNegativeExponentialOrder expReal

    -- Actual source-specific L5 leaf: selected CMP116 envelope and selected
    -- source/tree geometry have the concrete exponential presentation governed
    -- by the SAME lattice exponent and physical spacing data.
    selectedSourceEnvelopeExponential :
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
      sourceAmplitude *ℝ
        expReal
          (-ℝ
            embedQ embedding
              (Scale.latticeExponent scaleData
                * Scale.latticeDistance scaleData
                    (physicalDistance index)))

open LiteralRealCMP116ScaleCalibration public

physicalExponentialUpper :
  ∀ {ScaleCarrier Volume Root SourceDirection Index source
      sourceLeft sourceRight scaleAt volumeAt expReal embedding} →
  LiteralRealCMP116ScaleCalibration
    ScaleCarrier Volume Root SourceDirection Index
    source sourceLeft sourceRight scaleAt volumeAt expReal embedding →
  Index → ℝ
physicalExponentialUpper calibration index =
  physicalAmplitude calibration *ℝ
    expReal
      (-ℝ
        embedQ _
          (Scale.physicalMass (scaleData calibration)
            * physicalDistance calibration index))

sourceEnvelopeBelowPhysicalExponentialUpper :
  ∀ {ScaleCarrier Volume Root SourceDirection Index source
      sourceLeft sourceRight scaleAt volumeAt expReal embedding}
    (calibration :
      LiteralRealCMP116ScaleCalibration
        ScaleCarrier Volume Root SourceDirection Index
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
  physicalExponentialUpper calibration index
sourceEnvelopeBelowPhysicalExponentialUpper
    {embedding = embedding} calibration cutoff index =
  let
    order = exponentialOrder calibration
    d = physicalDistance calibration index

    exponentOrder :
      embedQ embedding
        (Scale.physicalMass (scaleData calibration) * d)
      ≤ℝ
      embedQ embedding
        (Scale.latticeExponent (scaleData calibration)
          * Scale.latticeDistance (scaleData calibration) d)
    exponentOrder =
      embeddedPhysicalExponentBelowLatticeExponent
        embedding
        (scaleData calibration)
        d
        (physicalDistanceNonnegative calibration index)

    decayOrder =
      negativeExpAntitone order exponentOrder

    sourceAmplitudeDecayOrder :
      sourceAmplitude calibration *ℝ
        expReal
          (-ℝ
            embedQ embedding
              (Scale.latticeExponent (scaleData calibration)
                * Scale.latticeDistance (scaleData calibration) d))
      ≤ℝ
      sourceAmplitude calibration *ℝ
        expReal
          (-ℝ
            embedQ embedding
              (Scale.physicalMass (scaleData calibration) * d))
    sourceAmplitudeDecayOrder =
      leftScaleNonnegative order
        (sourceAmplitudeNonnegative calibration)
        decayOrder

    amplitudeOrder :
      sourceAmplitude calibration *ℝ
        expReal
          (-ℝ
            embedQ embedding
              (Scale.physicalMass (scaleData calibration) * d))
      ≤ℝ
      physicalAmplitude calibration *ℝ
        expReal
          (-ℝ
            embedQ embedding
              (Scale.physicalMass (scaleData calibration) * d))
    amplitudeOrder =
      rightScaleNonnegative order
        (expNonnegative order
          (-ℝ
            embedQ embedding
              (Scale.physicalMass (scaleData calibration) * d)))
        (sourceAmplitudeBelowPhysicalAmplitude calibration)

    composed =
      transitive order sourceAmplitudeDecayOrder amplitudeOrder
  in
  subst
    (λ lower →
      lower ≤ℝ physicalExponentialUpper calibration index)
    (sym (selectedSourceEnvelopeExponential
      calibration cutoff index))
    composed

------------------------------------------------------------------------
-- Preferred pinned-real adapter.
--
-- This converts the structural calibration above into the existing real
-- CMP119/CMP116 continuum-upper compiler.  Hence downstream B sees no arbitrary
-- pointwise L5 field.
------------------------------------------------------------------------

asPhysicalUpperInputs :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      ScaleCarrier Volume Root SourceDirection Index
      sequenceLimit limitLaws quotient division S
      a covarianceLaws group twoJ source application expReal embedding}
    (calibration :
      LiteralRealCMP116ScaleCalibration
        ScaleCarrier Volume Root SourceDirection Index
        source
        (λ index →
          Cumulant.sourceDirectionOf
            (TwoJ.meaning twoJ)
            (App.left application index))
        (λ index →
          Cumulant.sourceDirectionOf
            (TwoJ.meaning twoJ)
            (App.right application index))
        (App.scaleAt application)
        (App.volumeAt application)
        expReal embedding)
    (orderLimit : Cluster.RealUpperClosedLimit sequenceLimit) →
  Upper.LiteralRealCMP116PhysicalUpperInputs
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
    ScaleCarrier Volume Root SourceDirection Index
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws} {quotient = quotient} {division = division}
    {S = S} a covarianceLaws group twoJ source application
asPhysicalUpperInputs calibration orderLimit = record
  { Upper.LiteralRealCMP116PhysicalUpperInputs.physicalUpper =
      physicalExponentialUpper calibration
  ; Upper.LiteralRealCMP116PhysicalUpperInputs.sourceEnvelopeBelowPhysicalUpper =
      sourceEnvelopeBelowPhysicalExponentialUpper calibration
  ; Upper.LiteralRealCMP116PhysicalUpperInputs.orderLimit =
      orderLimit
  }

literalRealCMP116PhysicalScaleTransportLevel : ProofLevel
literalRealCMP116PhysicalScaleTransportLevel = machineChecked

literalRealCMP116EnvelopeToPhysicalUpperCompilerLevel : ProofLevel
literalRealCMP116EnvelopeToPhysicalUpperCompilerLevel = machineChecked

-- Standard analysis only: order closure and exp(-x) antitonicity/nonnegativity.
realNegativeExponentialOrderLevel : ProofLevel
realNegativeExponentialOrderLevel = standardImported

-- Remaining literal L5 research leaf after this compiler:
-- identify the selected CMP116 source/tree envelope with the concrete
-- sourceAmplitude * exp(-mu * d_lattice) presentation uniformly in cutoff.
literalCMP116SelectedEnvelopeExponentialIdentificationLevel : ProofLevel
literalCMP116SelectedEnvelopeExponentialIdentificationLevel = conditional
