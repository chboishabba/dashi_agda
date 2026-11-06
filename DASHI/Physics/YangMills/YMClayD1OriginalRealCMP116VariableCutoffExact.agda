module DASHI.Physics.YangMills.YMClayD1OriginalRealCMP116VariableCutoffExact where

------------------------------------------------------------------------
-- D1 / the exact selected ORIGINAL REAL CMP116 application for the
-- genuine changing-carrier four-dimensional Wilson SU(N) Gibbs family.
--
-- The source's theorem is imported on its own selected analytic domain.
-- The selected source magnitude is identified with the true, native,
-- cutoff-dependent covariance, not with an independent rational carrier.
--
-- A proof of the source's physical applicability and the uniform envelope
-- must be supplied from original CMP119/122/R445/CMP116 analytic estimates.
-- The result is a uniform REAL upper bound on actual native Wilson tests;
-- it is a conditional application, not a proof of that physical estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst)
open import DASHI.Foundations.RealAnalysisAxioms
  using (ℝ; absℝ; _≤ℝ_; ≤ℝ-trans)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayOriginalVariableWilsonCovarianceSourceExact as Wilson
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as CMP116

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : Nat → ℝ)
    (oneLink : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
    (divide : ℝ → ℝ → ℝ)
  where

  record OriginalRealCMP116PhysicalSelection
      (PhysicalTest Scale Volume Root SourceDirection : Set)
      (source : CMP116.PublishedCMP116DifferentiatedLocalization
        Scale Volume Root SourceDirection ℝ)
      : Set₁ where
    field
      -- PhysicalTest is a continuum-labelled gauge-invariant local
      -- family, with a realization on each actual original lattice.
      originalTest :
        (n : Nat) → PhysicalTest →
        Wilson.Test theory traceData exponential beta oneLink
          bilateral divide n

      originalGaugeInvariant :
        ∀ n test →
        Wilson.originalGaugeInvariant
          theory traceData exponential beta oneLink bilateral divide
          n (originalTest n test)

      scaleAt : Nat → Scale
      volumeAt : Nat → Volume
      direction : PhysicalTest → SourceDirection

      -- On the physical source's common analytic polydisc; this is
      -- NOT supplied by a merely formal mixed-log jet equality.
      pairAdmissible :
        ∀ n left right →
        CMP116.AdmissibleSourcePair source
          (scaleAt n) (volumeAt n)
          (direction left) (direction right)

      -- The one critical source identity on the SAME actual SU(N)
      -- original real Gibbs expectation at cutoff n.
      differentiatedSourceIsOriginalRealCovariance :
        ∀ n left right →
        CMP116.differentiatedMagnitude source
          (scaleAt n) (volumeAt n)
          (direction left) (direction right)
        ≡
        absℝ
          (Wilson.originalWilsonConnectedCovariance
            theory traceData exponential beta oneLink bilateral divide
            n (originalTest n left) (originalTest n right))

      -- Genuine physical geometry and nonperturbative uniform
      -- localization. The envelope is independent of n and volume;
      -- this field is one of the remaining HARD analytic estimates.
      physicalUpper : PhysicalTest → PhysicalTest → ℝ

      uniformSourceEnvelope :
        ∀ n left right →
        CMP116.sourceEnvelope source
          (scaleAt n) (volumeAt n)
          (CMP116.sourceRoot source
            (scaleAt n) (volumeAt n)
            (direction left) (direction right))
          (CMP116.sourceDistance source
            (direction left) (direction right))
        ≤ℝ physicalUpper left right

      sourceOrderIsRealOrder :
        ∀ lower upper →
        CMP116.LessEqual source lower upper →
        lower ≤ℝ upper

  open OriginalRealCMP116PhysicalSelection public

  -- Actual original Yang--Mills covariance localization. The constant
  -- does not depend on n, unlike bounds on arbitrary fixed lattice
  -- spacings. Physical exponential-rate calibration remains in
  -- uniformSourceEnvelope.
  originalWilsonRealCovarianceUniformBound :
    ∀ {PhysicalTest Scale Volume Root SourceDirection}
      {source : CMP116.PublishedCMP116DifferentiatedLocalization
        Scale Volume Root SourceDirection ℝ}
      (selected : OriginalRealCMP116PhysicalSelection
        PhysicalTest Scale Volume Root SourceDirection source) →
    ∀ n left right →
    absℝ
      (Wilson.originalWilsonConnectedCovariance
        theory traceData exponential beta oneLink bilateral divide
        n (originalTest selected n left) (originalTest selected n right))
    ≤ℝ physicalUpper selected left right
  originalWilsonRealCovarianceUniformBound {source = source}
      selected n left right =
    subst
      (λ lower → lower ≤ℝ physicalUpper selected left right)
      (differentiatedSourceIsOriginalRealCovariance selected n left right)
      (≤ℝ-trans
        (sourceOrderIsRealOrder selected _ _
          (CMP116.sourceDifferentiatedLocalization source
            (scaleAt selected n) (volumeAt selected n)
            (direction selected left) (direction selected right)
            (pairAdmissible selected n left right)))
        (uniformSourceEnvelope selected n left right))
