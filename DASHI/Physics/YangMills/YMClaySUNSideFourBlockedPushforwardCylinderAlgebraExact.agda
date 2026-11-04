module DASHI.Physics.YangMills.YMClaySUNSideFourBlockedPushforwardCylinderAlgebraExact where

------------------------------------------------------------------------
-- R445.P04: ACTUAL side-four SUN Wilson--Gibbs fine-source PUSHFORWARD.
--
-- Source: #1444 YMClaySUNSideFourBlockedFineHaarObservableExact.
-- The selected fine measure is the actual original side-four (1024 native
-- bonds) periodic SUN Gibbs density + the SAME chosen one-link product
-- Haar functional. The selected block is the original noncommutative
-- two-link native side-four -> side-two SU(N) holonomy.
--
-- F_* mu(F) = E_mu[F(B(U))] is implemented on this SAME original source:
-- positivity / linearity / partition normalization follow from the
-- original physical cylinder algebra, not from new scalar assumptions.
-- For gauge-invariant original coarse observables, the existing
-- original fine-measure gauge covariance is reused directly.
--
-- This is a genuine weighted finite-source pushforward FUNCTIONAL,
-- NOT a proof of a density relative to the coarse product-Haar, NOT
-- Wilson-action closure and NOT a regular conditional distribution.
-- 4D infinite-volume and continuum limits, RP and mass gap are OPEN.
--
-- Wilson (1974), Bałaban (1985); original DASHI finite sources.
-- Source-written, NOT exact-head Agda checked; RealAnalysisAxioms is
-- a transitive axiom boundary, therefore NO Golden --safe declaration.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; _+ℝ_; _*ℝ_; _≤ℝ_; _<ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as Variable
import DASHI.Physics.YangMills.YMClaySUNSideFourBlockedFineHaarObservableExact as Existing
import DASHI.Physics.YangMills.YMClaySUNConstructedPeriodicGaugeCodecExact as Constructed
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicProductHaarExact as Haar
import DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact as Codec
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Product
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact as Cyl

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (betaFine : ℝ)
    (oneLink : Product.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
    (divide : ℝ → ℝ → ℝ)
  where

  FineLinks : Set
  FineLinks = Variable.SUNPeriodicLinks theory 3

  CoarseLinks : Set
  CoarseLinks = Variable.SUNPeriodicLinks theory 1

  originalFineGibbsMeasure : Physical.PhysicalFiniteYMMeasure FineLinks ℝ
  originalFineGibbsMeasure =
    Existing.selectedFineMeasure theory traceData exponential
      betaFine oneLink bilateral divide

  actualBlockedLinkMap : FineLinks → CoarseLinks
  actualBlockedLinkMap =
    Existing.selectedBlock theory traceData exponential
      betaFine oneLink bilateral divide

  pullbackCoarse :
    (CoarseLinks → ℝ) → FineLinks → ℝ
  pullbackCoarse observable fine =
    observable (actualBlockedLinkMap fine)

  -- The full density (not only the unweighted product Haar) is retained.
  -- No artificial coarse Gibbs density is ever inserted.
  actualPushforwardNumerator :
    (CoarseLinks → ℝ) → ℝ
  actualPushforwardNumerator observable =
    Cyl.unnormalizedNumerator originalFineGibbsMeasure
      (pullbackCoarse observable)

  actualPushforwardPartition : ℝ
  actualPushforwardPartition =
    Physical.partitionFunction originalFineGibbsMeasure

  actualPushforwardNormalized :
    (CoarseLinks → ℝ) → ℝ
  actualPushforwardNormalized observable =
    Physical.normalizedExpectation originalFineGibbsMeasure
      (pullbackCoarse observable)

  -- The actual original Gibbs density, one-link Haar and partition are
  -- exactly those of #1444. This is the same physical finite source.
  actualPushforwardNumeratorIsOriginalWeightedIntegral :
    ∀ observable →
    actualPushforwardNumerator observable
    ≡
    Physical.haarIntegral originalFineGibbsMeasure
      (λ fine →
        Variable.periodicSUNGibbsDensity
          theory traceData exponential 3 betaFine fine
        *ℝ observable (actualBlockedLinkMap fine))
  actualPushforwardNumeratorIsOriginalWeightedIntegral observable =
    refl

  actualPushforwardNormalizedIsOriginalBlockedExpectation :
    ∀ observable →
    actualPushforwardNormalized observable
    ≡
    Physical.normalizedExpectation originalFineGibbsMeasure
      (λ fine → observable (actualBlockedLinkMap fine))
  actualPushforwardNormalizedIsOriginalBlockedExpectation observable =
    refl

  -- The original one-link source algebra + the actual native decoder
  -- supply all physical finite integration premises. We do not assume a
  -- new coarse-source positivity/linearity record.
  originalFineIntegrationLaws :
    (ordered : Ordered.OneLinkOrderedHaarAlgebra oneLink)
    (strictToWeak : ∀ {value} → 0ℝ <ℝ value → 0ℝ ≤ℝ value) →
    Cyl.PhysicalFiniteMeasureIntegrationLaws originalFineGibbsMeasure
  originalFineIntegrationLaws ordered strictToWeak =
    Haar.periodicProductIntegrationLaws
      theory traceData exponential 3 betaFine
      oneLink (Codec.decodeOriginalBonds 4) divide
      ordered strictToWeak

  actualPushforwardNumeratorZero :
    (ordered : Ordered.OneLinkOrderedHaarAlgebra oneLink)
    (strictToWeak : ∀ {value} → 0ℝ <ℝ value → 0ℝ ≤ℝ value) →
    actualPushforwardNumerator (λ _ → 0ℝ) ≡ 0ℝ
  actualPushforwardNumeratorZero ordered strictToWeak =
    Cyl.numeratorZero (originalFineIntegrationLaws ordered strictToWeak)

  actualPushforwardNumeratorOne :
    (ordered : Ordered.OneLinkOrderedHaarAlgebra oneLink)
    (strictToWeak : ∀ {value} → 0ℝ <ℝ value → 0ℝ ≤ℝ value) →
    actualPushforwardNumerator (λ _ → 1ℝ)
      ≡ actualPushforwardPartition
  actualPushforwardNumeratorOne ordered strictToWeak =
    Cyl.numeratorOneIsPartitionFunction
      (originalFineIntegrationLaws ordered strictToWeak)

  actualPushforwardNumeratorAdd :
    (ordered : Ordered.OneLinkOrderedHaarAlgebra oneLink)
    (strictToWeak : ∀ {value} → 0ℝ <ℝ value → 0ℝ ≤ℝ value) →
    ∀ left right →
    actualPushforwardNumerator (λ coarse → left coarse +ℝ right coarse)
    ≡
    actualPushforwardNumerator left +ℝ actualPushforwardNumerator right
  actualPushforwardNumeratorAdd ordered strictToWeak left right =
    Cyl.numeratorAdd
      (originalFineIntegrationLaws ordered strictToWeak)
      (pullbackCoarse left) (pullbackCoarse right)

  actualPushforwardNumeratorScale :
    (ordered : Ordered.OneLinkOrderedHaarAlgebra oneLink)
    (strictToWeak : ∀ {value} → 0ℝ <ℝ value → 0ℝ ≤ℝ value) →
    ∀ scalar observable →
    actualPushforwardNumerator (λ coarse → scalar *ℝ observable coarse)
    ≡
    scalar *ℝ actualPushforwardNumerator observable
  actualPushforwardNumeratorScale ordered strictToWeak scalar observable =
    Cyl.numeratorScale
      (originalFineIntegrationLaws ordered strictToWeak)
      scalar (pullbackCoarse observable)

  actualPushforwardNumeratorPositive :
    (ordered : Ordered.OneLinkOrderedHaarAlgebra oneLink)
    (strictToWeak : ∀ {value} → 0ℝ <ℝ value → 0ℝ ≤ℝ value) →
    ∀ observable →
    (∀ coarse → 0ℝ ≤ℝ observable coarse) →
    0ℝ ≤ℝ actualPushforwardNumerator observable
  actualPushforwardNumeratorPositive
      ordered strictToWeak observable nonnegative =
    Cyl.numeratorPositive
      (originalFineIntegrationLaws ordered strictToWeak)
      (pullbackCoarse observable)
      (λ fine → nonnegative (actualBlockedLinkMap fine))

  -- Normalization uses the strictly positive ACTUAL fine partition
  -- and a legitimate scalar self-division law. No division-by-zero
  -- convention or new "coarse probability" axiom is smuggled in.
  actualFinePartitionPositive :
    Ordered.OneLinkStrictlyPositiveIntegration oneLink →
    0ℝ <ℝ actualPushforwardPartition
  actualFinePartitionPositive strict =
    Constructed.actualPeriodicPartitionPositive
      theory traceData exponential 3 betaFine
      oneLink bilateral divide strict

  actualPushforwardUnitNormalized :
    (ordered : Ordered.OneLinkOrderedHaarAlgebra oneLink)
    (strictToWeak : ∀ {value} → 0ℝ <ℝ value → 0ℝ ≤ℝ value)
    (strict : Ordered.OneLinkStrictlyPositiveIntegration oneLink)
    (positiveSelfDivision :
      ∀ value → 0ℝ <ℝ value → divide value value ≡ 1ℝ) →
    actualPushforwardNormalized (λ _ → 1ℝ) ≡ 1ℝ
  actualPushforwardUnitNormalized
      ordered strictToWeak strict positiveSelfDivision =
    trans
      (cong
        (λ value → divide value actualPushforwardPartition)
        (actualPushforwardNumeratorOne ordered strictToWeak))
      (positiveSelfDivision actualPushforwardPartition
        (actualFinePartitionPositive strict))

  -- #1444 already proved this pointwise gauge invariance for every
  -- original native coarse cylinder observable. This module inherits
  -- it directly, without a second gauge symmetry hypothesis.
  actualPushforwardGaugeInvariant :
    ∀ observable
      (pointwise :
        Existing.CoarsePointwiseObservable
          theory traceData exponential betaFine
          oneLink bilateral divide observable)
      (gamma : Variable.SUNPeriodicGauge theory 3) →
    Physical.normalizedExpectation originalFineGibbsMeasure
      (λ fine →
        observable
          (actualBlockedLinkMap
            (Variable.periodicSUNGaugeTransform
              theory 3 fine gamma)))
    ≡ actualPushforwardNormalized observable
  actualPushforwardGaugeInvariant observable pointwise gamma =
    Existing.originalFineMeasureBlockedGaugeInvariant
      theory traceData exponential betaFine
      oneLink bilateral divide observable pointwise gamma

  -- Gauge invariance for BOTH selected original coarse physical
  -- Wilson action and the literal coarse Gibbs test density.
  actualPushforwardWilsonGaugeInvariant :
    ∀ betaCoarse
      (gamma : Variable.SUNPeriodicGauge theory 3) →
    Physical.normalizedExpectation originalFineGibbsMeasure
      (λ fine →
        Variable.periodicSUNWilsonAction
          theory traceData 1 betaCoarse
          (actualBlockedLinkMap
            (Variable.periodicSUNGaugeTransform
              theory 3 fine gamma)))
    ≡
    actualPushforwardNormalized
      (Variable.periodicSUNWilsonAction
        theory traceData 1 betaCoarse)
  actualPushforwardWilsonGaugeInvariant betaCoarse gamma =
    Existing.originalFineGibbsBlockedWilsonGaugeInvariant
      theory traceData exponential betaFine
      oneLink bilateral divide betaCoarse gamma

  actualPushforwardGibbsGaugeInvariant :
    ∀ betaCoarse
      (gamma : Variable.SUNPeriodicGauge theory 3) →
    Physical.normalizedExpectation originalFineGibbsMeasure
      (λ fine →
        Variable.periodicSUNGibbsDensity
          theory traceData exponential 1 betaCoarse
          (actualBlockedLinkMap
            (Variable.periodicSUNGaugeTransform
              theory 3 fine gamma)))
    ≡
    actualPushforwardNormalized
      (Variable.periodicSUNGibbsDensity
        theory traceData exponential 1 betaCoarse)
  actualPushforwardGibbsGaugeInvariant betaCoarse gamma =
    Existing.originalFineGibbsBlockedGibbsGaugeInvariant
      theory traceData exponential betaFine
      oneLink bilateral divide betaCoarse gamma

-- NO R445 physical pushforward-vs-bare coarse Wilson measure identity:
-- the above provides a positive normalized source cylinder functional,
-- not an identification of its Radon--Nikodym density or a measure kernel.
-- Neither the one-link Haar existence nor UV/IR uniform estimates are paid.
