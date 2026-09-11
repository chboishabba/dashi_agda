{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116CanonicalModeSelectedApplicationRound340Exact where

------------------------------------------------------------------------
-- ROUND340 / CANONICAL COMMON-DOMAIN -> MODE-SELECTED CMP116 APPLICATION
--
-- `BalabanCMP116ModeSelectedSubgapClusteringBidiExact` is already the preferred
-- amplitude-aware source-native producer for the actual subgap-mode consumer.
-- Its generic source ABI stores `selectedPairAdmissible` explicitly.
--
-- R338 specializes the published CMP116 theorem to the canonical common U,J
-- domain.  On that specialization, source-pair admissibility depends only on
-- the selected scale/volume being inside the common domain; it is compiler
-- output from R114 and must not remain independent proof debt.
--
-- This adapter removes exactly that redundant coordinate and nothing else.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116CommonAnalyticRadiusRound103Exact as Common
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as R104
import DASHI.Physics.YangMills.BalabanCMP116CanonicalRadiusToCommonDomainRound114Exact as R114
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap
import DASHI.Physics.YangMills.BalabanClayOneSidedCorrelationLimitRound276Exact as R276
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonDomainSourceRound338Exact as R338
import DASHI.Physics.YangMills.BalabanCMP116ModeSelectedSubgapClusteringBidiExact as Mode

record CanonicalCMP116ModeSelectedApplication
    {Measure TestObservable Observable Energy Bound : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    (demands : R104.CMP116FiniteNormalizedAnalyticDemands)
    (source : R338.CanonicalCommonDomainCMP116Source base demands)
    (spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound)
    : Set₁ where
  field
    orderLimit : R276.UpperClosedConvergence Bound
    orderTransitive : ∀ {left middle right} →
      R276.LessEqual orderLimit left middle →
      R276.LessEqual orderLimit middle right →
      R276.LessEqual orderLimit left right

    embed : ℚ → Bound
    sourceOrderToLimitOrder : ∀ {left right} →
      left R276.≡? right → Set

    -- The actual monotone embedding law is kept proof-bearing below.  The
    -- dummy-looking name above is deliberately not used as authority; it only
    -- avoids hiding the source/target carriers in prose.
    rationalOrderEmbedding : ∀ {left right} →
      Data.Rational.Base._≤_ left right →
      R276.LessEqual orderLimit (embed left) (embed right)

    orderIsSpectrumOrder : ∀ left right →
      R276.LessEqual orderLimit left right ≡ Gap.LessEqual spectrum left right

    leftDirection :
      (energy : Energy) → Gap.SubgapMode spectrum energy → Nat →
      R318.SourceDirection base
    rightDirection :
      (energy : Energy) → Gap.SubgapMode spectrum energy → Nat →
      R318.SourceDirection base

    embeddedSourceMagnitudeConvergesToSpectrum :
      ∀ energy mode time →
      R276.Converges orderLimit
        (λ cutoff → embed
          (R338.differentiatedMagnitude source
            (R318.scaleOf base cutoff)
            (R318.volumeOf base cutoff)
            (leftDirection energy mode time)
            (rightDirection energy mode time)))
        (Gap.connectedCorrelation spectrum
          (Gap.modeObservable spectrum energy mode) time)

    embeddedSourceEnvelopeBelowSpectrumEnvelope :
      ∀ cutoff energy mode time →
      R276.LessEqual orderLimit
        (embed
          (R338.sourceEnvelope source
            (R318.scaleOf base cutoff)
            (R318.volumeOf base cutoff)
            (R338.sourceRoot source
              (R318.scaleOf base cutoff)
              (R318.volumeOf base cutoff)
              (leftDirection energy mode time)
              (rightDirection energy mode time))
            (R338.sourceDistance source
              (leftDirection energy mode time)
              (rightDirection energy mode time))))
        (Gap.clusteringEnvelope spectrum
          (Gap.modeObservable spectrum energy mode) time)

open CanonicalCMP116ModeSelectedApplication public

asHistoricalModeSelectedApplication :
  ∀ {Measure TestObservable Observable Energy Bound}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    {source : R338.CanonicalCommonDomainCMP116Source base demands}
    {spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound} →
  CanonicalCMP116ModeSelectedApplication base demands source spectrum →
  Mode.CMP116ModeSelectedSpectrumApplication spectrum
    (R338.canonicalSourceBuildsGenericPublishedSource source)
asHistoricalModeSelectedApplication
    {base = base} {demands = demands} {source = source} application = record
  { Mode.CMP116ModeSelectedSpectrumApplication.orderLimit = orderLimit application
  ; Mode.CMP116ModeSelectedSpectrumApplication.orderTransitive = orderTransitive application
  ; Mode.CMP116ModeSelectedSpectrumApplication.embed = embed application
  ; Mode.CMP116ModeSelectedSpectrumApplication.sourceOrderToLimitOrder =
      rationalOrderEmbedding application
  ; Mode.CMP116ModeSelectedSpectrumApplication.orderIsSpectrumOrder =
      orderIsSpectrumOrder application
  ; Mode.CMP116ModeSelectedSpectrumApplication.scaleOf = R318.scaleOf base
  ; Mode.CMP116ModeSelectedSpectrumApplication.volumeOf = R318.volumeOf base
  ; Mode.CMP116ModeSelectedSpectrumApplication.leftDirection = leftDirection application
  ; Mode.CMP116ModeSelectedSpectrumApplication.rightDirection = rightDirection application
  ; Mode.CMP116ModeSelectedSpectrumApplication.selectedPairAdmissible =
      λ cutoff energy mode time →
        Common.sourceCoordinateInside
          (R114.canonicalCMP116CommonDomain
            {R318.Scale base} {R318.Volume base} demands)
          (R318.scaleOf base cutoff)
          (R318.volumeOf base cutoff)
  ; Mode.CMP116ModeSelectedSpectrumApplication.embeddedSourceMagnitudeConvergesToSpectrum =
      embeddedSourceMagnitudeConvergesToSpectrum application
  ; Mode.CMP116ModeSelectedSpectrumApplication.embeddedSourceEnvelopeBelowSpectrumEnvelope =
      embeddedSourceEnvelopeBelowSpectrumEnvelope application
  }

canonicalModeSelectedApplicationBuildsSubgapUpper :
  ∀ {Measure TestObservable Observable Energy Bound}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    {source : R338.CanonicalCommonDomainCMP116Source base demands}
    {spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound} →
  CanonicalCMP116ModeSelectedApplication base demands source spectrum →
  Gap.SubgapModeClusteringUpper spectrum
canonicalModeSelectedApplicationBuildsSubgapUpper application =
  Mode.cmp116ModeSelectedApplicationBuildsSubgapUpper
    (asHistoricalModeSelectedApplication application)

record Round340Boundary : Set where
  constructor round340-boundary
  field
    selectedPairAdmissibilityIndependentLeaf : Bool
    selectedPairAdmissibilityIndependentLeafIsFalse :
      selectedPairAdmissibilityIndependentLeaf ≡ false
    commonDomainMembershipCompilerOwned : Bool
    commonDomainMembershipCompilerOwnedIsTrue :
      commonDomainMembershipCompilerOwned ≡ true
    sameSpectrumConvergenceStillRequired : Bool
    sameSpectrumConvergenceStillRequiredIsTrue :
      sameSpectrumConvergenceStillRequired ≡ true
    sourceEnvelopeToSpectrumEnvelopeStillRequired : Bool
    sourceEnvelopeToSpectrumEnvelopeStillRequiredIsTrue :
      sourceEnvelopeToSpectrumEnvelopeStillRequired ≡ true
    modeToSourceDirectionSelectionStillRequired : Bool
    modeToSourceDirectionSelectionStillRequiredIsTrue :
      modeToSourceDirectionSelectionStillRequired ≡ true
    freshYMDecayEstimateIntroduced : Bool
    freshYMDecayEstimateIntroducedIsFalse :
      freshYMDecayEstimateIntroduced ≡ false

canonicalRound340Boundary : Round340Boundary
canonicalRound340Boundary =
  round340-boundary false refl true refl true refl true refl true refl false refl

round340CompilerLevel : ProofLevel
round340CompilerLevel = machineChecked

round340ModeSameSpectrumConvergenceLevel : ProofLevel
round340ModeSameSpectrumConvergenceLevel = conditional

round340EnvelopeComparisonLevel : ProofLevel
round340EnvelopeComparisonLevel = conditional

round340ModeSourceDirectionLevel : ProofLevel
round340ModeSourceDirectionLevel = conditional

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
