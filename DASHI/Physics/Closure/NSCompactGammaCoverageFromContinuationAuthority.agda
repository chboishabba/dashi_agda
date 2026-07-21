module DASHI.Physics.Closure.NSCompactGammaCoverageFromContinuationAuthority where

open import Agda.Primitive using (Level; lsuc)
open import Data.Sum.Base using (_⊎_)

open import DASHI.Physics.Closure.NSCompactGammaFourCriticalObligations
import DASHI.Physics.Closure.NSCompactGammaInvariantCoverageReduction as Coverage
import DASHI.Physics.Closure.NSPeriodicFourierAnalyticAuthorityBoundary as Authority
import DASHI.Physics.Closure.NSPeriodicContinuationAuthorityAdapter as Continuation

------------------------------------------------------------------------
-- Official coverage with the standard branches discharged by published theory.
--
-- The remaining novel inputs are now only:
--
--   * the exhaustive five-way classification;
--   * Gamma-depletion -> BKM;
--   * the normalized/adaptive chart route and its switching theorem.
------------------------------------------------------------------------

record NovelCoverageInputs
    {i : Level}
    (S : OfficialInitialDataSetting i)
    (C : Continuation.SelectedPeriodicContinuationAuthority S) : Set (lsuc i) where
  field
    GammaDepleted AdaptiveChartRoute : InitialDatum S → Set i

    PacketNormalizationOrAdaptiveFloor : InitialDatum S → Set i
    ChartSelectionPiecewiseConstant : InitialDatum S → Set i
    ChartSwitchTimesLocallyFinite : InitialDatum S → Set i
    ChartSwitchCostsSummable : InitialDatum S → Set i
    CompactGammaPreservedBetweenSwitches : InitialDatum S → Set i

    officialCaseSplit : ∀ u₀ →
      SmoothDivergenceFreeFiniteEnergy S u₀ →
      Authority.ZeroDatum (Continuation.authority C) u₀
      ⊎ (Authority.SmallDatum (Continuation.authority C) u₀
      ⊎ (Authority.DiffuseSpectrum (Continuation.authority C) u₀
      ⊎ (GammaDepleted u₀
      ⊎ AdaptiveChartRoute u₀)))

    gammaDepletionBKMContinues : ∀ u₀ →
      SmoothDivergenceFreeFiniteEnergy S u₀ →
      GammaDepleted u₀ → UniversalContinuationMechanism S u₀

    chartRouteSuppliesNormalizationOrAdaptiveFloor : ∀ u₀ →
      AdaptiveChartRoute u₀ → PacketNormalizationOrAdaptiveFloor u₀
    chartRoutePiecewiseConstant : ∀ u₀ →
      AdaptiveChartRoute u₀ → ChartSelectionPiecewiseConstant u₀
    chartRouteSwitchesLocallyFinite : ∀ u₀ →
      AdaptiveChartRoute u₀ → ChartSwitchTimesLocallyFinite u₀
    chartRouteSwitchCostsSummable : ∀ u₀ →
      AdaptiveChartRoute u₀ → ChartSwitchCostsSummable u₀
    chartRoutePreservedBetweenSwitches : ∀ u₀ →
      AdaptiveChartRoute u₀ → CompactGammaPreservedBetweenSwitches u₀

    controlledAdaptiveChartContinues : ∀ u₀ →
      SmoothDivergenceFreeFiniteEnergy S u₀ →
      AdaptiveChartRoute u₀ →
      PacketNormalizationOrAdaptiveFloor u₀ →
      ChartSelectionPiecewiseConstant u₀ →
      ChartSwitchTimesLocallyFinite u₀ →
      ChartSwitchCostsSummable u₀ →
      CompactGammaPreservedBetweenSwitches u₀ →
      UniversalContinuationMechanism S u₀

open NovelCoverageInputs public

novelInputsToAdaptiveCoverage :
  ∀ {i} {S : OfficialInitialDataSetting i}
    {C : Continuation.SelectedPeriodicContinuationAuthority S} →
  NovelCoverageInputs S C →
  Coverage.AdaptiveChartOrDirectBKM S
novelInputsToAdaptiveCoverage {C = C} N = record
  { ZeroDatum = Authority.ZeroDatum (Continuation.authority C)
  ; SmallData = Authority.SmallDatum (Continuation.authority C)
  ; DiffuseSpectrum = Authority.DiffuseSpectrum (Continuation.authority C)
  ; GammaDepleted = GammaDepleted N
  ; AdaptiveChartRoute = AdaptiveChartRoute N
  ; PacketNormalizationOrAdaptiveFloor =
      PacketNormalizationOrAdaptiveFloor N
  ; ChartSelectionPiecewiseConstant = ChartSelectionPiecewiseConstant N
  ; ChartSwitchTimesLocallyFinite = ChartSwitchTimesLocallyFinite N
  ; ChartSwitchCostsSummable = ChartSwitchCostsSummable N
  ; CompactGammaPreservedBetweenSwitches =
      CompactGammaPreservedBetweenSwitches N
  ; officialCaseSplit = officialCaseSplit N
  ; zeroDatumContinues = λ u₀ official zero →
      Continuation.zeroAuthorityBranchContinues C u₀ zero
  ; smallDataContinues = λ u₀ official small →
      Continuation.smallAuthorityBranchContinues C u₀ small
  ; diffuseSpectrumBKMContinues = λ u₀ official diffuse →
      Continuation.diffuseAuthorityBranchContinues C u₀ official diffuse
  ; gammaDepletionBKMContinues = gammaDepletionBKMContinues N
  ; chartRouteSuppliesNormalizationOrAdaptiveFloor =
      chartRouteSuppliesNormalizationOrAdaptiveFloor N
  ; chartRoutePiecewiseConstant = chartRoutePiecewiseConstant N
  ; chartRouteSwitchesLocallyFinite = chartRouteSwitchesLocallyFinite N
  ; chartRouteSwitchCostsSummable = chartRouteSwitchCostsSummable N
  ; chartRoutePreservedBetweenSwitches = chartRoutePreservedBetweenSwitches N
  ; controlledAdaptiveChartContinues = controlledAdaptiveChartContinues N
  }

coverageFromStandardContinuationAndNovelInputs :
  ∀ {i} {S : OfficialInitialDataSetting i}
    {C : Continuation.SelectedPeriodicContinuationAuthority S} →
  NovelCoverageInputs S C →
  UniversalReplacementMechanism S
coverageFromStandardContinuationAndNovelInputs N =
  Coverage.adaptiveChartOrDirectBKMMechanism
    (novelInputsToAdaptiveCoverage N)
