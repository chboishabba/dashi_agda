module DASHI.Physics.Closure.NSCompactGammaInvariantCoverageReduction where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

open import DASHI.Physics.Closure.NSCompactGammaFourCriticalObligations

------------------------------------------------------------------------
-- Real-carrier invariant-region logic.
--
-- Once continuity/Dini regularity and the four strict boundary estimates have
-- been proved in the concrete real carrier, a first exit is impossible.  This
-- module performs that no-first-exit argument exactly; it does not replace any
-- boundary differential estimate by an opaque final invariant-field assumption.
------------------------------------------------------------------------

data CompactGammaBoundaryFace : Set where
  gammaFloorFace : CompactGammaBoundaryFace
  packetEnergyFloorFace : CompactGammaBoundaryFace
  offPacketCeilingFace : CompactGammaBoundaryFace
  sizeCeilingFace : CompactGammaBoundaryFace

record FirstExitBoundaryReduction (i : Level) : Set (lsuc i) where
  field
    Time State : Set i

    FirstExit : Time → State → Set i
    BoundaryHit : CompactGammaBoundaryFace → Time → State → Set i

    firstExitHitsBoundary : ∀ τ u →
      FirstExit τ u →
      Σ CompactGammaBoundaryFace (λ face → BoundaryHit face τ u)

    gammaFloorStrictlyInward : ∀ τ u →
      BoundaryHit gammaFloorFace τ u → ⊥

    packetEnergyFloorStrictlyInward : ∀ τ u →
      BoundaryHit packetEnergyFloorFace τ u → ⊥

    offPacketCeilingStrictlyInward : ∀ τ u →
      BoundaryHit offPacketCeilingFace τ u → ⊥

    sizeCeilingStrictlyInward : ∀ τ u →
      BoundaryHit sizeCeilingFace τ u → ⊥

open FirstExitBoundaryReduction public

compactGammaFirstExitImpossible :
  ∀ {i} (R : FirstExitBoundaryReduction i) →
  ∀ τ u → FirstExit R τ u → ⊥
compactGammaFirstExitImpossible R τ u exit
  with firstExitHitsBoundary R τ u exit
... | gammaFloorFace , hit =
  gammaFloorStrictlyInward R τ u hit
... | packetEnergyFloorFace , hit =
  packetEnergyFloorStrictlyInward R τ u hit
... | offPacketCeilingFace , hit =
  offPacketCeilingStrictlyInward R τ u hit
... | sizeCeilingFace , hit =
  sizeCeilingStrictlyInward R τ u hit

------------------------------------------------------------------------
-- Official-data coverage logic.
--
-- The fixed positive absolute-floor atlas is already refuted.  A viable route
-- must therefore classify each official datum into one of:
--
--   zero, direct small-data, direct diffuse-spectrum BKM,
--   normalized/adaptive compact-Gamma chart, or depletion/BKM.
--
-- The chart branch explicitly carries normalization/adaptive-floor validity,
-- locally finite switching, summable switch costs and preservation between
-- switches.  Pattern matching below proves the universal replacement mechanism.
------------------------------------------------------------------------

record AdaptiveChartOrDirectBKM
    {i : Level}
    (S : OfficialInitialDataSetting i) : Set (lsuc i) where
  field
    ZeroDatum SmallData DiffuseSpectrum GammaDepleted :
      InitialDatum S → Set i

    AdaptiveChartRoute : InitialDatum S → Set i
    PacketNormalizationOrAdaptiveFloor : InitialDatum S → Set i
    ChartSelectionPiecewiseConstant : InitialDatum S → Set i
    ChartSwitchTimesLocallyFinite : InitialDatum S → Set i
    ChartSwitchCostsSummable : InitialDatum S → Set i
    CompactGammaPreservedBetweenSwitches : InitialDatum S → Set i

    officialCaseSplit : ∀ u₀ →
      SmoothDivergenceFreeFiniteEnergy S u₀ →
      ZeroDatum u₀
      ⊎ (SmallData u₀
      ⊎ (DiffuseSpectrum u₀
      ⊎ (GammaDepleted u₀
      ⊎ AdaptiveChartRoute u₀)))

    zeroDatumContinues : ∀ u₀ →
      ZeroDatum u₀ → UniversalContinuationMechanism S u₀

    smallDataContinues : ∀ u₀ →
      SmallData u₀ → UniversalContinuationMechanism S u₀

    diffuseSpectrumBKMContinues : ∀ u₀ →
      DiffuseSpectrum u₀ → UniversalContinuationMechanism S u₀

    gammaDepletionBKMContinues : ∀ u₀ →
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
      AdaptiveChartRoute u₀ →
      PacketNormalizationOrAdaptiveFloor u₀ →
      ChartSelectionPiecewiseConstant u₀ →
      ChartSwitchTimesLocallyFinite u₀ →
      ChartSwitchCostsSummable u₀ →
      CompactGammaPreservedBetweenSwitches u₀ →
      UniversalContinuationMechanism S u₀

open AdaptiveChartOrDirectBKM public

adaptiveChartOrDirectBKMMechanism :
  ∀ {i} {S : OfficialInitialDataSetting i} →
  AdaptiveChartOrDirectBKM S →
  UniversalReplacementMechanism S
adaptiveChartOrDirectBKMMechanism {S = S} C = record
  { allOfficialDataHaveUniversalMechanism = close }
  where
  close : ∀ u₀ →
    SmoothDivergenceFreeFiniteEnergy S u₀ →
    UniversalContinuationMechanism S u₀
  close u₀ official with officialCaseSplit C u₀ official
  ... | inj₁ zero = zeroDatumContinues C u₀ zero
  ... | inj₂ (inj₁ small) = smallDataContinues C u₀ small
  ... | inj₂ (inj₂ (inj₁ diffuse)) =
    diffuseSpectrumBKMContinues C u₀ diffuse
  ... | inj₂ (inj₂ (inj₂ (inj₁ depleted))) =
    gammaDepletionBKMContinues C u₀ depleted
  ... | inj₂ (inj₂ (inj₂ (inj₂ chart))) =
    controlledAdaptiveChartContinues C u₀ chart
      (chartRouteSuppliesNormalizationOrAdaptiveFloor C u₀ chart)
      (chartRoutePiecewiseConstant C u₀ chart)
      (chartRouteSwitchesLocallyFinite C u₀ chart)
      (chartRouteSwitchCostsSummable C u₀ chart)
      (chartRoutePreservedBetweenSwitches C u₀ chart)
