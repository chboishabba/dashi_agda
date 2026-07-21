module DASHI.Physics.Closure.NSCompactGammaOfficialCoverageCompletion where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

open import DASHI.Physics.Closure.NSCompactGammaFourCriticalObligations
open import DASHI.Physics.Closure.NSCompactGammaParameterCoverageCompletion

------------------------------------------------------------------------
-- Complete route A: zero/nonzero split.
------------------------------------------------------------------------

record CompleteZeroNonzeroCoverage
    {i : Level}
    (S : OfficialInitialDataSetting i) : Set (lsuc i) where
  field
    route : ZeroNonzeroOfficialCoverage S
    zeroOrNonzero : ∀ u₀ →
      (u₀ ≡ zeroDatum route)
      ⊎ NotEqual route u₀ (zeroDatum route)

open CompleteZeroNonzeroCoverage public

zeroNonzeroCoverageYieldsGlobalSmoothness :
  ∀ {i} {S : OfficialInitialDataSetting i} →
  (C : CompleteZeroNonzeroCoverage S) →
  ∀ u₀ →
  SmoothDivergenceFreeFiniteEnergy S u₀ →
  GlobalSmoothSolution (route C) u₀
zeroNonzeroCoverageYieldsGlobalSmoothness C u₀ official
  with zeroOrNonzero C u₀
... | inj₁ equal rewrite equal = zeroDatumGlobalSmooth (route C)
... | inj₂ nonzero = nonzeroRouteCloses (route C) u₀ official nonzero

------------------------------------------------------------------------
-- Complete route B: entry before singularity plus preservation/closure.
------------------------------------------------------------------------

record CompleteEntryCoverage
    {i : Level}
    (S : OfficialInitialDataSetting i) : Set (lsuc i) where
  field
    route : EntryCoverageRoute S
    GlobalSmoothSolution : InitialDatum S → Set i
    entryAndPreservationClose : ∀ u₀ u →
      SmoothDivergenceFreeFiniteEnergy S u₀ →
      SolvesFrom S u₀ u →
      GlobalSmoothSolution u₀

open CompleteEntryCoverage public

entryCoverageYieldsGlobalSmoothness :
  ∀ {i} {S : OfficialInitialDataSetting i} →
  (C : CompleteEntryCoverage S) →
  ∀ u₀ u →
  SmoothDivergenceFreeFiniteEnergy S u₀ →
  SolvesFrom S u₀ u →
  GlobalSmoothSolution C u₀
entryCoverageYieldsGlobalSmoothness C = entryAndPreservationClose C

------------------------------------------------------------------------
-- Complete route C: finite packet atlas and controlled switching.
------------------------------------------------------------------------

record CompletePacketAtlasCoverage
    {i : Level}
    (S : OfficialInitialDataSetting i) : Set (lsuc i) where
  field
    atlas : FinitePacketAtlasCoverage S
    GlobalSmoothSolution : InitialDatum S → Set i
    atlasMechanismCloses : ∀ u₀ →
      SmoothDivergenceFreeFiniteEnergy S u₀ →
      GlobalSmoothSolution u₀

open CompletePacketAtlasCoverage public

packetAtlasCoverageYieldsGlobalSmoothness :
  ∀ {i} {S : OfficialInitialDataSetting i} →
  (C : CompletePacketAtlasCoverage S) →
  ∀ u₀ →
  SmoothDivergenceFreeFiniteEnergy S u₀ →
  GlobalSmoothSolution C u₀
packetAtlasCoverageYieldsGlobalSmoothness C = atlasMechanismCloses C

------------------------------------------------------------------------
-- Complete route D: packet-chart or direct-BKM dichotomy.
--
-- This is the exact global route requested by the analytic audit.  It keeps the
-- spectral concentration/depletion alternatives, chart switching estimates and
-- final continuation mechanism in one owner, so a shell-selection witness from
-- one model cannot be combined with switching or BKM witnesses from another.
------------------------------------------------------------------------

record ChartOrDirectBKMCoverage
    {i : Level}
    (S : OfficialInitialDataSetting i) : Set (lsuc i) where
  field
    State Chart : Set i

    NonzeroState : State → Set i
    PacketConcentrated : Chart → State → Set i
    DiffuseSpectrumBKMControl : State → Set i
    GammaAboveFloor : Chart → State → Set i
    StretchingDepleted : State → Set i
    LocalBKMContinuation : State → Set i
    CompactGammaAdmissibleInChart : Chart → State → Set i

    spectralPacketOrDiffuseRegularity : ∀ state →
      NonzeroState state →
      (Σ Chart (λ chart → PacketConcentrated chart state))
      ⊎ DiffuseSpectrumBKMControl state

    gammaChartOrDepletion : ∀ chart state →
      PacketConcentrated chart state →
      GammaAboveFloor chart state ⊎ StretchingDepleted state

    stretchingDepletionGivesBKM : ∀ state →
      StretchingDepleted state → LocalBKMContinuation state

    diffuseSpectrumGivesBKM : ∀ state →
      DiffuseSpectrumBKMControl state → LocalBKMContinuation state

    selectedChartAdmissible : ∀ chart state →
      PacketConcentrated chart state →
      GammaAboveFloor chart state →
      CompactGammaAdmissibleInChart chart state

    selectedChart : State → Chart
    selectedChartPiecewiseConstant : State → Set i
    chartSwitchTimesLocallyFinite : State → Set i
    chartSwitchPotentialJumpControlled : State → Set i
    chartSwitchCostsSummable : State → Set i
    compactGammaPreservedBetweenSwitches : State → Set i

    -- The substantive global leaf.  It must be derived from the preceding
    -- dichotomies and switching estimates in the selected periodic carrier.
    chartOrDirectBKMSuppliesUniversalMechanism : ∀ u₀ →
      SmoothDivergenceFreeFiniteEnergy S u₀ →
      UniversalContinuationMechanism S u₀

open ChartOrDirectBKMCoverage public

chartOrDirectBKMToUniversalReplacement :
  ∀ {i} {S : OfficialInitialDataSetting i} →
  ChartOrDirectBKMCoverage S → UniversalReplacementMechanism S
chartOrDirectBKMToUniversalReplacement C = record
  { allOfficialDataHaveUniversalMechanism =
      chartOrDirectBKMSuppliesUniversalMechanism C
  }

record CompleteChartOrDirectBKMCoverage
    {i : Level}
    (S : OfficialInitialDataSetting i) : Set (lsuc i) where
  field
    route : ChartOrDirectBKMCoverage S
    GlobalSmoothSolution : InitialDatum S → Set i
    universalMechanismCloses : ∀ u₀ →
      UniversalContinuationMechanism S u₀ →
      GlobalSmoothSolution u₀

open CompleteChartOrDirectBKMCoverage public

chartOrDirectBKMCoverageYieldsGlobalSmoothness :
  ∀ {i} {S : OfficialInitialDataSetting i} →
  (C : CompleteChartOrDirectBKMCoverage S) →
  ∀ u₀ →
  SmoothDivergenceFreeFiniteEnergy S u₀ →
  GlobalSmoothSolution C u₀
chartOrDirectBKMCoverageYieldsGlobalSmoothness C u₀ official =
  universalMechanismCloses C u₀
    (chartOrDirectBKMSuppliesUniversalMechanism
      (route C) u₀ official)

------------------------------------------------------------------------
-- One proof-side resolution.  The obstruction route is deliberately not
-- included here because it refutes universality rather than producing a global
-- solution theorem.
------------------------------------------------------------------------

OfficialCoverageProof :
  ∀ {i} → OfficialInitialDataSetting i → Set (lsuc i)
OfficialCoverageProof S =
  CompleteZeroNonzeroCoverage S
  ⊎ (CompleteEntryCoverage S
  ⊎ (CompletePacketAtlasCoverage S
  ⊎ CompleteChartOrDirectBKMCoverage S))
