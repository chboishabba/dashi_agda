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
-- Every local predicate is indexed by the repository's actual `Solution S` and
-- `Time S`.  This prevents a disconnected abstract state space from carrying
-- the local dichotomies while an unrelated official solution supplies the final
-- continuation mechanism.
------------------------------------------------------------------------

record ChartOrDirectBKMCoverage
    {i : Level}
    (S : OfficialInitialDataSetting i) : Set (lsuc i) where
  field
    Chart : Set i

    NonzeroState : Solution S → Time S → Set i
    PacketConcentrated : Chart → Solution S → Time S → Set i
    DiffuseSpectrumBKMControl : Solution S → Time S → Set i
    GammaAboveFloor : Chart → Solution S → Time S → Set i
    StretchingDepleted : Solution S → Time S → Set i
    LocalBKMContinuation : Solution S → Time S → Set i
    CompactGammaAdmissibleInChart :
      Chart → Solution S → Time S → Set i

    spectralPacketOrDiffuseRegularity : ∀ u τ →
      NonzeroState u τ →
      (Σ Chart (λ chart → PacketConcentrated chart u τ))
      ⊎ DiffuseSpectrumBKMControl u τ

    gammaChartOrDepletion : ∀ chart u τ →
      PacketConcentrated chart u τ →
      GammaAboveFloor chart u τ ⊎ StretchingDepleted u τ

    stretchingDepletionGivesBKM : ∀ u τ →
      StretchingDepleted u τ → LocalBKMContinuation u τ

    diffuseSpectrumGivesBKM : ∀ u τ →
      DiffuseSpectrumBKMControl u τ → LocalBKMContinuation u τ

    selectedChartAdmissible : ∀ chart u τ →
      PacketConcentrated chart u τ →
      GammaAboveFloor chart u τ →
      CompactGammaAdmissibleInChart chart u τ

    selectedChart : Solution S → Time S → Chart
    selectedChartPiecewiseConstant : Solution S → Set i
    chartSwitchTimesLocallyFinite : Solution S → Set i
    chartSwitchPotentialJumpControlled : Solution S → Set i
    chartSwitchCostsSummable : Solution S → Set i
    compactGammaPreservedBetweenSwitches : Solution S → Set i

    -- The substantive global leaf.  It must be derived from the preceding
    -- dichotomies and switching estimates in the selected periodic carrier.
    chartOrDirectBKMSuppliesUniversalMechanism : ∀ u₀ u →
      SmoothDivergenceFreeFiniteEnergy S u₀ →
      SolvesFrom S u₀ u →
      UniversalContinuationMechanism S u₀

open ChartOrDirectBKMCoverage public

chartOrDirectBKMToUniversalReplacement :
  ∀ {i} {S : OfficialInitialDataSetting i} →
  (C : ChartOrDirectBKMCoverage S) →
  (solutionFor : InitialDatum S → Solution S) →
  (solutionForSolves : ∀ u₀ → SolvesFrom S u₀ (solutionFor u₀)) →
  UniversalReplacementMechanism S
chartOrDirectBKMToUniversalReplacement C solutionFor solutionForSolves = record
  { allOfficialDataHaveUniversalMechanism = λ u₀ official →
      chartOrDirectBKMSuppliesUniversalMechanism C
        u₀ (solutionFor u₀) official (solutionForSolves u₀)
  }

record CompleteChartOrDirectBKMCoverage
    {i : Level}
    (S : OfficialInitialDataSetting i) : Set (lsuc i) where
  field
    route : ChartOrDirectBKMCoverage S
    solutionFor : InitialDatum S → Solution S
    solutionForSolves : ∀ u₀ → SolvesFrom S u₀ (solutionFor u₀)

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
      (route C)
      u₀ (solutionFor C u₀)
      official (solutionForSolves C u₀))

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
