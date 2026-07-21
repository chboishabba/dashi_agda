module DASHI.Physics.Closure.NSPeriodicContinuationAuthorityAdapter where

open import Agda.Primitive using (Level; lsuc)

open import DASHI.Physics.Closure.NSCompactGammaFourCriticalObligations
import DASHI.Physics.Closure.NSPeriodicFourierAnalyticAuthorityBoundary as Authority

------------------------------------------------------------------------
-- Exact adapter from standard periodic continuation theorems to the official
-- compact-Gamma setting.
--
-- Zero-data, small-data and diffuse-spectrum/BKM branches are standard once the
-- carrier predicates are matched.  The adapter proves those three branches and
-- leaves only Gamma-depletion and adaptive-chart continuation as novel coverage
-- inputs.
------------------------------------------------------------------------

record SelectedPeriodicContinuationAuthority
    {i : Level}
    (S : OfficialInitialDataSetting i) : Set (lsuc i) where
  field
    authority :
      Authority.PublishedPeriodicContinuationAuthority
        (InitialDatum S) (Solution S) (Time S)

    officialSmoothToAuthoritySmooth : ∀ u₀ →
      SmoothDivergenceFreeFiniteEnergy S u₀ →
      Authority.SmoothDivergenceFreeFiniteEnergy authority u₀

    officialSolutionToAuthoritySolution : ∀ u₀ u →
      SolvesFrom S u₀ u →
      Authority.SolvesFrom authority u₀ u

    selectedSolution : InitialDatum S → Solution S
    selectedSolutionSolves : ∀ u₀ →
      SmoothDivergenceFreeFiniteEnergy S u₀ →
      SolvesFrom S u₀ (selectedSolution u₀)

    mechanismFromContinuationAtEveryTime : ∀ u₀ →
      (∀ T → Authority.ContinuesBeyond authority u₀ T) →
      UniversalContinuationMechanism S u₀

open SelectedPeriodicContinuationAuthority public

zeroAuthorityBranchContinues :
  ∀ {i} {S : OfficialInitialDataSetting i} →
  (C : SelectedPeriodicContinuationAuthority S) →
  ∀ u₀ →
  Authority.ZeroDatum (authority C) u₀ →
  UniversalContinuationMechanism S u₀
zeroAuthorityBranchContinues C u₀ zero =
  mechanismFromContinuationAtEveryTime C u₀
    (λ T → Authority.zeroSolutionGlobal (authority C) u₀ T zero)

smallAuthorityBranchContinues :
  ∀ {i} {S : OfficialInitialDataSetting i} →
  (C : SelectedPeriodicContinuationAuthority S) →
  ∀ u₀ →
  Authority.SmallDatum (authority C) u₀ →
  UniversalContinuationMechanism S u₀
smallAuthorityBranchContinues C u₀ small =
  mechanismFromContinuationAtEveryTime C u₀
    (λ T → Authority.smallDataGlobal (authority C) u₀ T small)

diffuseAuthorityBranchContinues :
  ∀ {i} {S : OfficialInitialDataSetting i} →
  (C : SelectedPeriodicContinuationAuthority S) →
  ∀ u₀ →
  SmoothDivergenceFreeFiniteEnergy S u₀ →
  Authority.DiffuseSpectrum (authority C) u₀ →
  UniversalContinuationMechanism S u₀
diffuseAuthorityBranchContinues C u₀ official diffuse =
  mechanismFromContinuationAtEveryTime C u₀ closeAt
  where
  solution : Solution S
  solution = selectedSolution C u₀

  officialSolves : SolvesFrom S u₀ solution
  officialSolves = selectedSolutionSolves C u₀ official

  authoritySmooth :
    Authority.SmoothDivergenceFreeFiniteEnergy (authority C) u₀
  authoritySmooth = officialSmoothToAuthoritySmooth C u₀ official

  authoritySolves : Authority.SolvesFrom (authority C) u₀ solution
  authoritySolves =
    officialSolutionToAuthoritySolution C u₀ solution officialSolves

  closeAt : ∀ T → Authority.ContinuesBeyond (authority C) u₀ T
  closeAt T =
    Authority.bkmContinuation (authority C) u₀ solution T
      authoritySmooth
      authoritySolves
      (Authority.diffuseSpectrumGivesBKM
        (authority C) u₀ solution T diffuse authoritySolves)
