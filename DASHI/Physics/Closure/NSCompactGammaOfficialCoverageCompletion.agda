module DASHI.Physics.Closure.NSCompactGammaOfficialCoverageCompletion where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)
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
-- One proof-side resolution.  The obstruction route is deliberately not
-- included here because it refutes universality rather than producing a global
-- solution theorem.
------------------------------------------------------------------------

OfficialCoverageProof :
  ∀ {i} → OfficialInitialDataSetting i → Set (lsuc i)
OfficialCoverageProof S =
  CompleteZeroNonzeroCoverage S
  ⊎ (CompleteEntryCoverage S ⊎ CompletePacketAtlasCoverage S)
