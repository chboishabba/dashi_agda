{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTActiveGaugeSectorTotalizationExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.SharedEffectiveSourceRecoveryExact as Shared
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as QFT

------------------------------------------------------------------------
-- CLAY QUANTIFIER != PHYSICAL SECTOR SUM
--
-- The literal Yang-Mills construction is parameterised by compact simple G
-- because the Clay theorem is universal in G.  That theorem parameter is not
-- itself a statement that every compact simple G is simultaneously an active
-- gauge sector of one physical candidate.
--
-- GRQFT must therefore choose the active physical sector(s) first and only then
-- totalise their stress.  The legacy QFTStressAggregation relation remains the
-- compatibility surface consumed by existing weld compilers.
------------------------------------------------------------------------

record PhysicalGaugeSectorSelection (U : Weld.UnifiedCandidate) : Set₁ where
  field
    ActiveSector :
      Weld.Candidate U →
      QFT.CompactSimpleGroup (Weld.qftCarriers U) →
      Set

    selectedGroup :
      Weld.Candidate U →
      QFT.CompactSimpleGroup (Weld.qftCarriers U)

    selectedGroupIsActive :
      ∀ candidate → ActiveSector candidate (selectedGroup candidate)

open PhysicalGaugeSectorSelection public

record SingleActiveGaugeSectorTotalization
    {U : Weld.UnifiedCandidate}
    (selection : PhysicalGaugeSectorSelection U) : Set₁ where
  field
    declaredTotalIsSelectedSector :
      ∀ candidate →
      Weld.qftTotalStressShared U candidate
      ≡
      Weld.actualQFTSectorStressShared U candidate
        (selectedGroup selection candidate)

    legacyAggregationCompatibility :
      ∀ candidate →
      Weld.QFTStressAggregation U candidate
        (Weld.actualQFTSectorStressShared U candidate)
        (Weld.qftTotalStressShared U candidate)

open SingleActiveGaugeSectorTotalization public

singleActiveSectorQFTSourceFactorisation :
  ∀ {U : Weld.UnifiedCandidate}
    (source : Shared.SharedEffectiveSourceTheory U)
    (selection : PhysicalGaugeSectorSelection U) →
  SingleActiveGaugeSectorTotalization selection →
  (∀ candidate regime →
    Weld.qftRegime U regime →
    Shared.effectiveSource source
      (Weld.coarseGrain U candidate regime) regime
    ≡
    Weld.actualQFTSectorStressShared U
      (Weld.coarseGrain U candidate regime)
      (selectedGroup selection
        (Weld.coarseGrain U candidate regime))) →
  Shared.QFTSourceFactorisation source
singleActiveSectorQFTSourceFactorisation
    {U = U} source selection totalization selectedFactorises = record
  { Shared.QFTSourceFactorisation.qftStressAggregates =
      legacyAggregationCompatibility totalization
  ; Shared.QFTSourceFactorisation.qftTotalSourceFactorises =
      λ candidate regime qftAtRegime →
        trans
          (selectedFactorises candidate regime qftAtRegime)
          (sym
            (declaredTotalIsSelectedSector totalization
              (Weld.coarseGrain U candidate regime)))
  }

clayUniversalGroupParameterMeansAllGroupsPhysicallyActive : Bool
clayUniversalGroupParameterMeansAllGroupsPhysicallyActive = false

clayUniversalGroupParameterMeansAllGroupsPhysicallyActiveIsFalse :
  clayUniversalGroupParameterMeansAllGroupsPhysicallyActive ≡ false
clayUniversalGroupParameterMeansAllGroupsPhysicallyActiveIsFalse = refl

singleGaugeSectorStressAutomaticallyEqualsTotalEinsteinSource : Bool
singleGaugeSectorStressAutomaticallyEqualsTotalEinsteinSource = false

singleGaugeSectorStressAutomaticallyEqualsTotalEinsteinSourceIsFalse :
  singleGaugeSectorStressAutomaticallyEqualsTotalEinsteinSource ≡ false
singleGaugeSectorStressAutomaticallyEqualsTotalEinsteinSourceIsFalse = refl

activeSectorSelectionPrecedesStressTotalization : Bool
activeSectorSelectionPrecedesStressTotalization = true

activeSectorSelectionPrecedesStressTotalizationIsTrue :
  activeSectorSelectionPrecedesStressTotalization ≡ true
activeSectorSelectionPrecedesStressTotalizationIsTrue = refl
