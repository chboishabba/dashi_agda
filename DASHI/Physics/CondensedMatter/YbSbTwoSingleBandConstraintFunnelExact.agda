module DASHI.Physics.CondensedMatter.YbSbTwoSingleBandConstraintFunnelExact where

------------------------------------------------------------------------
-- YbSb2 single-band exclusion funnel.
--
-- Source: Kataria et al., PRL accepted 3 Aug 2026,
-- DOI 10.1103/drzq-lfn5, arXiv:2601.07460.
--
-- The source argument is:
--   * orthorhombic D2h has only 1D irreps;
--   * in strong SOC this excludes the ordinary symmetry-allowed
--     single-band TRSB instability;
--   * in weak SOC, candidate TRSB single-band states have point nodes;
--   * experiment supports a fully gapped superconducting state.
--
-- This file proves the logic of the resulting no-go funnel while keeping
-- each physical/source premise explicit.
------------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)

record SingleBandTRSBFullGapFunnel : Set₁ where
  field
    Candidate : Set

    StrongSOC WeakSOC : Candidate → Set
    BreaksTRS HasPointNodes FullyGapped : Candidate → Set

    socExhaustive :
      (c : Candidate) → StrongSOC c ⊎ WeakSOC c

    strongSOCNoTRSB :
      (c : Candidate) → StrongSOC c → BreaksTRS c → ⊥

    weakSOCTRSBHasPointNodes :
      (c : Candidate) →
      WeakSOC c →
      BreaksTRS c →
      HasPointNodes c

    fullGapExcludesPointNodes :
      (c : Candidate) →
      FullyGapped c →
      HasPointNodes c →
      ⊥

open SingleBandTRSBFullGapFunnel public

record MatchesObservedTRSBFullGap
    (F : SingleBandTRSBFullGapFunnel)
    (c : Candidate F) : Set where
  constructor matches
  field
    breaksTRS : BreaksTRS F c
    fullyGapped : FullyGapped F c

open MatchesObservedTRSBFullGap public

noSingleBandCandidateMatchesTRSBFullGap :
  (F : SingleBandTRSBFullGapFunnel) →
  (c : Candidate F) →
  MatchesObservedTRSBFullGap F c →
  ⊥
noSingleBandCandidateMatchesTRSBFullGap F c observed
  with socExhaustive F c
... | inj₁ strong =
  strongSOCNoTRSB F c strong (breaksTRS observed)
... | inj₂ weak =
  fullGapExcludesPointNodes F c
    (fullyGapped observed)
    (weakSOCTRSBHasPointNodes F c weak (breaksTRS observed))

-- YbSb2 source-facing naming layer.  No premise is manufactured here.
record YbSbTwoSingleBandSourcePackage : Set₁ where
  field
    funnel : SingleBandTRSBFullGapFunnel

open YbSbTwoSingleBandSourcePackage public

ybSbTwoSingleBandNoGo :
  (S : YbSbTwoSingleBandSourcePackage) →
  (c : Candidate (funnel S)) →
  MatchesObservedTRSBFullGap (funnel S) c →
  ⊥
ybSbTwoSingleBandNoGo S =
  noSingleBandCandidateMatchesTRSBFullGap (funnel S)

-- Keep the multiorbital INT lane on a distinct carrier.  The single-band
-- theorem above cannot eliminate this type by mere reuse.
record MultiOrbitalINTCandidate : Set₁ where
  field
    BreaksTRS FullyGapped OrbitalAntisymmetric : Set
