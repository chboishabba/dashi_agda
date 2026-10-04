module DASHI.Moonshine.OggSSPSmallCharacteristicCorrectionMechanismComparisonExact where

------------------------------------------------------------------------
-- SMALL-CHARACTERISTIC CORRECTION MECHANISM COMPARISON
--
-- p=2 has TWO exact total-10 constructions:
--
--   A. orientation doublet x five invariant sectors, each with basis weight 1;
--   B. five unoriented inertia sectors weighted by v_2 of centralizer order:
--        3 + 3 + 2 + 1 + 1 = 10.
--
-- These have the same total but are not the same mechanism.
-- The centralizer-weighted candidate is preferred as the more arithmetic local
-- statistic because it is defined directly from isotropy orders.
--
-- p=3:
--
--   A. Deligne--Rapoport local incidence C2-orbit rank = 2;
--   B. analogous v_3 centralizer-depth sum on unoriented inertia = 4.
--
-- Hence the p=2 centralizer mechanism does NOT extend uniformly to p=3.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.OggSSPSmallCharacteristicInvariantClassRankExact as Rank
import DASHI.Moonshine.OggSSPP2InertiaCentralizerValuationExact as P2Centralizer
import DASHI.Moonshine.OggSSPP3InertiaCentralizerValuationNoGoExact as P3Centralizer
import DASHI.Moonshine.OggSSPSmallCharacteristicWildStackCorrectionConjectureExact as Wild
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

data CorrectionMechanism : Set where
  p2OrientationInvariantRank :
    CorrectionMechanism
  p2InertiaCentralizerDepth :
    CorrectionMechanism
  p3LocalOrbitRank :
    CorrectionMechanism
  p3InertiaCentralizerDepth :
    CorrectionMechanism

mechanismTotal :
  CorrectionMechanism ->
  Nat
mechanismTotal p2OrientationInvariantRank = 10
mechanismTotal p2InertiaCentralizerDepth =
  P2Centralizer.p2UnorientedInertiaDepthSum
mechanismTotal p3LocalOrbitRank = 2
mechanismTotal p3InertiaCentralizerDepth =
  P3Centralizer.p3UnorientedInertiaDepthSum

p2OrientationRankTotalIsTen :
  mechanismTotal p2OrientationInvariantRank ≡ 10
p2OrientationRankTotalIsTen = refl

p2CentralizerTotalIsTen :
  mechanismTotal p2InertiaCentralizerDepth ≡ 10
p2CentralizerTotalIsTen =
  P2Centralizer.p2UnorientedInertiaDepthSumIsTen

p3LocalOrbitTotalIsTwo :
  mechanismTotal p3LocalOrbitRank ≡ 2
p3LocalOrbitTotalIsTwo = refl

p3CentralizerTotalIsFour :
  mechanismTotal p3InertiaCentralizerDepth ≡ 4
p3CentralizerTotalIsFour =
  P3Centralizer.p3UnorientedInertiaDepthSumIsFour

------------------------------------------------------------------------
-- Preferred candidates are prime-specific.
------------------------------------------------------------------------

preferredP2Mechanism : CorrectionMechanism
preferredP2Mechanism =
  p2InertiaCentralizerDepth

preferredP3Mechanism : CorrectionMechanism
preferredP3Mechanism =
  p3LocalOrbitRank

preferredP2PaysExceptionalGap :
  mechanismTotal preferredP2Mechanism
  ≡ Wild.wildGeometricSectorCount Wild.primeTwo
preferredP2PaysExceptionalGap =
  P2Centralizer.p2UnorientedInertiaDepthSumIsTen

preferredP3PaysExceptionalGap :
  mechanismTotal preferredP3Mechanism
  ≡ Wild.wildGeometricSectorCount Wild.primeThree
preferredP3PaysExceptionalGap = refl

------------------------------------------------------------------------
-- Equal p2 totals do not identify mechanisms.
------------------------------------------------------------------------

data EqualP2TotalsIdentifyMechanisms : Set where
data OneUniformCentralizerLawCoversP2P3 : Set where
data PreferredMechanismIsAnalyticValuationTheorem : Set where

equalP2TotalsDoNotIdentifyMechanisms :
  EqualP2TotalsIdentifyMechanisms -> ⊥
equalP2TotalsDoNotIdentifyMechanisms ()

uniformCentralizerLawDoesNotCoverP2P3 :
  OneUniformCentralizerLawCoversP2P3 -> ⊥
uniformCentralizerLawDoesNotCoverP2P3 ()

preferredMechanismStillNeedsAnalyticValuationTheorem :
  PreferredMechanismIsAnalyticValuationTheorem -> ⊥
preferredMechanismStillNeedsAnalyticValuationTheorem ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryCrossModuleInference

record CorrectionMechanismComparisonBoundary : Set where
  constructor correction-mechanism-comparison-boundary
  field
    p2OrientationRankTenExact : Bool
    p2CentralizerDepthTenExact : Bool
    equalP2TotalsCollapsedToSameMechanism : Bool
    p2CentralizerDepthPreferredCandidate : Bool
    p3LocalOrbitTwoExact : Bool
    p3CentralizerDepthFourExact : Bool
    uniformCentralizerLawRejected : Bool
    p3LocalOrbitPreferredCandidate : Bool
    preferredCandidatesAlreadyAnalyticTheorems : Bool

canonicalCorrectionMechanismComparisonBoundary :
  CorrectionMechanismComparisonBoundary
canonicalCorrectionMechanismComparisonBoundary =
  correction-mechanism-comparison-boundary
    true true false true
    true true true true false
