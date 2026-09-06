module DASHI.Analysis.RiemannG2AlpogeFurmanClusteringNonDescentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannReflectionOrbitDefectExact as AF
import DASHI.Analysis.RiemannG2GapSplitClusteringLeanReturn8894Exact as Gap

------------------------------------------------------------------------
-- ALPOGE--FURMAN GLOBAL SIMPLE-ZERO RESULT -> LOCAL CLUSTERING NON-DESCENT
--
-- Primary source:
--   Levent Alpöge and Ralph Furman,
--   "More than two thirds of the zeta zeros are simple and on the critical line",
--   arXiv:2608.13637 (2026), DOI: 10.48550/arXiv.2608.13637.
--
-- The existing AF owner records the global/asymptotic theorem and carefully
-- separates it from the actual analytic zero carrier.  The current gap-split
-- consumer is different: at one selected ordinate and one selected scale
-- D = pi/(3 Lambda), it needs the target-centred inequality
--
--   (4/pi^2) * highGapMass < lowGapMass.
--
-- This module proves the information-shape obstruction exactly: a global
-- simple-zero population summary does not determine a local low/high-gap split.
-- Therefore the >2/3 theorem is a valuable global donor, but it cannot be used
-- as a direct inhabitant of the local clustering producer without an additional
-- localization theorem.
------------------------------------------------------------------------

data GlobalSimpleSummary : Set where
  twoThirdsSimpleSummary : GlobalSimpleSummary

data LocalGapPattern : Set where
  locallyClustered locallyUnclustered : LocalGapPattern

data FiniteZeroWorld : Set where
  sameGlobalClustered sameGlobalUnclustered : FiniteZeroWorld

globalSimpleView : FiniteZeroWorld → GlobalSimpleSummary
globalSimpleView sameGlobalClustered = twoThirdsSimpleSummary
globalSimpleView sameGlobalUnclustered = twoThirdsSimpleSummary

localGapView : FiniteZeroWorld → LocalGapPattern
localGapView sameGlobalClustered = locallyClustered
localGapView sameGlobalUnclustered = locallyUnclustered

sameGlobalSummary :
  globalSimpleView sameGlobalClustered ≡
  globalSimpleView sameGlobalUnclustered
sameGlobalSummary = refl

localPatternsDiffer :
  localGapView sameGlobalClustered ≡ localGapView sameGlobalUnclustered → ⊥
localPatternsDiffer ()

record GlobalSimpleToLocalClusteringBoundary : Set where
  constructor global-simple-to-local-clustering-boundary
  field
    sourceAuthor : String
    sourceTitle : String
    stableIdentifier : String

    globalSimpleCriticalLineProportionIsRelevantDonor : Bool
    globalSimpleCriticalLineProportionIsRelevantDonorIsTrue :
      globalSimpleCriticalLineProportionIsRelevantDonor ≡ true

    existingAFReflectionOwnerImported : Bool
    existingAFReflectionOwnerImportedIsTrue :
      existingAFReflectionOwnerImported ≡ true

    globalSimpleSummaryDeterminesTargetLocalGapPattern : Bool
    globalSimpleSummaryDeterminesTargetLocalGapPatternIsFalse :
      globalSimpleSummaryDeterminesTargetLocalGapPattern ≡ false

    alpogeFurmanDirectlyClosesGapSplitClustering : Bool
    alpogeFurmanDirectlyClosesGapSplitClusteringIsFalse :
      alpogeFurmanDirectlyClosesGapSplitClustering ≡ false

    additionalLocalizationTheoremRequired : Bool
    additionalLocalizationTheoremRequiredIsTrue :
      additionalLocalizationTheoremRequired ≡ true

    clusteringConsumerStillLive : Bool
    clusteringConsumerStillLiveIsTrue : clusteringConsumerStillLive ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    boundedReading : String

open GlobalSimpleToLocalClusteringBoundary public

canonicalGlobalSimpleToLocalClusteringBoundary :
  GlobalSimpleToLocalClusteringBoundary
canonicalGlobalSimpleToLocalClusteringBoundary =
  global-simple-to-local-clustering-boundary
    "Levent Alpöge; Ralph Furman"
    "More than two thirds of the zeta zeros are simple and on the critical line"
    "DOI 10.48550/arXiv.2608.13637"
    true refl
    true refl
    false refl
    false refl
    true refl
    true refl
    false refl
    "The Alpöge--Furman global simple/on-critical-line proportion is strong and relevant background, but global population information does not descend to the selected target-centred low/high-gap split. The exact finite collision above has identical global summaries and different local gap patterns. A new localization/spacing theorem is therefore required before this donor can feed the live (4/pi^2) highGapMass < lowGapMass consumer."

------------------------------------------------------------------------
-- Weld back to the existing 8894 owner: clustering remains the live route.
------------------------------------------------------------------------

existingGapSplitStillRequiresClustering :
  Gap.currentGapSplitRouteState ≡ Gap.clusteringRequired
existingGapSplitStillRequiresClustering = refl

existingGapSplitRejectsCoarseCountingOnly :
  Gap.GapSplitRelevant Gap.deriveClusteringFromCoarseCountingOnly → ⊥
existingGapSplitRejectsCoarseCountingOnly = Gap.coarseCountingClusteringPruned
