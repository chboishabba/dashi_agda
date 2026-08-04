module DASHI.Physics.Closure.NSTriadKNLuoHighestAlphaFrontierReceipt where

------------------------------------------------------------------------
-- PURPOSE
-- Authoritative status receipt for the highest-alpha route.  It distinguishes
-- the closed finite Fourier foundation and cross-stage compositions from the
-- still-uninhabited continuum, physical, infinite-dimensional, arbitrary-data
-- and audit leaves.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSTriadKNLuoHighestAlphaFiniteFourierFoundationExact as Foundation
import DASHI.Physics.Closure.NSTriadKNLuoHighestAlphaCriticalCutsetExact as Cutset
import DASHI.Physics.Closure.NSTriadKNLuoHighestAlphaPathCompositionExact as Path
import DASHI.Physics.Closure.NSTriadKNLuoFullCompletionLemmaInventoryExact as Full

record HighestAlphaFrontierReceipt : Set where
  constructor receipt
  field
    fullInventoryOccurrenceCount : Nat
    fullInventoryUniqueNameCount : Nat
    criticalCutsetCount : Nat
    criticalPhaseCount : Nat

    fullCompletionInventoryConstructed : Bool
    finiteHermitianParsevalFoundationClosed : Bool
    hardProjectorOrthogonalityFoundationClosed : Bool
    hardProjectorDifferentialCommutationFoundationClosed : Bool
    highestAlphaCriticalCutsetConstructed : Bool
    finiteAnalyticCompositionClosed : Bool
    sourceSchurCompositionClosed : Bool
    canonicalContradictionCompositionClosed : Bool
    submissionCompositionClosed : Bool

    continuumTorusIntegralIdentificationClosed : Bool
    highestAlphaCriticalCutsetInhabited : Bool
    canonicalAnalyticPhysicalLeavesInhabited : Bool
    periodicNavierStokesGlobalRegularityProved : Bool
    submissionPackageComplete : Bool

open HighestAlphaFrontierReceipt public

highestAlphaFrontierReceipt : HighestAlphaFrontierReceipt
highestAlphaFrontierReceipt = receipt
  Full.completionLemmaOccurrenceCount
  Full.completionLemmaUniqueNameCount
  Cutset.criticalLemmaCount
  Cutset.criticalPhaseCount
  Full.fullCompletionLemmaInventoryConstructed
  Foundation.finiteHermitianParsevalFoundationClosed
  Foundation.hardProjectorOrthogonalityFoundationClosed
  Foundation.hardProjectorDifferentialCommutationFoundationClosed
  Cutset.highestAlphaCriticalCutsetConstructed
  Path.highestAlphaFiniteAnalyticCompositionClosed
  Path.highestAlphaSourceSchurCompositionClosed
  Path.highestAlphaCanonicalContradictionCompositionClosed
  Path.highestAlphaSubmissionCompositionClosed
  Foundation.continuumTorusIntegralIdentificationClosed
  Cutset.highestAlphaCriticalCutsetInhabited
  Cutset.canonicalAnalyticPhysicalLeavesInhabited
  Cutset.periodicNavierStokesGlobalRegularityProved
  Cutset.submissionPackageComplete

finiteFourierFoundationIsClosed :
  finiteHermitianParsevalFoundationClosed
    highestAlphaFrontierReceipt ≡ true
finiteFourierFoundationIsClosed =
  Foundation.finiteHermitianParsevalFoundationClosedIsTrue

hardProjectorOrthogonalityIsClosed :
  hardProjectorOrthogonalityFoundationClosed
    highestAlphaFrontierReceipt ≡ true
hardProjectorOrthogonalityIsClosed =
  Foundation.hardProjectorOrthogonalityFoundationClosedIsTrue

highestAlphaCutsetIsConstructed :
  highestAlphaCriticalCutsetConstructed
    highestAlphaFrontierReceipt ≡ true
highestAlphaCutsetIsConstructed =
  Cutset.highestAlphaCriticalCutsetConstructedIsTrue

finiteAnalyticCompositionIsClosed :
  finiteAnalyticCompositionClosed
    highestAlphaFrontierReceipt ≡ true
finiteAnalyticCompositionIsClosed =
  Path.highestAlphaFiniteAnalyticCompositionClosedIsTrue

sourceSchurCompositionIsClosed :
  sourceSchurCompositionClosed
    highestAlphaFrontierReceipt ≡ true
sourceSchurCompositionIsClosed =
  Path.highestAlphaSourceSchurCompositionClosedIsTrue

canonicalContradictionCompositionIsClosed :
  canonicalContradictionCompositionClosed
    highestAlphaFrontierReceipt ≡ true
canonicalContradictionCompositionIsClosed =
  Path.highestAlphaCanonicalContradictionCompositionClosedIsTrue

submissionCompositionIsClosed :
  submissionCompositionClosed
    highestAlphaFrontierReceipt ≡ true
submissionCompositionIsClosed =
  Path.highestAlphaSubmissionCompositionClosedIsTrue

continuumIntegralIdentificationRemainsOpen :
  continuumTorusIntegralIdentificationClosed
    highestAlphaFrontierReceipt ≡ false
continuumIntegralIdentificationRemainsOpen = refl

highestAlphaCutsetRemainsOpen :
  highestAlphaCriticalCutsetInhabited
    highestAlphaFrontierReceipt ≡ false
highestAlphaCutsetRemainsOpen = refl

canonicalPhysicalLeavesRemainOpen :
  canonicalAnalyticPhysicalLeavesInhabited
    highestAlphaFrontierReceipt ≡ false
canonicalPhysicalLeavesRemainOpen = refl

globalRegularityRemainsOpen :
  periodicNavierStokesGlobalRegularityProved
    highestAlphaFrontierReceipt ≡ false
globalRegularityRemainsOpen = refl

submissionPackageRemainsIncomplete :
  submissionPackageComplete highestAlphaFrontierReceipt ≡ false
submissionPackageRemainsIncomplete = refl
