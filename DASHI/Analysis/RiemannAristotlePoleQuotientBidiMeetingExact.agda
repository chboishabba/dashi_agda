module DASHI.Analysis.RiemannAristotlePoleQuotientBidiMeetingExact where

------------------------------------------------------------------------
-- BIDI MEETING: UNIVERSAL POLE QUOTIENT + COMPLEMENT MARGIN
--
-- This module binds the new complement-margin compiler to the strongest
-- already-owned source lane instead of inventing a new observer.
--
-- Forward source facts already recorded in
-- RiemannAristotleUniversalEvenConeBidiExact:
--
--   * arbitrary target zero admits the pole quotient;
--   * the same-ordinate cluster is strictly positive there;
--   * in the high-ordinate short-support lane the prime vector is exactly zero;
--   * Gamma is NOT paid/eliminated in that lane.
--
-- Backward consumer:
--
--   cluster = offOrdinate + Gamma
--   margin <= cluster
--   offOrdinate + Gamma <= budget < margin
--
-- which closes contradiction through the generic complement-margin compiler.
--
-- This is architecture/provenance plus an Agda compiler weld.  It does not
-- assert the missing off-ordinate estimate, Gamma bound, or quantitative margin.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as U
import DASHI.Analysis.RiemannAristotlePoleQuotientComplementMarginCompilerExact as C

universalPoleQuotientAvailable :
  U.poleQuotientAvailableForArbitraryTargetZero U.canonicalUniversalEvenConeReturn
  ≡ true
universalPoleQuotientAvailable = refl

universalClusterStrictlyPositive :
  U.sameOrdinateClusterStrictlyPositiveInOwner U.canonicalUniversalEvenConeReturn
  ≡ true
universalClusterStrictlyPositive = refl

universalHighOrdinatePrimeExactlyZero :
  U.highOrdinatePrimeVectorExactlyZeroInOwner U.canonicalUniversalEvenConeReturn
  ≡ true
universalHighOrdinatePrimeExactlyZero = refl

universalGammaPaymentStillOpen :
  U.gammaPaymentClosed U.canonicalUniversalEvenConeReturn ≡ false
universalGammaPaymentStillOpen = refl

poleQuotientBidiContradiction :
  (S : C.OrderedComplementSurface) →
  C.PoleQuotientComplementMargin S →
  ⊥
poleQuotientBidiContradiction = C.poleQuotientComplementMarginContradiction

record PoleQuotientBidiMeetingBoundary : Set where
  constructor pole-quotient-bidi-meeting-boundary
  field
    existingUniversalObserverReused : Bool
    existingUniversalObserverReusedIsTrue :
      existingUniversalObserverReused ≡ true

    finalLaneUsesRankTwoExactSchur : Bool
    finalLaneUsesRankTwoExactSchurIsFalse :
      finalLaneUsesRankTwoExactSchur ≡ false

    poleKilledExactlyByExistingOwner : Bool
    poleKilledExactlyByExistingOwnerIsTrue :
      poleKilledExactlyByExistingOwner ≡ true

    highOrdinatePrimeKilledExactlyByExistingOwner : Bool
    highOrdinatePrimeKilledExactlyByExistingOwnerIsTrue :
      highOrdinatePrimeKilledExactlyByExistingOwner ≡ true

    gammaRetainedAsDeterministicComplement : Bool
    gammaRetainedAsDeterministicComplementIsTrue :
      gammaRetainedAsDeterministicComplement ≡ true

    complementContradictionCompilerClosed : Bool
    complementContradictionCompilerClosedIsTrue :
      complementContradictionCompilerClosed ≡ true

    targetCenteredOffOrdinateBoundClosed : Bool
    targetCenteredOffOrdinateBoundClosedIsFalse :
      targetCenteredOffOrdinateBoundClosed ≡ false

    gammaComplementBudgetClosed : Bool
    gammaComplementBudgetClosedIsFalse :
      gammaComplementBudgetClosed ≡ false

    quantitativePositiveClusterMarginClosed : Bool
    quantitativePositiveClusterMarginClosedIsFalse :
      quantitativePositiveClusterMarginClosed ≡ false

canonicalPoleQuotientBidiMeetingBoundary : PoleQuotientBidiMeetingBoundary
canonicalPoleQuotientBidiMeetingBoundary =
  pole-quotient-bidi-meeting-boundary
    true refl
    false refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
