module DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact where

------------------------------------------------------------------------
-- UNIVERSAL EVEN-CONE BIDI CUTSET
--
-- Forward from existing Lean owners:
--
--   * `literalWeilSameOrdinateEvenCone` already constructs, for any target zero
--     at nonzero ordinate, a nonnegative taper and parity quotient in which the
--     literal pole class is annihilated exactly and the complete same-ordinate
--     zero cluster has strictly positive value.
--
--   * `primeEvenConeUnreachable` further proves that, under
--
--         9*pi <= 4*|t|*log 2,
--
--     the literal prime vector vanishes exactly for the same high-ordinate
--     taper family.
--
-- Backward from the final RH contradiction:
--
--   * the remaining high-ordinate mathematical payment is therefore the signed
--     off-ordinate zero fibre plus the deterministic Gamma channel;
--   * low ordinates can be discharged independently by any certified source
--     theorem/verification covering the complementary region;
--   * the final logical composition does not need the conditional three-zero
--     Schur construction.
--
-- This file records provenance and the high/low logical compiler.  It does not
-- transport the cited Lean proofs into Agda.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannG2FinalPoleQuotientAnalyticCoreExact as FinalCore

record UniversalEvenConeReturn : Set where
  constructor universal-even-cone-return
  field
    poleQuotientAvailableForArbitraryTargetZero : Bool
    poleQuotientAvailableForArbitraryTargetZeroIsTrue :
      poleQuotientAvailableForArbitraryTargetZero ≡ true

    sameOrdinateClusterStrictlyPositiveInOwner : Bool
    sameOrdinateClusterStrictlyPositiveInOwnerIsTrue :
      sameOrdinateClusterStrictlyPositiveInOwner ≡ true

    highOrdinatePrimeVectorExactlyZeroInOwner : Bool
    highOrdinatePrimeVectorExactlyZeroInOwnerIsTrue :
      highOrdinatePrimeVectorExactlyZeroInOwner ≡ true

    leanProofTransportedIntoAgda : Bool
    leanProofTransportedIntoAgdaIsFalse : leanProofTransportedIntoAgda ≡ false

    absoluteOffOrdinateMajorantStillPreferred : Bool
    absoluteOffOrdinateMajorantStillPreferredIsFalse :
      absoluteOffOrdinateMajorantStillPreferred ≡ false

    signedOffOrdinateEstimateClosed : Bool
    signedOffOrdinateEstimateClosedIsFalse : signedOffOrdinateEstimateClosed ≡ false

    gammaPaymentClosed : Bool
    gammaPaymentClosedIsFalse : gammaPaymentClosed ≡ false

    boundedReading : String

open UniversalEvenConeReturn public

canonicalUniversalEvenConeReturn : UniversalEvenConeReturn
canonicalUniversalEvenConeReturn =
  universal-even-cone-return
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    "The universal target observer is already the same-ordinate positive even-cone quotient: the pole class is killed exactly for every target ordinate, and the prime vector is exactly zero in the high-ordinate short-support regime. The remaining high-ordinate work is signed off-ordinate reflection-orbit control plus Gamma."

------------------------------------------------------------------------
-- Backward high/low completion compiler.
------------------------------------------------------------------------

record HighLowCompletion : Set₁ where
  field
    Zero : Set
    Critical Low High : Zero → Set

    cover : (ρ : Zero) → Low ρ ⊎ High ρ
    lowCertifiedCritical : (ρ : Zero) → Low ρ → Critical ρ
    highAnalyticCritical : (ρ : Zero) → High ρ → Critical ρ

open HighLowCompletion public

allCriticalFromHighLow :
  (d : HighLowCompletion) →
  (ρ : Zero d) → Critical d ρ
allCriticalFromHighLow d ρ with cover d ρ
... | inj₁ low = lowCertifiedCritical d ρ low
... | inj₂ high = highAnalyticCritical d ρ high

------------------------------------------------------------------------
-- SAME-SUBSTRATE RH WELD
--
-- The generic high/low compiler above is useful only if its Zero and Critical
-- carriers are identified with the SAME completed-zeta object consumed by the
-- prize-facing `RiemannHypothesisFor`.  The records below make that identity
-- definitional rather than leaving a prose-level final bridge.
------------------------------------------------------------------------

record AnalyticNontrivialZero (analytic : Analytic.AnalyticSubstrate) : Set where
  constructor analytic-nontrivial-zero
  field
    point :
      Analytic.ComplexAnalyticCarrier.Complex
        (Analytic.AnalyticSubstrate.carrier analytic)
    nontrivial :
      Analytic.CompletedRiemannZeta.nontrivialZero
        (Analytic.AnalyticSubstrate.completed analytic)
        point

open AnalyticNontrivialZero public

analyticCritical :
  {analytic : Analytic.AnalyticSubstrate} →
  AnalyticNontrivialZero analytic → Set
analyticCritical {analytic} ρ =
  Analytic.CompletedRiemannZeta.criticalLine
    (Analytic.AnalyticSubstrate.completed analytic)
    (point ρ)

record AnalyticHighLowCompletion
    (analytic : Analytic.AnalyticSubstrate) : Set₁ where
  constructor analytic-high-low-completion
  field
    Low High : AnalyticNontrivialZero analytic → Set

    cover :
      (ρ : AnalyticNontrivialZero analytic) →
      Low ρ ⊎ High ρ

    lowCertifiedCritical :
      (ρ : AnalyticNontrivialZero analytic) →
      Low ρ →
      analyticCritical ρ

    highAnalyticCritical :
      (ρ : AnalyticNontrivialZero analytic) →
      High ρ →
      analyticCritical ρ

open AnalyticHighLowCompletion public

toGenericHighLowCompletion :
  {analytic : Analytic.AnalyticSubstrate} →
  AnalyticHighLowCompletion analytic →
  HighLowCompletion
toGenericHighLowCompletion {analytic} d = record
  { Zero = AnalyticNontrivialZero analytic
  ; Critical = analyticCritical
  ; Low = AnalyticHighLowCompletion.Low d
  ; High = AnalyticHighLowCompletion.High d
  ; cover = AnalyticHighLowCompletion.cover d
  ; lowCertifiedCritical = AnalyticHighLowCompletion.lowCertifiedCritical d
  ; highAnalyticCritical = AnalyticHighLowCompletion.highAnalyticCritical d
  }

analyticHighLowCompletionImpliesRH :
  (analytic : Analytic.AnalyticSubstrate) →
  AnalyticHighLowCompletion analytic →
  Analytic.RiemannHypothesisFor analytic
analyticHighLowCompletionImpliesRH analytic d s hz =
  allCriticalFromHighLow
    (toGenericHighLowCompletion d)
    (analytic-nontrivial-zero s hz)

------------------------------------------------------------------------
-- OFF-LINE HIGH-ZERO -> FINAL ANALYTIC CORES -> CONTRADICTION.
--
-- This is the exact prize-facing role of the two final analytic cores.  They
-- must be constructible for the SAME high nontrivial zero under the hypothesis
-- that this zero is off the critical line.  The existing final-core compiler
-- then produces bottom.  No unconditional `bottom` inhabitant is asserted.
------------------------------------------------------------------------

CriticalLineStable : Analytic.AnalyticSubstrate → Set
CriticalLineStable analytic =
  (s : Analytic.ComplexAnalyticCarrier.Complex
    (Analytic.AnalyticSubstrate.carrier analytic)) →
  Neg (Neg
    (Analytic.CompletedRiemannZeta.criticalLine
      (Analytic.AnalyticSubstrate.completed analytic) s)) →
  Analytic.CompletedRiemannZeta.criticalLine
    (Analytic.AnalyticSubstrate.completed analytic) s

record HighOffLineAnalyticCoreProducer
    (analytic : Analytic.AnalyticSubstrate)
    (High : AnalyticNontrivialZero analytic → Set) : Set₁ where
  constructor high-off-line-analytic-core-producer
  field
    coresForOffLineHigh :
      (ρ : AnalyticNontrivialZero analytic) →
      High ρ →
      Neg (analyticCritical ρ) →
      FinalCore.FinalPoleQuotientTwoAnalyticCores

    attachmentsForOffLineHigh :
      (ρ : AnalyticNontrivialZero analytic) →
      (high : High ρ) →
      (offLine : Neg (analyticCritical ρ)) →
      FinalCore.FinalPoleQuotientAnalyticCoreAttachments
        (coresForOffLineHigh ρ high offLine)

    completionForOffLineHigh :
      (ρ : AnalyticNontrivialZero analytic) →
      (high : High ρ) →
      (offLine : Neg (analyticCritical ρ)) →
      FinalCore.FinalPoleQuotientAnalyticCompletion
        (coresForOffLineHigh ρ high offLine)
        (attachmentsForOffLineHigh ρ high offLine)

open HighOffLineAnalyticCoreProducer public

highOffLineAnalyticCoreContradiction :
  {analytic : Analytic.AnalyticSubstrate} →
  {High : AnalyticNontrivialZero analytic → Set} →
  HighOffLineAnalyticCoreProducer analytic High →
  (ρ : AnalyticNontrivialZero analytic) →
  High ρ →
  Neg (analyticCritical ρ) →
  ⊥
highOffLineAnalyticCoreContradiction producer ρ high offLine =
  FinalCore.compileAnalyticCoresToHighOrdinateContradiction
    (coresForOffLineHigh producer ρ high offLine)
    (attachmentsForOffLineHigh producer ρ high offLine)
    (completionForOffLineHigh producer ρ high offLine)

highCriticalFromAnalyticCores :
  {analytic : Analytic.AnalyticSubstrate} →
  {High : AnalyticNontrivialZero analytic → Set} →
  CriticalLineStable analytic →
  HighOffLineAnalyticCoreProducer analytic High →
  (ρ : AnalyticNontrivialZero analytic) →
  High ρ →
  analyticCritical ρ
highCriticalFromAnalyticCores stable producer ρ high =
  stable
    (point ρ)
    (λ offLine →
      highOffLineAnalyticCoreContradiction producer ρ high offLine)

compileAnalyticHighLowCompletion :
  (analytic : Analytic.AnalyticSubstrate) →
  (Low High : AnalyticNontrivialZero analytic → Set) →
  ((ρ : AnalyticNontrivialZero analytic) → Low ρ ⊎ High ρ) →
  ((ρ : AnalyticNontrivialZero analytic) → Low ρ → analyticCritical ρ) →
  CriticalLineStable analytic →
  HighOffLineAnalyticCoreProducer analytic High →
  AnalyticHighLowCompletion analytic
compileAnalyticHighLowCompletion analytic Low High coverLowHigh lowCritical stable producer =
  analytic-high-low-completion
    Low
    High
    coverLowHigh
    lowCritical
    (highCriticalFromAnalyticCores stable producer)

analyticCoreHighLowCompletionImpliesRH :
  (analytic : Analytic.AnalyticSubstrate) →
  (Low High : AnalyticNontrivialZero analytic → Set) →
  ((ρ : AnalyticNontrivialZero analytic) → Low ρ ⊎ High ρ) →
  ((ρ : AnalyticNontrivialZero analytic) → Low ρ → analyticCritical ρ) →
  CriticalLineStable analytic →
  HighOffLineAnalyticCoreProducer analytic High →
  Analytic.RiemannHypothesisFor analytic
analyticCoreHighLowCompletionImpliesRH
  analytic Low High coverLowHigh lowCritical stable producer =
  analyticHighLowCompletionImpliesRH analytic
    (compileAnalyticHighLowCompletion
      analytic Low High coverLowHigh lowCritical stable producer)

record UniversalEvenConeBoundary : Set where
  constructor universal-even-cone-boundary
  field
    threeExtraZerosNeededForUniversalObserver : Bool
    threeExtraZerosNeededForUniversalObserverIsFalse :
      threeExtraZerosNeededForUniversalObserver ≡ false

    lowOrdinateVerificationManufacturedHere : Bool
    lowOrdinateVerificationManufacturedHereIsFalse :
      lowOrdinateVerificationManufacturedHere ≡ false

    highOrdinateSignedTailManufacturedHere : Bool
    highOrdinateSignedTailManufacturedHereIsFalse :
      highOrdinateSignedTailManufacturedHere ≡ false

    rhDerivedHere : Bool
    rhDerivedHereIsFalse : rhDerivedHere ≡ false

canonicalUniversalEvenConeBoundary : UniversalEvenConeBoundary
canonicalUniversalEvenConeBoundary =
  universal-even-cone-boundary false refl false refl false refl false refl
