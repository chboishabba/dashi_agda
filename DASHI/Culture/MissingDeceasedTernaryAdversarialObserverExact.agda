module DASHI.Culture.MissingDeceasedTernaryAdversarialObserverExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import DASHI.Algebra.BalancedTernary using (Trit; neg; zero; pos)

------------------------------------------------------------------------
-- TERNARY OBSERVER FIBRE FOR INVESTIGATIVE CLAIMS
--
-- Cultural meme labels such as "normie / schizo / psycho" are retained only
-- as source-side vocabulary.  The formal carrier is neutral: baseline identity,
-- high-recall pattern search, and strategic/adversarial modelling.
--
-- The positive/negative polarity is deliberately conventional.  Any consumer
-- that depends on which nonzero observer was named + rather than - has imported
-- source rhetoric into the formal semantics and must fail the swap test.
------------------------------------------------------------------------

data ObserverPolarity : Set where
  patternDetector baselineObserver adversarialObserver : ObserverPolarity

observerTrit : ObserverPolarity → Trit
observerTrit patternDetector = pos
observerTrit baselineObserver = zero
observerTrit adversarialObserver = neg

polaritySwap : ObserverPolarity → ObserverPolarity
polaritySwap patternDetector = adversarialObserver
polaritySwap baselineObserver = baselineObserver
polaritySwap adversarialObserver = patternDetector

polaritySwapInvolution : (observer : ObserverPolarity) →
  polaritySwap (polaritySwap observer) ≡ observer
polaritySwapInvolution patternDetector = refl
polaritySwapInvolution baselineObserver = refl
polaritySwapInvolution adversarialObserver = refl

identityObserverMapsToZero : observerTrit baselineObserver ≡ zero
identityObserverMapsToZero = refl

record TemporalObserverFibre : Set where
  constructor temporal-observer-fibre
  field
    observationTime : String
    evidenceObjectReference : String
    observer : ObserverPolarity
    reading : String
    acquisitionConsequence : String

open TemporalObserverFibre public

record ObserverSwapInvariantReading : Set where
  constructor observer-swap-invariant-reading
  field
    claimReference : String
    baselineReadingReference : String
    positiveReadingReference : String
    negativeReadingReference : String
    signChoiceCreatesEvidenceAuthority : Bool
    signChoiceCreatesEvidenceAuthorityIsFalse :
      signChoiceCreatesEvidenceAuthority ≡ false
    bothPolaritiesMayNominateAcquisitions : Bool
    bothPolaritiesMayNominateAcquisitionsIsTrue :
      bothPolaritiesMayNominateAcquisitions ≡ true

canonicalObserverSwapInvariantReading : ObserverSwapInvariantReading
canonicalObserverSwapInvariantReading = observer-swap-invariant-reading
  "missing/deceased cohort candidate common-cause claim"
  "retain literal source/event state and ordinary reference-population reading"
  "search aggressively for structural conjunctions and anomalous dependencies"
  "model strategic concealment, selective disclosure and adversarial incentives"
  false refl true refl

record TernaryObserverBoundary : Set where
  constructor ternary-observer-boundary
  field
    memeClinicalLabelsAreFormalDiagnoses : Bool
    baselineObserverEqualsTruth : Bool
    patternDetectorEqualsParanoia : Bool
    adversarialObserverEqualsActualAdversary : Bool
    signPolarityHasIntrinsicMeaning : Bool
    allThreeObserversMayInspectSameEvidence : Bool
    observerRoleMayChangeOverTime : Bool

canonicalTernaryObserverBoundary : TernaryObserverBoundary
canonicalTernaryObserverBoundary = ternary-observer-boundary
  false false false false false true true
