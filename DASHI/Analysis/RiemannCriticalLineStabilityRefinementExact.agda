module DASHI.Analysis.RiemannCriticalLineStabilityRefinementExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥; ⊥-elim)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal

------------------------------------------------------------------------
-- CRITICAL-LINE STABILITY AS AN OBSERVER-REFINEMENT PROBLEM
--
-- A contradiction from an assumed off-line zero gives
--
--   ¬ ¬ criticalLine(s).
--
-- The prize-facing consumer asks for
--
--   criticalLine(s).
--
-- On the current AnalyticSubstrate, `criticalLine` is an arbitrary predicate
-- field.  Therefore double-negation elimination is not available merely from
-- the name "critical line".  The missing coordinate is the representation that
-- explains what this predicate actually is and why that concrete predicate is
-- stable.
--
-- This module supplies exactly that compiler and nothing classical by fiat.
------------------------------------------------------------------------

Not : Set -> Set
Not P = P -> ⊥

record CriticalLinePredicateRefinement
    (analytic : Analytic.AnalyticSubstrate) : Set₁ where
  private
    Complex =
      Analytic.ComplexAnalyticCarrier.Complex
        (Analytic.AnalyticSubstrate.carrier analytic)
    abstractCritical =
      Analytic.CompletedRiemannZeta.criticalLine
        (Analytic.AnalyticSubstrate.completed analytic)
  field
    RefinedCritical : Complex -> Set

    abstractImpliesRefined :
      (s : Complex) -> abstractCritical s -> RefinedCritical s

    refinedImpliesAbstract :
      (s : Complex) -> RefinedCritical s -> abstractCritical s

    refinedCriticalStable :
      (s : Complex) -> Not (Not (RefinedCritical s)) -> RefinedCritical s

    sameCompletedZetaPredicateReceipt : Set
    sameCompletedZetaPredicateReceiptWitness :
      sameCompletedZetaPredicateReceipt

    refinementReference : String

open CriticalLinePredicateRefinement public

compileCriticalLineStable :
  forall {analytic} ->
  CriticalLinePredicateRefinement analytic ->
  Universal.CriticalLineStable analytic
compileCriticalLineStable {analytic} refinement s nnAbstract =
  refinedImpliesAbstract refinement s
    (refinedCriticalStable refinement s nnRefined)
  where
  abstractCritical : Set
  abstractCritical =
    Analytic.CompletedRiemannZeta.criticalLine
      (Analytic.AnalyticSubstrate.completed analytic) s

  refinedCritical : Set
  refinedCritical = RefinedCritical refinement s

  nnRefined : Not (Not refinedCritical)
  nnRefined notRefined =
    nnAbstract
      (λ abstractProof ->
        notRefined (abstractImpliesRefined refinement s abstractProof))

------------------------------------------------------------------------
-- A decidable refined predicate is one sufficient constructive producer of
-- stability.  This is local decidability of the exact refined predicate, not a
-- global excluded-middle axiom.
------------------------------------------------------------------------

data LocalDecision (P : Set) : Set where
  yes : P -> LocalDecision P
  no : Not P -> LocalDecision P

stableFromLocalDecision :
  forall {P} -> LocalDecision P -> Not (Not P) -> P
stableFromLocalDecision (yes proof) nnP = proof
stableFromLocalDecision (no notP) nnP = ⊥-elim (nnP notP)

record DecidableCriticalLinePredicateRefinement
    (analytic : Analytic.AnalyticSubstrate) : Set₁ where
  private
    Complex =
      Analytic.ComplexAnalyticCarrier.Complex
        (Analytic.AnalyticSubstrate.carrier analytic)
    abstractCritical =
      Analytic.CompletedRiemannZeta.criticalLine
        (Analytic.AnalyticSubstrate.completed analytic)
  field
    RefinedCritical : Complex -> Set

    abstractImpliesRefined :
      (s : Complex) -> abstractCritical s -> RefinedCritical s

    refinedImpliesAbstract :
      (s : Complex) -> RefinedCritical s -> abstractCritical s

    decideRefinedCritical :
      (s : Complex) -> LocalDecision (RefinedCritical s)

    sameCompletedZetaPredicateReceipt : Set
    sameCompletedZetaPredicateReceiptWitness :
      sameCompletedZetaPredicateReceipt

    refinementReference : String

open DecidableCriticalLinePredicateRefinement public

fromDecidableRefinement :
  forall {analytic} ->
  DecidableCriticalLinePredicateRefinement analytic ->
  CriticalLinePredicateRefinement analytic
fromDecidableRefinement refinement = record
  { CriticalLinePredicateRefinement.RefinedCritical =
      DecidableCriticalLinePredicateRefinement.RefinedCritical refinement
  ; CriticalLinePredicateRefinement.abstractImpliesRefined =
      DecidableCriticalLinePredicateRefinement.abstractImpliesRefined refinement
  ; CriticalLinePredicateRefinement.refinedImpliesAbstract =
      DecidableCriticalLinePredicateRefinement.refinedImpliesAbstract refinement
  ; CriticalLinePredicateRefinement.refinedCriticalStable =
      λ s -> stableFromLocalDecision
        (DecidableCriticalLinePredicateRefinement.decideRefinedCritical refinement s)
  ; CriticalLinePredicateRefinement.sameCompletedZetaPredicateReceipt =
      DecidableCriticalLinePredicateRefinement.sameCompletedZetaPredicateReceipt refinement
  ; CriticalLinePredicateRefinement.sameCompletedZetaPredicateReceiptWitness =
      DecidableCriticalLinePredicateRefinement.sameCompletedZetaPredicateReceiptWitness refinement
  ; CriticalLinePredicateRefinement.refinementReference =
      DecidableCriticalLinePredicateRefinement.refinementReference refinement
  }

compileDecidableCriticalLineStable :
  forall {analytic} ->
  DecidableCriticalLinePredicateRefinement analytic ->
  Universal.CriticalLineStable analytic
compileDecidableCriticalLineStable refinement =
  compileCriticalLineStable (fromDecidableRefinement refinement)

------------------------------------------------------------------------
-- Firewalls and current boundary.
------------------------------------------------------------------------

data ArbitraryPredicateNamePaysStability : Set where

data CarrierIdentityAlonePaysStability : Set where

arbitraryPredicateNameDoesNotPayStability :
  ArbitraryPredicateNamePaysStability -> ⊥
arbitraryPredicateNameDoesNotPayStability ()

carrierIdentityAloneDoesNotPayStability :
  CarrierIdentityAlonePaysStability -> ⊥
carrierIdentityAloneDoesNotPayStability ()

record CriticalLineStabilityRefinementBoundary : Set where
  constructor critical-line-stability-refinement-boundary
  field
    abstractCriticalLinePredicateAutomaticallyStable : Bool
    abstractCriticalLinePredicateAutomaticallyStableIsFalse :
      abstractCriticalLinePredicateAutomaticallyStable ≡ false

    wholeComplexCarrierIdentityAloneProvesPredicateStability : Bool
    wholeComplexCarrierIdentityAloneProvesPredicateStabilityIsFalse :
      wholeComplexCarrierIdentityAloneProvesPredicateStability ≡ false

    exactPredicateRefinementPlusStabilityCompilesConsumerReceipt : Bool
    exactPredicateRefinementPlusStabilityCompilesConsumerReceiptIsTrue :
      exactPredicateRefinementPlusStabilityCompilesConsumerReceipt ≡ true

    localDecidabilityOfExactRefinedPredicateIsSufficient : Bool
    localDecidabilityOfExactRefinedPredicateIsSufficientIsTrue :
      localDecidabilityOfExactRefinedPredicateIsSufficient ≡ true

    globalExcludedMiddleIntroducedHere : Bool
    globalExcludedMiddleIntroducedHereIsFalse :
      globalExcludedMiddleIntroducedHere ≡ false

    canonicalActualZetaPredicateRefinementInhabitedHere : Bool
    canonicalActualZetaPredicateRefinementInhabitedHereIsFalse :
      canonicalActualZetaPredicateRefinementInhabitedHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalCriticalLineStabilityRefinementBoundary :
  CriticalLineStabilityRefinementBoundary
canonicalCriticalLineStabilityRefinementBoundary =
  critical-line-stability-refinement-boundary
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
    "The high-side contradiction naturally yields double-negated criticality. Because AnalyticSubstrate stores criticalLine as an arbitrary predicate, its stability is not automatic. Refine that observer by identifying the exact completed-zeta criticalLine predicate with a concrete predicate that is itself stable; equivalently, a locally decidable exact refinement is sufficient. The compiler then produces CriticalLineStable constructively. Whole complex-carrier identity alone is insufficient because it does not identify the predicate. No global excluded middle, postulate, or RH theorem is introduced here."
