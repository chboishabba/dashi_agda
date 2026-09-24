module DASHI.Mathematics.Complexity.PNotEqualsNPPolynomialObserverNoGoExact where

------------------------------------------------------------------------
-- P != NP OBSERVER/COMPRESSION NO-GO RESULTS
--
-- This owner prunes two tempting but invalid lower-bound routes.
--
-- 1. "Polynomial-time representation" does NOT imply information loss.
--    PolynomialCostModel explicitly certifies the identity map as polynomial.
--
-- 2. Cook--Levin finite configuration encodings do NOT imply information
--    loss.  FiniteConfigurationCodec supplies decode(encode(c)) = c, hence
--    encode is injective.
--
-- Therefore neither polynomial representability nor lossless finite tableau
-- encoding can, by itself, force the SAT/UNSAT collision needed by
-- PNotEqualsNPDirectSATLowerBoundExact.
--
-- Any successful observer route must prove an additional, genuinely
-- non-injective / SAT-insufficient resource theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.Nat.Base using (z≤n)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.FiniteConfigurationEncodingExact as Finite
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PolynomialFactorisationCostExact as Factor
import DASHI.Mathematics.Complexity.PolynomialClassicalObserverExact as PolyObserver
import DASHI.Core.EfficientRecoverableQuotientExact as ERQ
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct

Injective :
  ∀ {A B : Set} →
  (A → B) → Set
Injective map =
  ∀ {left right} →
  map left ≡ map right →
  left ≡ right

identityInjective :
  ∀ {A : Set} →
  Injective (λ (value : A) → value)
identityInjective same = same

------------------------------------------------------------------------
-- Polynomial-time representation alone cannot force compression.
------------------------------------------------------------------------

polynomialIdentityRepresentationIsLossless :
  ∀ {Word : Set}
    (cost : PR.PolynomialCostModel Word) →
  PR.polynomialTimeMap cost (λ word → word)
  × Injective (λ (word : Word) → word)
polynomialIdentityRepresentationIsLossless cost =
  PR.identityMapPolynomial cost , identityInjective

------------------------------------------------------------------------
-- Injective observers cannot carry a consumer non-descent witness.
------------------------------------------------------------------------

injectiveObserverBlocksConsumerNonDescent :
  ∀ {State Surface Outcome : Set}
    {observe : State → Surface}
    {consumer : State → Outcome} →
  Injective observe →
  Descent.ConsumerNonDescentWitness observe consumer →
  ⊥
injectiveObserverBlocksConsumerNonDescent injective witness =
  Descent.differentOutcome witness
    (cong consumer
      (injective
        (Descent.sameSurface witness)))

------------------------------------------------------------------------
-- Lossless finite configuration codecs are injective.
------------------------------------------------------------------------

finiteConfigurationEncodingIsInjective :
  ∀ {Configuration : Set}
    (codec : Finite.FiniteConfigurationCodec Configuration) →
  Injective (Finite.encode codec)
finiteConfigurationEncodingIsInjective codec {left} {right} sameEncoding =
  trans
    (sym (Finite.decodeEncode codec left))
    (trans
      (cong (Finite.decode codec) sameEncoding)
      (Finite.decodeEncode codec right))

finiteConfigurationEncodingCannotCauseNonDescent :
  ∀ {Configuration Outcome : Set}
    (codec : Finite.FiniteConfigurationCodec Configuration)
    (consumer : Configuration → Outcome) →
  Descent.ConsumerNonDescentWitness
    (Finite.encode codec)
    consumer →
  ⊥
finiteConfigurationEncodingCannotCauseNonDescent codec consumer =
  injectiveObserverBlocksConsumerNonDescent
    (finiteConfigurationEncodingIsInjective codec)

------------------------------------------------------------------------
-- SAT-specific consequence.
--
-- An injective formula observer cannot identify a satisfiable formula with an
-- unsatisfiable formula.  This requires no SAT decider and no excluded middle.
------------------------------------------------------------------------

injectiveFormulaObserverCannotCollapseSATAndUNSAT :
  ∀ {Surface : Set}
    {observe : Cook.BooleanFormula → Surface} →
  Injective observe →
  (satisfiableFormula unsatisfiableFormula : Cook.BooleanFormula) →
  Cook.Satisfiable satisfiableFormula →
  (Cook.Satisfiable unsatisfiableFormula → ⊥) →
  observe satisfiableFormula ≡ observe unsatisfiableFormula →
  ⊥
injectiveFormulaObserverCannotCollapseSATAndUNSAT
    injective satisfiableFormula unsatisfiableFormula
    satisfiableWitness unsatisfiableWitness sameObservation =
  unsatisfiableWitness
    (transportSatisfiable
      (injective sameObservation)
      satisfiableWitness)
  where
    transportSatisfiable :
      ∀ {left right : Cook.BooleanFormula} →
      left ≡ right →
      Cook.Satisfiable left →
      Cook.Satisfiable right
    transportSatisfiable refl witness = witness

------------------------------------------------------------------------
-- Factorization through an injective representation is compatible with
-- arbitrary consumers, so factorization itself is not a lower bound.
------------------------------------------------------------------------

identityFactorization :
  ∀ {Word : Set}
    (consumer : Word → Bool) →
  (word : Word) →
  consumer word ≡ consumer ((λ value → value) word)
identityFactorization consumer word = refl


------------------------------------------------------------------------
-- Coverage alone is vacuous: every polynomial candidate factors through the
-- identity observer with polynomial observer and downstream costs.
------------------------------------------------------------------------

identityCostAwareFactorisation :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost) →
  Factor.CostAwareDecisionFactorisation
    cost
    (Direct.decide candidate)
identityCostAwareFactorisation {cost = cost} candidate = record
  { Factor.observe = λ formula → formula
  ; Factor.consumeObserved = Direct.decide candidate
  ; Factor.factorisationCorrect = λ formula → refl
  ; Factor.observerPolynomial = PR.identityMapPolynomial cost
  ; Factor.observedConsumerPolynomial =
      Direct.polynomialDecision candidate
  }

identityFactorisationObserverIsInjective :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost) →
  Injective
    (Factor.observe
      (identityCostAwareFactorisation candidate))
identityFactorisationObserverIsInjective candidate =
  identityInjective

identityFactorisationCannotProvideSATRelevantLoss :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost) →
  (satisfiableFormula unsatisfiableFormula : Cook.BooleanFormula) →
  Cook.Satisfiable satisfiableFormula →
  (Cook.Satisfiable unsatisfiableFormula → ⊥) →
  Factor.observe
      (identityCostAwareFactorisation candidate)
      satisfiableFormula
    ≡
  Factor.observe
      (identityCostAwareFactorisation candidate)
      unsatisfiableFormula →
  ⊥
identityFactorisationCannotProvideSATRelevantLoss
    candidate satisfiableFormula unsatisfiableFormula
    satisfiableWitness unsatisfiableWitness =
  injectiveFormulaObserverCannotCollapseSATAndUNSAT
    (identityFactorisationObserverIsInjective candidate)
    satisfiableFormula
    unsatisfiableFormula
    satisfiableWitness
    unsatisfiableWitness


------------------------------------------------------------------------
-- The full PolynomialClassicalObserver carrier is also permissive enough to
-- admit a lossless identity observer with zero-valued supplied measurements.
--
-- This is an important modelling result: the observer record's polynomial
-- envelopes do not, by themselves, prove that representationSize,
-- constructionCost, or recoveryCost are faithful operational measurements.
------------------------------------------------------------------------

zeroPolynomialBound :
  ERQ.PolynomialBound (λ n → zero)
zeroPolynomialBound =
  ERQ.polynomialBound zero zero (λ n → z≤n)

zeroLengthIndexedEnvelope :
  ∀ {Word : Set}
    {inputLength : Word → Nat} →
  PolyObserver.LengthIndexedEnvelope
    inputLength
    (λ word → zero)
zeroLengthIndexedEnvelope = record
  { PolyObserver.envelope = λ n → zero
  ; PolyObserver.dominates = λ word → z≤n
  ; PolyObserver.polynomial = zeroPolynomialBound
  }

identityPolynomialClassicalObserver :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost) →
  PolyObserver.PolynomialClassicalObserver
    cost
    (Direct.decide candidate)
identityPolynomialClassicalObserver {cost = cost} candidate = record
  { PolyObserver.inputLength = λ formula → zero
  ; PolyObserver.representation = λ formula → formula
  ; PolyObserver.representationSize = λ formula → zero
  ; PolyObserver.constructionCost = λ formula → zero
  ; PolyObserver.recoverDecision = Direct.decide candidate
  ; PolyObserver.recoveryCost = λ formula → zero
  ; PolyObserver.representationSizeBound = zeroLengthIndexedEnvelope
  ; PolyObserver.constructionCostBound = zeroLengthIndexedEnvelope
  ; PolyObserver.recoveryCostBound = zeroLengthIndexedEnvelope
  ; PolyObserver.representationPolynomial = PR.identityMapPolynomial cost
  ; PolyObserver.recoveryPolynomial = Direct.polynomialDecision candidate
  ; PolyObserver.consumerFactors = λ formula → refl
  }

identityPolynomialClassicalObserverIsInjective :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost) →
  Injective
    (PolyObserver.representation
      (identityPolynomialClassicalObserver candidate))
identityPolynomialClassicalObserverIsInjective candidate =
  identityInjective

identityPolynomialClassicalObserverCannotCollapseSATAndUNSAT :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost) →
  (satisfiableFormula unsatisfiableFormula : Cook.BooleanFormula) →
  Cook.Satisfiable satisfiableFormula →
  (Cook.Satisfiable unsatisfiableFormula → ⊥) →
  PolyObserver.representation
      (identityPolynomialClassicalObserver candidate)
      satisfiableFormula
    ≡
  PolyObserver.representation
      (identityPolynomialClassicalObserver candidate)
      unsatisfiableFormula →
  ⊥
identityPolynomialClassicalObserverCannotCollapseSATAndUNSAT
    candidate satisfiableFormula unsatisfiableFormula
    satisfiableWitness unsatisfiableWitness =
  injectiveFormulaObserverCannotCollapseSATAndUNSAT
    (identityPolynomialClassicalObserverIsInjective candidate)
    satisfiableFormula
    unsatisfiableFormula
    satisfiableWitness
    unsatisfiableWitness
