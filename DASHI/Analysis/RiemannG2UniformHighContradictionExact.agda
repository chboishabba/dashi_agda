module DASHI.Analysis.RiemannG2UniformHighContradictionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.RiemannG2UniformLiteralPhaseHighProducerExact as Literal

record UniformHighContradictionProducer
    (analytic : Analytic.AnalyticSubstrate)
    (High : Universal.AnalyticNontrivialZero analytic -> Set) : Set₁ where
  field
    contradictionForOffLineHigh :
      (rho : Universal.AnalyticNontrivialZero analytic) ->
      High rho ->
      (Universal.analyticCritical rho -> ⊥) ->
      ⊥
    producerReference : String

open UniformHighContradictionProducer public

fromLiteralPhaseProducer :
  forall {analytic High} ->
  Literal.UniformLiteralPhaseHighProducer analytic High ->
  UniformHighContradictionProducer analytic High
fromLiteralPhaseProducer producer = record
  { contradictionForOffLineHigh =
      Literal.uniformLiteralPhaseHighContradiction producer
  ; producerReference =
      "compiled from UniformLiteralPhaseHighProducer"
  }

record UniformHighContradictionBoundary : Set where
  constructor uniform-high-contradiction-boundary
  field
    terminalHighConsumerNeedsLiteralPhaseImplementation : Bool
    terminalHighConsumerNeedsLiteralPhaseImplementationIsFalse :
      terminalHighConsumerNeedsLiteralPhaseImplementation ≡ false
    literalPhaseProducerCompilesGenericHighContradiction : Bool
    literalPhaseProducerCompilesGenericHighContradictionIsTrue :
      literalPhaseProducerCompilesGenericHighContradiction ≡ true
    fixedHighCaseSufficesForUniformProducer : Bool
    fixedHighCaseSufficesForUniformProducerIsFalse :
      fixedHighCaseSufficesForUniformProducer ≡ false
    genericHighContradictionAloneClaimsRH : Bool
    genericHighContradictionAloneClaimsRHIsFalse :
      genericHighContradictionAloneClaimsRH ≡ false
    highestAlphaReading : String

canonicalUniformHighContradictionBoundary : UniformHighContradictionBoundary
canonicalUniformHighContradictionBoundary =
  uniform-high-contradiction-boundary
    false refl
    true refl
    false refl
    false refl
    "Use one implementation-neutral high consumer: for every arbitrary high nontrivial zero, an off-critical-line assumption leads to contradiction. Direct literal-phase and proof-carrying certified-upper routes should compile to this same interface rather than forking the terminal high/low architecture. A fixed case is insufficient and RH is not derived here."
