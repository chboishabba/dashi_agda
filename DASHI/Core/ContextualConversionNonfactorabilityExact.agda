module DASHI.Core.ContextualConversionNonfactorabilityExact where

open import DASHI.Core.Prelude
import DASHI.Core.ConsumerDescentMinimalObserverExact as Consumer

------------------------------------------------------------------------
-- CONTEXTUAL CONVERSION / REALISATION NON-FACTORABILITY
--
-- Generic theorem shape shared by provisioning, situated accessibility,
-- embodied reachability and other DASHI lanes:
--
--   input × conversion context -> realised outcome
--
-- If two states retain the same input while context changes the realised
-- outcome, then the realised outcome cannot factor through the input observer
-- alone.  This is deliberately domain-neutral: no causal, economic, clinical
-- or political semantics are built into the theorem.
------------------------------------------------------------------------

record ContextualConversion
    (Input Context Output : Set) : Set where
  constructor contextualConversion
  field
    realise : Input × Context → Output

open ContextualConversion public

inputObserver :
  ∀ {Input Context : Set} →
  Input × Context → Input
inputObserver = proj₁

record ContextEssentialWitness
    {Input Context Output : Set}
    (conversion : ContextualConversion Input Context Output) : Set where
  constructor contextEssentialWitness
  field
    input : Input
    leftContext rightContext : Context
    differentRealisation :
      realise conversion (input , leftContext) ≡
      realise conversion (input , rightContext) → ⊥

open ContextEssentialWitness public

contextEssentialGivesConsumerNonDescent :
  ∀ {Input Context Output : Set}
    {conversion : ContextualConversion Input Context Output} →
  ContextEssentialWitness conversion →
  Consumer.ConsumerNonDescentWitness
    inputObserver
    (realise conversion)
contextEssentialGivesConsumerNonDescent witness =
  Consumer.consumerNonDescentWitness
    (input witness , leftContext witness)
    (input witness , rightContext witness)
    refl
    (differentRealisation witness)

contextEssentialBlocksInputSufficiency :
  ∀ {Input Context Output : Set}
    {conversion : ContextualConversion Input Context Output} →
  ContextEssentialWitness conversion →
  Consumer.ConsumerSufficient inputObserver (realise conversion) →
  ⊥
contextEssentialBlocksInputSufficiency witness =
  Consumer.nonDescentWitnessBlocksSufficiency
    (contextEssentialGivesConsumerNonDescent witness)

contextEssentialBlocksInputFactorization :
  ∀ {Input Context Output : Set}
    {conversion : ContextualConversion Input Context Output} →
  ContextEssentialWitness conversion →
  Consumer.FactorsThrough inputObserver (realise conversion) →
  ⊥
contextEssentialBlocksInputFactorization witness =
  Consumer.nonDescentWitnessBlocksFactorization
    (contextEssentialGivesConsumerNonDescent witness)

record ContextualConversionBoundary : Set where
  constructor contextualConversionBoundary
  field
    sameInputMayRealiseDifferentOutcomes : Bool
    contextEssentialBlocksInputOnlyFactorization : Bool
    contextDifferenceIsByItselfCausalIdentification : Bool
    oneDomainWitnessDefinesEveryConversionMechanism : Bool

canonicalContextualConversionBoundary : ContextualConversionBoundary
canonicalContextualConversionBoundary =
  contextualConversionBoundary true true false false
