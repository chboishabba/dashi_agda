module DASHI.Core.ConsumerIndexedTranslationRealisationExact where

------------------------------------------------------------------------
-- CONSUMER-INDEXED TRANSLATION / REALISATION ADEQUACY
--
-- Cross-pollinated theorem pattern from draft PRs #615, #621, #625, #608 and
-- #602.  A representation can be adequate for one consumer and inadequate for
-- another; translation, reconstruction/realisation, semantic authority and
-- physical execution remain separate proof obligations.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

record TranslationRealisationSystem : Set₁ where
  constructor translationRealisationSystem
  field
    Source : Set
    Representation : Set
    Realized : Set
    Consumer : Set
    Outcome : Consumer → Set

    translate : Source → Representation
    realize : Representation → Realized
    observe : (consumer : Consumer) → Realized → Outcome consumer

    FaithfulTranslation : Source → Set
    AdequateRealisation : Representation → Set
    ConsumerSufficient : (consumer : Consumer) → Realized → Set

open TranslationRealisationSystem public

AdequateFor :
  (system : TranslationRealisationSystem) →
  (source : Source system) →
  (consumer : Consumer system) → Set
AdequateFor system source consumer =
  FaithfulTranslation system source ×
  (AdequateRealisation system (translate system source) ×
   ConsumerSufficient system consumer
     (realize system (translate system source)))

record ConsumerRelativeAdequacyWitness
    (system : TranslationRealisationSystem)
    (source : Source system)
    (good bad : Consumer system) : Set₁ where
  constructor consumerRelativeAdequacyWitness
  field
    adequateForGood : AdequateFor system source good
    inadequateForBad : AdequateFor system source bad → ⊥

open ConsumerRelativeAdequacyWitness public

adequateForOneConsumerDoesNotGlobalise :
  (system : TranslationRealisationSystem) →
  (source : Source system) →
  (good bad : Consumer system) →
  ConsumerRelativeAdequacyWitness system source good bad →
  (AdequateFor system source good → AdequateFor system source bad) → ⊥
adequateForOneConsumerDoesNotGlobalise system source good bad witness promote =
  inadequateForBad witness (promote (adequateForGood witness))

------------------------------------------------------------------------
-- Stage-indexed adequacy matrix.
------------------------------------------------------------------------

data AdequacyStage : Set where
  sourceAcquired
  translated
  reconstructed
  realized
  kernelChecked
  empiricallyCalibrated
  normativelyAdmitted
  : AdequacyStage

record StageConsumerAdequacy (Consumer : Set) : Set₁ where
  constructor stageConsumerAdequacy
  field
    Adequate : AdequacyStage → Consumer → Set

open StageConsumerAdequacy public

record StageConsumerSeparation
    {Consumer : Set}
    (matrix : StageConsumerAdequacy Consumer) : Set₁ where
  constructor stageConsumerSeparation
  field
    stage : AdequacyStage
    goodConsumer badConsumer : Consumer
    goodEvidence : Adequate matrix stage goodConsumer
    badFailure : Adequate matrix stage badConsumer → ⊥

------------------------------------------------------------------------
-- Canonical finite witness: the same realized artifact is adequate for a
-- structural consumer but not for an empirical consumer.
------------------------------------------------------------------------

data DemoSource : Set where sourceText : DemoSource
data DemoRepresentation : Set where typedModel : DemoRepresentation
data DemoRealized : Set where checkedArtifact : DemoRealized
data DemoConsumer : Set where structuralConsumer empiricalConsumer : DemoConsumer
data DemoOutcome : DemoConsumer → Set where
  structuralOutcome : DemoOutcome structuralConsumer
  empiricalOutcome : DemoOutcome empiricalConsumer

data DemoFaithful : DemoSource → Set where faithfulSource : DemoFaithful sourceText
data DemoRealisation : DemoRepresentation → Set where realizedModel : DemoRealisation typedModel
data DemoSufficient : (consumer : DemoConsumer) → DemoRealized → Set where
  structuralSufficient : DemoSufficient structuralConsumer checkedArtifact

demoSystem : TranslationRealisationSystem
demoSystem = translationRealisationSystem
  DemoSource DemoRepresentation DemoRealized DemoConsumer DemoOutcome
  (λ { sourceText → typedModel })
  (λ { typedModel → checkedArtifact })
  (λ { structuralConsumer checkedArtifact → structuralOutcome
     ; empiricalConsumer checkedArtifact → empiricalOutcome })
  DemoFaithful DemoRealisation DemoSufficient

demoAdequateStructural : AdequateFor demoSystem sourceText structuralConsumer
demoAdequateStructural = faithfulSource , (realizedModel , structuralSufficient)

demoNotAdequateEmpirical : AdequateFor demoSystem sourceText empiricalConsumer → ⊥
demoNotAdequateEmpirical (_ , (_ , ()))

demoConsumerRelative :
  ConsumerRelativeAdequacyWitness demoSystem sourceText structuralConsumer empiricalConsumer
demoConsumerRelative = consumerRelativeAdequacyWitness
  demoAdequateStructural demoNotAdequateEmpirical

record TranslationRealisationBoundary : Set where
  constructor translationRealisationBoundary
  field
    syntacticValidityImpliesHistoricalAdequacy : Bool
    syntacticValidityImpliesHistoricalAdequacyIsFalse :
      syntacticValidityImpliesHistoricalAdequacy ≡ false
    historicalAdequacyImpliesExecutability : Bool
    historicalAdequacyImpliesExecutabilityIsFalse :
      historicalAdequacyImpliesExecutability ≡ false
    executabilityImpliesEveryConsumerSufficient : Bool
    executabilityImpliesEveryConsumerSufficientIsFalse :
      executabilityImpliesEveryConsumerSufficient ≡ false
    adequateForOneConsumerImpliesAdequateForEveryConsumer : Bool
    adequateForOneConsumerImpliesAdequateForEveryConsumerIsFalse :
      adequateForOneConsumerImpliesAdequateForEveryConsumer ≡ false
    outcomeMatchImpliesCausalIdentification : Bool
    outcomeMatchImpliesCausalIdentificationIsFalse :
      outcomeMatchImpliesCausalIdentification ≡ false

canonicalTranslationRealisationBoundary : TranslationRealisationBoundary
canonicalTranslationRealisationBoundary =
  translationRealisationBoundary false refl false refl false refl false refl false refl
