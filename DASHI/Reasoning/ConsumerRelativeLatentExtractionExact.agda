module DASHI.Reasoning.ConsumerRelativeLatentExtractionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Cognition.PNF.DecisionActionProjectionNonFactorabilityExact as Decision

------------------------------------------------------------------------
-- CONSUMER-RELATIVE LATENT EXTRACTION
--
-- A latent coordinate L can be extracted from an observation Q exactly when
-- the target factors through that observation:
--
--   L = decode ∘ Q.
--
-- This is intentionally just an alias/weld over the existing generic
-- factorability calculus.  No new inverse-problem mathematics is introduced.
------------------------------------------------------------------------

CanExtractLatent :
  ∀ {State Observation Latent : Set} →
  (observe : State → Observation) →
  (latent : State → Latent) →
  Set₁
CanExtractLatent = NF.FactorsThrough

record LatentExtractionContract
    {State Observation Latent : Set}
    (observe : State → Observation)
    (latent : State → Latent) : Set₁ where
  constructor latent-extraction-contract
  field
    decoder : Observation → Latent
    exactDecode : (state : State) → latent state ≡ decoder (observe state)
    consumerLabel : String
    latentLabel : String
    receipt : String

open LatentExtractionContract public

contractToFactorsThrough :
  ∀ {State Observation Latent}
    {observe : State → Observation}
    {latent : State → Latent} →
  LatentExtractionContract observe latent →
  CanExtractLatent observe latent
contractToFactorsThrough contract =
  NF.factorsThrough
    (decoder contract)
    (exactDecode contract)

factorsThroughToContract :
  ∀ {State Observation Latent}
    {observe : State → Observation}
    {latent : State → Latent} →
  String → String → String →
  CanExtractLatent observe latent →
  LatentExtractionContract observe latent
factorsThroughToContract consumer latentLabel receipt factor =
  latent-extraction-contract
    (NF.interpretFlat factor)
    (NF.factorisation factor)
    consumer
    latentLabel
    receipt

nonfactorabilityBlocksLatentExtraction :
  ∀ {State Observation Latent}
    {observe : State → Observation}
    {latent : State → Latent} →
  NF.NonFactorabilityWitness observe latent →
  CanExtractLatent observe latent →
  ⊥
nonfactorabilityBlocksLatentExtraction =
  NF.witnessRulesOutEveryFlatFactorisation

postprocessingCannotRecoverErasedLatent :
  ∀ {State Observation Recharted Latent}
    {observe : State → Observation}
    {latent : State → Latent} →
  (rechart : Observation → Recharted) →
  NF.NonFactorabilityWitness observe latent →
  CanExtractLatent (λ state → rechart (observe state)) latent →
  ⊥
postprocessingCannotRecoverErasedLatent =
  NF.rechartingCannotRecoverErasedPhenomenon

------------------------------------------------------------------------
-- Paid cognition instance: action does not decode the fine decision state.
------------------------------------------------------------------------

decisionFineStateNotExtractableFromAction :
  CanExtractLatent Decision.observedAction Decision.fineDecisionState → ⊥
decisionFineStateNotExtractableFromAction =
  Decision.actionCannotRecoverFineDecisionState

decisionActionNonfactorabilityWitness :
  NF.NonFactorabilityWitness Decision.observedAction Decision.fineDecisionState
decisionActionNonfactorabilityWitness = Decision.actionProjectionWitness

------------------------------------------------------------------------
-- Minimality boundary.
------------------------------------------------------------------------

data ConsumerMinimalityImpliesPhysicalMinimality : Set where

consumerMinimalityDoesNotEstablishPhysicalMinimality :
  ConsumerMinimalityImpliesPhysicalMinimality → ⊥
consumerMinimalityDoesNotEstablishPhysicalMinimality ()

record LatentExtractionFrontier : Set where
  constructor latent-extraction-frontier
  field
    exactFactorisationIsExtractionCriterion : Bool
    exactFactorisationIsExtractionCriterionIsTrue :
      exactFactorisationIsExtractionCriterion ≡ true

    decisionFineStateExtractionFromActionPaid : Bool
    decisionFineStateExtractionFromActionPaidIsFalse :
      decisionFineStateExtractionFromActionPaid ≡ false

    rememberedEventExtractionPaid : Bool
    rememberedEventExtractionPaidIsFalse :
      rememberedEventExtractionPaid ≡ false

    memoryInfluenceExtractionPaid : Bool
    memoryInfluenceExtractionPaidIsFalse :
      memoryInfluenceExtractionPaid ≡ false

    motorPolicyExtractionPaid : Bool
    motorPolicyExtractionPaidIsFalse :
      motorPolicyExtractionPaid ≡ false

    latentDecoderMayBeConsumerSpecific : Bool
    latentDecoderMayBeConsumerSpecificIsTrue :
      latentDecoderMayBeConsumerSpecific ≡ true

    postprocessingA lossyObservationRecoversErasedLatent : Bool
    postprocessingA lossyObservationRecoversErasedLatentIsFalse :
      postprocessingA lossyObservationRecoversErasedLatent ≡ false

    consumerMinimalCodeIdentifiesPhysicalLatentDimension : Bool
    consumerMinimalCodeIdentifiesPhysicalLatentDimensionIsFalse :
      consumerMinimalCodeIdentifiesPhysicalLatentDimension ≡ false

    interpretation : String

open LatentExtractionFrontier public

canonicalLatentExtractionFrontier : LatentExtractionFrontier
canonicalLatentExtractionFrontier = latent-extraction-frontier
  true refl
  false refl
  false refl
  false refl
  false refl
  true refl
  false refl
  false refl
  "Latent extraction is consumer-relative factorisation. A decoder is paid only when the requested latent coordinate factors through the declared observation. Existing action non-factorability already blocks exact recovery of fine decision state from action alone. Memory-event, memory-influence, and motor-policy extraction remain separate unpaid obligations. Minimality for one consumer does not identify a physically minimal neural state or latent dimension."
