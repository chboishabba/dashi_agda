module DASHI.Cognition.PNF.IndependentSentenceAdmissionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import DASHI.Cognition.PNF.ComplexityArithmetic using (_+ᶜ_)

------------------------------------------------------------------------
-- Physical sentence staging is not semantic authority.
--
-- The strict numeric runtime composes each sentence independently and then
-- transports that already-composed carrier through temporary PostgreSQL stage
-- relations. Reusing the stage RELATIONS is therefore admissible only when a
-- fresh-stage run and a reset/reused-stage run have exactly the same semantic
-- result. This is the proof obligation used by the session-local staging
-- optimisation; it does not identify or merge sentence fibres.
------------------------------------------------------------------------

record StagingTransparency
  (Sentence Input SemanticResult : Set)
  : Set₁ where
  field
    freshStageAdmission : Sentence → Input → SemanticResult
    reusedStageAdmission : Sentence → Input → SemanticResult
    transparent : ∀ sentence input →
      reusedStageAdmission sentence input ≡ freshStageAdmission sentence input

open StagingTransparency public

stageReusePreservesSentenceAdmission :
  ∀ {Sentence Input SemanticResult : Set}
    (law : StagingTransparency Sentence Input SemanticResult)
    (sentence : Sentence)
    (input : Input) →
  reusedStageAdmission law sentence input
  ≡ freshStageAdmission law sentence input
stageReusePreservesSentenceAdmission law sentence input =
  transparent law sentence input

------------------------------------------------------------------------
-- Fixed staging-setup exposure.
--
-- Recreating m physical stage relations for every one of n sentence fibres
-- introduces n copies of a cost that is independent of the sentence payload.
-- A session-reused physical carrier pays that setup once. These functions are
-- execution-cost witnesses only; they do not assign real wall-clock units.
------------------------------------------------------------------------

repeatedStageSetupExposure : Nat → Nat → Nat
repeatedStageSetupExposure zero setup = zero
repeatedStageSetupExposure (suc n) setup =
  setup +ᶜ repeatedStageSetupExposure n setup

reusedStageSetupExposure : Nat → Nat → Nat
reusedStageSetupExposure zero setup = zero
reusedStageSetupExposure (suc n) setup = setup

eightSentencesFiveFreshStages :
  repeatedStageSetupExposure 8 5 ≡ 40
eightSentencesFiveFreshStages = refl

eightSentencesFiveReusedStages :
  reusedStageSetupExposure 8 5 ≡ 5
eightSentencesFiveReusedStages = refl

------------------------------------------------------------------------
-- Stronger boundary for a future multi-sentence COPY / transaction batch.
--
-- Reusing empty physical relations does NOT by itself authorize batching the
-- semantic admission of different sentences. To amortize COPY startup or
-- transaction boundaries, the concrete implementation must establish that
-- admissions for disjoint sentence fibres commute and that batching is exactly
-- the same state transformation as the pointwise admissions.
------------------------------------------------------------------------

record IndependentSentenceAdmissions
  (Sentence Input State : Set)
  : Set₁ where
  field
    admit : Sentence → Input → State → State
    Distinct : Sentence → Sentence → Set
    commute :
      ∀ {left right leftInput rightInput state} →
      Distinct left right →
      admit left leftInput (admit right rightInput state)
      ≡
      admit right rightInput (admit left leftInput state)

open IndependentSentenceAdmissions public

record TwoSentenceBatchFactorization
  (Sentence Input State : Set)
  (law : IndependentSentenceAdmissions Sentence Input State)
  : Set₁ where
  field
    batchTwo : Sentence → Input → Sentence → Input → State → State
    factorizes :
      ∀ {left right leftInput rightInput state} →
      Distinct law left right →
      batchTwo left leftInput right rightInput state
      ≡
      admit law right rightInput (admit law left leftInput state)

open TwoSentenceBatchFactorization public

batchAdmissionEqualsPointwiseAdmission :
  ∀ {Sentence Input State : Set}
    {law : IndependentSentenceAdmissions Sentence Input State}
    (batch : TwoSentenceBatchFactorization Sentence Input State law)
    {left right : Sentence}
    {leftInput rightInput : Input}
    {state : State} →
    Distinct law left right →
  batchTwo batch left leftInput right rightInput state
  ≡
  admit law right rightInput (admit law left leftInput state)
batchAdmissionEqualsPointwiseAdmission batch distinct =
  factorizes batch distinct
