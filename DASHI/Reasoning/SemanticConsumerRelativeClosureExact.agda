module DASHI.Reasoning.SemanticConsumerRelativeClosureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.BidiResidualApproximationExact as Bidi
import DASHI.Core.PredictionEnvelopeExact as Envelope
import DASHI.Core.DiscriminatorSynthesisExact as Discriminator
import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as Candidate
import DASHI.Reasoning.SemanticCandidateResidualBidiExact as Semantic

------------------------------------------------------------------------
-- CONSUMER-RELATIVE SEMANTIC CLOSURE
--
-- Full semantic point identification is stronger than many downstream tasks
-- require.  If every currently live semantic candidate yields the same
-- declared consumer result, that consumer is closed even while semantic
-- ambiguity remains.  This is the language-side instantiation of the generic
-- prediction-envelope / consumer-relative closure geometry.
------------------------------------------------------------------------

SemanticConsumer : Set → Set₁
SemanticConsumer Decision = Candidate.CandidateSemanticFragment → Decision

ConsumerClosedOnSemanticFibre :
  ∀ {Decision : Set} →
  Candidate.CandidateSemanticFibre →
  SemanticConsumer Decision →
  Set
ConsumerClosedOnSemanticFibre fibre consumer =
  Bidi.PointIdentifies
    (Semantic.semanticCandidateFibre fibre)
    consumer

record SemanticConsumerClosure
    {Decision : Set}
    (fibre : Candidate.CandidateSemanticFibre)
    (consumer : SemanticConsumer Decision) : Set₁ where
  constructor semanticConsumerClosure
  field
    closed : ConsumerClosedOnSemanticFibre fibre consumer
    consumerReference : String
    closureReference : String
    unresolvedSemanticReference : String

open SemanticConsumerClosure public

------------------------------------------------------------------------
-- Closure may survive residual refinement: removing live candidates cannot
-- create a consumer disagreement that was absent on the larger fibre.
------------------------------------------------------------------------

closurePersistsUnderSemanticRefinement :
  ∀ {Decision : Set}
    {prior posterior : Bidi.ResidualFibre Candidate.CandidateSemanticFragment}
    {consumer : Candidate.CandidateSemanticFragment → Decision} →
  Bidi.FibreRefines posterior prior →
  Bidi.PointIdentifies prior consumer →
  Bidi.PointIdentifies posterior consumer
closurePersistsUnderSemanticRefinement refines closed left right leftLive rightLive =
  closed left right (refines left leftLive) (refines right rightLive)

------------------------------------------------------------------------
-- The generic discriminator owner already defines prospective closure of a
-- declared consumer after measurement.  This bridge simply gives that concept
-- its semantic reading; no new experiment ontology is introduced.
------------------------------------------------------------------------

record SemanticConsumerClosingProbe
    {Evidence Decision : Set}
    (compatible : Envelope.Compatible Evidence Candidate.CandidateSemanticFragment)
    (consumer : Candidate.CandidateSemanticFragment → Decision) : Set₁ where
  constructor semanticConsumerClosingProbe
  field
    probe : Discriminator.ExperimentBundle Candidate.CandidateSemanticFragment
    prospectivelyCloses :
      Discriminator.ProspectivelyClosesConsumer compatible consumer probe
    sourceOrContextProbeReference : String
    calibrationReference : String
    consumerReference : String

open SemanticConsumerClosingProbe public

------------------------------------------------------------------------
-- Finite exact regression: semantic ambiguity can remain while the consumer
-- is already constant.  This intentionally uses synthetic candidates rather
-- than pretending to be a materialised SensiBlaw run.
------------------------------------------------------------------------

data ToySemantic : Set where
  readingA readingB readingC : ToySemantic

data ToyDecision : Set where
  sameDecision differentDecision : ToyDecision

ToyFibre : ToySemantic → Set
ToyFibre readingA = ⊤
ToyFibre readingB = ⊤
ToyFibre readingC = ⊥

toyConsumer : ToySemantic → ToyDecision
toyConsumer readingA = sameDecision
toyConsumer readingB = sameDecision
toyConsumer readingC = differentDecision

toyConsumerClosedWithTwoLiveReadings :
  Bidi.PointIdentifies ToyFibre toyConsumer
toyConsumerClosedWithTwoLiveReadings readingA readingA liveL liveR = refl
toyConsumerClosedWithTwoLiveReadings readingA readingB liveL liveR = refl
toyConsumerClosedWithTwoLiveReadings readingA readingC liveL ()
toyConsumerClosedWithTwoLiveReadings readingB readingA liveL liveR = refl
toyConsumerClosedWithTwoLiveReadings readingB readingB liveL liveR = refl
toyConsumerClosedWithTwoLiveReadings readingB readingC liveL ()
toyConsumerClosedWithTwoLiveReadings readingC right () liveR

readingAStillLive : ToyFibre readingA
readingAStillLive = tt

readingBStillLive : ToyFibre readingB
readingBStillLive = tt

readingsRemainDistinct : readingA ≡ readingB → ⊥
readingsRemainDistinct ()

record SemanticConsumerClosureBoundary : Set where
  constructor semanticConsumerClosureBoundary
  field
    consumerClosureRequiresUniqueSemanticReading : Bool
    consumerClosureRequiresUniqueSemanticReadingIsFalse :
      consumerClosureRequiresUniqueSemanticReading ≡ false
    semanticAmbiguityMayRemainAfterConsumerClosure : Bool
    semanticAmbiguityMayRemainAfterConsumerClosureIsTrue :
      semanticAmbiguityMayRemainAfterConsumerClosure ≡ true
    refinementCanPreserveConsumerClosure : Bool
    refinementCanPreserveConsumerClosureIsTrue :
      refinementCanPreserveConsumerClosure ≡ true
    nextProbeMayTargetConsumerRatherThanWorldIdentity : Bool
    nextProbeMayTargetConsumerRatherThanWorldIdentityIsTrue :
      nextProbeMayTargetConsumerRatherThanWorldIdentity ≡ true

canonicalSemanticConsumerClosureBoundary : SemanticConsumerClosureBoundary
canonicalSemanticConsumerClosureBoundary =
  semanticConsumerClosureBoundary false refl true refl true refl true refl
