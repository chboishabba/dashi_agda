module DASHI.Reasoning.RelationRepresentationExperimentProtocolExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Reasoning.StructuralMetaphorTaskCompressionExact as Compression
import DASHI.Reasoning.RelationRepresentationAdequacyExact as Adequacy
import DASHI.Reasoning.RelationRepresentationRealizationExact as Realization

------------------------------------------------------------------------
-- EXPERIMENT PROTOCOL FOR EIGENSLUR / FLOURISHING-STYLE RELATION SEARCH
--
-- This is a protocol carrier, not an empirical result.  It formalizes the
-- proof obligations exposed by the Instagram/eigenslur discussion and by the
-- repository cross-pollination:
--
-- matched pairs
-- -> candidate representation family
-- -> declared comparison geometry
-- -> held-out transport scope
-- -> declared consumer family
-- -> static factorisation / collision search
-- -> dynamic trace test where relevant
-- -> target-realization obligation
-- -> authority boundary.
--
-- Candidate complexity is not a truth ordering.  Escalation means only that a
-- richer family is permitted after a simpler candidate loses a required
-- distinction.
------------------------------------------------------------------------

data CandidateClass : Set where
  offsetCandidate
  rotationCandidate
  affineCandidate
  nonlinearCandidate
  contextualCandidate
  : CandidateClass

candidateFamily : CandidateClass → Adequacy.TransformationFamily
candidateFamily offsetCandidate = Adequacy.fixedTranslation
candidateFamily rotationCandidate = Adequacy.linearRotation
candidateFamily affineCandidate = Adequacy.affineTransformation
candidateFamily nonlinearCandidate = Adequacy.learnedNonlinearTransformation
candidateFamily contextualCandidate = Adequacy.applicationSuppliedTransformation

-- A deliberately partial escalation grammar.  It does not say every empirical
-- search must traverse every class, nor that a richer class is normatively
-- superior.
data MayEscalate : CandidateClass → CandidateClass → Set where
  offsetToRotation : MayEscalate offsetCandidate rotationCandidate
  rotationToAffine : MayEscalate rotationCandidate affineCandidate
  affineToNonlinear : MayEscalate affineCandidate nonlinearCandidate
  nonlinearToContextual : MayEscalate nonlinearCandidate contextualCandidate

record HeldOutScope : Set where
  constructor heldOutScope
  field
    targetHeldOut : Bool
    contextHeldOut : Bool
    modelHeldOut : Bool
    temporalCheckpointHeldOut : Bool
    scopeReading : String

record RelationExperimentProtocol : Set₁ where
  constructor relationExperimentProtocol
  field
    matchedPairingDeclared : Bool
    pairingReading : String
    candidate : CandidateClass
    geometry : Adequacy.ComparisonGeometry
    heldOut : HeldOutScope
    consumerNames : List String
    dynamicTraceRequired : Bool
    targetRealizationRequired : Bool
    normativeAuthorityAutoGranted : Bool
    protocolReading : String

open RelationExperimentProtocol public

------------------------------------------------------------------------
-- A representation collision is a first-class rejection of that candidate for
-- the declared consumer.  It does not prove that the representation is useless
-- for every task and does not select the next family automatically.
------------------------------------------------------------------------

record CandidateConsumerFailure
    {Fine Representation Consumer : Set}
    (encode : Fine → Representation)
    (consumer : Fine → Consumer) : Set₁ where
  constructor candidateConsumerFailure
  field
    collision : Compression.CompressionFailureWitness encode consumer
    failedCandidate : CandidateClass
    failureReading : String

open CandidateConsumerFailure public

failedCandidateCannotRealizeConsumer :
  ∀ {Fine Representation Consumer : Set}
    {encode : Fine → Representation}
    {consumer : Fine → Consumer} →
  CandidateConsumerFailure encode consumer →
  Realization.RepresentationRealizationWitness encode consumer →
  ⊥
failedCandidateCannotRealizeConsumer failure =
  Realization.representationCollisionBlocksRealization (collision failure)

record ReopenedCandidateSearch
    {Fine Representation Consumer : Set}
    (encode : Fine → Representation)
    (consumer : Fine → Consumer) : Set₁ where
  constructor reopenedCandidateSearch
  field
    rejected : CandidateConsumerFailure encode consumer
    nextCandidate : CandidateClass
    escalation : MayEscalate (failedCandidate rejected) nextCandidate
    residualMustRemainAvailable : Bool
    residualMustRemainAvailableIsTrue : residualMustRemainAvailable ≡ true
    reopeningReading : String

------------------------------------------------------------------------
-- Concrete protocol specimens.  These are experiment designs, not observed
-- successes.
------------------------------------------------------------------------

strictEigenslurHoldout : HeldOutScope
strictEigenslurHoldout =
  heldOutScope true true true true
    "Hold out target identities, discourse contexts, model families, and training/checkpoint time when testing whether a relation code transfers."

strictFlourishingHoldout : HeldOutScope
strictFlourishingHoldout =
  heldOutScope true true true true
    "Hold out action/virtue families, situated contexts, model families, and temporal checkpoints; consumer tests remain separately declared."

eigenslurProtocol : RelationExperimentProtocol
eigenslurProtocol =
  relationExperimentProtocol
    true
    "Compare a contextualized derogatory form against a declared matched target-identity baseline; unrelated token subtraction is not admitted by default."
    offsetCandidate
    Adequacy.cosineLikeGeometry
    strictEigenslurHoldout
    ("coarse semantic relation" ∷ "situated meaning" ∷ "history/provenance" ∷ [])
    true
    true
    false
    "Begin with the simplest offset hypothesis, but permit reopening into rotation/affine/nonlinear/contextual families when declared consumers collide."

flourishingProtocol : RelationExperimentProtocol
flourishingProtocol =
  relationExperimentProtocol
    true
    "Compare a candidate improved action-state against a matched baseline inside the same declared situation."
    offsetCandidate
    Adequacy.cosineLikeGeometry
    strictFlourishingHoldout
    ("functioning" ∷ "capability" ∷ "agency" ∷ "trajectory" ∷ "situated authority" ∷ [])
    true
    true
    false
    "A positive/prosocial relation code is only a candidate empirical regularity until the declared flourishing consumers and realization boundary are discharged."

------------------------------------------------------------------------
-- Protocol boundaries.
------------------------------------------------------------------------

record RelationExperimentProtocolBoundary : Set where
  constructor relationExperimentProtocolBoundary
  field
    firstPrincipalComponentClosesExperiment : Bool
    firstPrincipalComponentClosesExperimentIsFalse :
      firstPrincipalComponentClosesExperiment ≡ false

    bestMetricSelectsTargetOntology : Bool
    bestMetricSelectsTargetOntologyIsFalse :
      bestMetricSelectsTargetOntology ≡ false

    inSampleFitCountsAsHeldOutTransport : Bool
    inSampleFitCountsAsHeldOutTransportIsFalse :
      inSampleFitCountsAsHeldOutTransport ≡ false

    oneConsumerSuccessClosesAllConsumers : Bool
    oneConsumerSuccessClosesAllConsumersIsFalse :
      oneConsumerSuccessClosesAllConsumers ≡ false

    collisionReopensCandidateSearch : Bool
    collisionReopensCandidateSearchIsTrue :
      collisionReopensCandidateSearch ≡ true

    richerCandidateAutomaticallyBetterEthically : Bool
    richerCandidateAutomaticallyBetterEthicallyIsFalse :
      richerCandidateAutomaticallyBetterEthically ≡ false

canonicalRelationExperimentProtocolBoundary : RelationExperimentProtocolBoundary
canonicalRelationExperimentProtocolBoundary =
  relationExperimentProtocolBoundary
    false refl
    false refl
    false refl
    false refl
    true refl
    false refl
