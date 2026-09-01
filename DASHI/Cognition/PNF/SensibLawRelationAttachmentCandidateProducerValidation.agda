module DASHI.Cognition.PNF.SensibLawRelationAttachmentCandidateProducerValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawRelationAttachmentCandidateProducerExact as Producer

candidateOnly :
  Producer.candidateOnly (Producer.candidate Producer.canonicalRelationProducerBoundary) ≡ true
candidateOnly = refl

contextResolutionRequired :
  Producer.contextResolutionRequired (Producer.candidate Producer.canonicalRelationProducerBoundary)
  ≡ true
contextResolutionRequired = refl

semanticAuthorityZero :
  Producer.semanticAuthorityGranted Producer.canonicalRelationProducerBoundary ≡ false
semanticAuthorityZero = refl

publicationEffectZero :
  Producer.publicationEffect Producer.canonicalRelationProducerBoundary ≡ false
publicationEffectZero = refl

noSecondRuntime :
  Producer.directRuntimeNeedsSecondRelationalRuntime
    Producer.canonicalRelationResolutionAdmissionBoundary
  ≡ false
noSecondRuntime = refl

consumerParityMayIgnoreFineExecutionIdentity :
  Producer.consumerParityMayIgnoreFineExecutionIdentity
    Producer.canonicalRelationResolutionAdmissionBoundary
  ≡ true
consumerParityMayIgnoreFineExecutionIdentity = refl

prepositionCannotSelfPromoteToJurisdiction :
  Producer.ParserPrepositionProvesJurisdiction → ⊥
prepositionCannotSelfPromoteToJurisdiction =
  Producer.parserPrepositionDoesNotProveJurisdiction

agentMarkerCannotSelfPromoteToActor :
  Producer.ParserAgentMarkerProvesActor → ⊥
agentMarkerCannotSelfPromoteToActor =
  Producer.parserAgentMarkerDoesNotProveActor

relationCandidateCannotSelfAdmit :
  Producer.CandidateRelationAutomaticallyAdmitted → ⊥
relationCandidateCannotSelfAdmit =
  Producer.candidateRelationIsNotAutomaticallyAdmitted
