module DASHI.Education.DigitalESDCandidateWorldExecutionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDAdaptiveScreeningExecutionExact as Loop
import DASHI.Education.DigitalESDSituatedCapabilityEvidenceCrossPollinationExact as Situated

------------------------------------------------------------------------
-- ZERO-CONFIG DIGITAL-ESD CANDIDATE WORLD EXECUTION
--
-- Runtime owner:
--   interop_scripts/digital_esd/run_world.py
--
-- The runtime composes existing acquisition/screen/retrieve/parse receipts and
-- projects their observed/candidate products into one inspectable graph.
-- Graph construction and candidate algebra may be automated.  Semantic,
-- screening and admission authority remain receipt-gated.
------------------------------------------------------------------------

canonicalExecutionLoopBoundary : Loop.AdaptiveScreeningExecutionBoundary
canonicalExecutionLoopBoundary = Loop.canonicalAdaptiveScreeningExecutionBoundary

canonicalSituatedWorldBoundary :
  Situated.DigitalESDSituatedCapabilityEvidenceBoundary
canonicalSituatedWorldBoundary =
  Situated.canonicalDigitalESDSituatedCapabilityEvidenceBoundary

record CandidateWorldArtifact : Set where
  constructor candidate-world-artifact
  field
    worldManifestReference : String
    nodesReference : String
    edgesReference : String
    agentInspectionReference : String

    candidateGraphAutomaticallyBuilt : Bool
    candidateGraphAutomaticallyBuiltIsTrue :
      candidateGraphAutomaticallyBuilt ≡ true

    parserCandidatesPrepopulated : Bool
    parserCandidatesPrepopulatedIsTrue :
      parserCandidatesPrepopulated ≡ true

    stageReceiptsProjectedIntoGraph : Bool
    stageReceiptsProjectedIntoGraphIsTrue :
      stageReceiptsProjectedIntoGraph ≡ true

    unresolvedAuthorityGatesRetained : Bool
    unresolvedAuthorityGatesRetainedIsTrue :
      unresolvedAuthorityGatesRetained ≡ true

open CandidateWorldArtifact public

record DigitalESDCandidateWorldExecutionBoundary : Set where
  constructor digital-esd-candidate-world-execution-boundary
  field
    normalEntryPointIsSingleCommand : Bool
    normalEntryPointIsSingleCommandIsTrue :
      normalEntryPointIsSingleCommand ≡ true

    candidateScreeningCanBePrepopulated : Bool
    candidateScreeningCanBePrepopulatedIsTrue :
      candidateScreeningCanBePrepopulated ≡ true

    candidatePNFCanBePrepopulated : Bool
    candidatePNFCanBePrepopulatedIsTrue :
      candidatePNFCanBePrepopulated ≡ true

    candidateGraphCanBeBuiltAutomatically : Bool
    candidateGraphCanBeBuiltAutomaticallyIsTrue :
      candidateGraphCanBeBuiltAutomatically ≡ true

    candidateInterpretationCreatesSemanticAuthority : Bool
    candidateInterpretationCreatesSemanticAuthorityIsFalse :
      candidateInterpretationCreatesSemanticAuthority ≡ false

    graphMembershipCreatesSourceAuditAdmission : Bool
    graphMembershipCreatesSourceAuditAdmissionIsFalse :
      graphMembershipCreatesSourceAuditAdmission ≡ false

    agentInspectionMayPromoteWithoutReceipt : Bool
    agentInspectionMayPromoteWithoutReceiptIsFalse :
      agentInspectionMayPromoteWithoutReceipt ≡ false

    residualQueuesCanBeDerivedAutomatically : Bool
    residualQueuesCanBeDerivedAutomaticallyIsTrue :
      residualQueuesCanBeDerivedAutomatically ≡ true

open DigitalESDCandidateWorldExecutionBoundary public

canonicalDigitalESDCandidateWorldExecutionBoundary :
  DigitalESDCandidateWorldExecutionBoundary
canonicalDigitalESDCandidateWorldExecutionBoundary =
  digital-esd-candidate-world-execution-boundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    true refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CandidateWorldCreatesSemanticAuthority : Set where
data CandidateWorldCreatesSourceAuditAdmission : Set where
data AgentInspectionWithoutReceiptCreatesAuthority : Set where

candidateWorldDoesNotCreateSemanticAuthority :
  CandidateWorldCreatesSemanticAuthority → ⊥
candidateWorldDoesNotCreateSemanticAuthority ()

candidateWorldDoesNotCreateSourceAuditAdmission :
  CandidateWorldCreatesSourceAuditAdmission → ⊥
candidateWorldDoesNotCreateSourceAuditAdmission ()

agentInspectionStillRequiresAuthorityReceipt :
  AgentInspectionWithoutReceiptCreatesAuthority → ⊥
agentInspectionStillRequiresAuthorityReceipt ()

candidateWorldExecutionReading : String
candidateWorldExecutionReading =
  "The normal Digital-ESD runtime surface is one zero-config candidate-world command. Existing screening/retrieval/verification/parser receipts are projected into one provenance-preserving graph; parser PNF/facet/EvidenceObservation candidates and residual queues are prepopulated automatically; the agent inspects the world rather than manually traversing artifact directories. Automated graph membership, algebraic fit or candidate interpretation does not create semantic authority or SourceAuditAdmission: those promotions remain explicit receipt-bearing steps."
