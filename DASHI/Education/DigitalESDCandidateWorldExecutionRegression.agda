module DASHI.Education.DigitalESDCandidateWorldExecutionRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDCandidateWorldExecutionExact as World
import DASHI.Education.DigitalESDAdaptiveScreeningExecutionExact as Loop
import DASHI.Education.DigitalESDSituatedCapabilityEvidenceCrossPollinationExact as Situated

loopOwnerRegression :
  World.canonicalExecutionLoopBoundary
  ≡ Loop.canonicalAdaptiveScreeningExecutionBoundary
loopOwnerRegression = refl

situatedOwnerRegression :
  World.canonicalSituatedWorldBoundary
  ≡ Situated.canonicalDigitalESDSituatedCapabilityEvidenceBoundary
situatedOwnerRegression = refl

singleCommandRegression :
  World.DigitalESDCandidateWorldExecutionBoundary.normalEntryPointIsSingleCommand
    World.canonicalDigitalESDCandidateWorldExecutionBoundary ≡ true
singleCommandRegression = refl

candidatePNFRegression :
  World.DigitalESDCandidateWorldExecutionBoundary.candidatePNFCanBePrepopulated
    World.canonicalDigitalESDCandidateWorldExecutionBoundary ≡ true
candidatePNFRegression = refl

candidateAuthorityRegression :
  World.DigitalESDCandidateWorldExecutionBoundary.candidateInterpretationCreatesSemanticAuthority
    World.canonicalDigitalESDCandidateWorldExecutionBoundary ≡ false
candidateAuthorityRegression = refl

admissionRegression :
  World.DigitalESDCandidateWorldExecutionBoundary.graphMembershipCreatesSourceAuditAdmission
    World.canonicalDigitalESDCandidateWorldExecutionBoundary ≡ false
admissionRegression = refl


boundedInspectionRegression :
  World.DigitalESDCandidateWorldExecutionBoundary.boundedInspectionReturned
    World.canonicalDigitalESDCandidateWorldExecutionBoundary ≡ true
boundedInspectionRegression = refl

flatJsonRuntimeRegression :
  World.FlatJsonGraphIsCanonicalRuntimeState →
  ⊥
flatJsonRuntimeRegression = World.flatJsonGraphDoesNotBecomeCanonicalRuntimeState
