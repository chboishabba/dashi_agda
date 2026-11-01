module DASHI.Education.DigitalESDTransferablePedagogicalPrinciplesRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Biology.CrossPaperDialecticalDevelopment as Development
import DASHI.Education.DigitalESDTransferablePedagogicalPrinciplesExact as Principles

principleCountRegression : Principles.transferablePrincipleCount ≡ 7
principleCountRegression = refl

feedbackPrincipleIsCrossPaperSynthesisRegression :
  Principles.TransferablePrincipleRow.claimRegister
    Principles.feedbackAsRevisableSignalRow
  ≡ Development.crossPaperInference
feedbackPrincipleIsCrossPaperSynthesisRegression = refl

agencyPrincipleCandidateOnlyRegression :
  Principles.TransferablePrincipleRow.candidateOnly
    Principles.constitutiveLearnerAgencyRow
  ≡ true
agencyPrincipleCandidateOnlyRegression = refl

localChoiceRetainedRegression :
  Principles.TransferablePrinciplesBoundary.localChoiceRetained
    Principles.canonicalTransferablePrinciplesBoundary
  ≡ true
localChoiceRetainedRegression = refl

sourceFibresRetainedRegression :
  Principles.TransferablePrinciplesBoundary.sourceFibresRetained
    Principles.canonicalTransferablePrinciplesBoundary
  ≡ true
sourceFibresRetainedRegression = refl

principlesNotAliceEmpiricalFindingsRegression :
  Principles.TransferablePrinciplesBoundary.crossPaperPrinciplesAreAliceEmpiricalFindings
    Principles.canonicalTransferablePrinciplesBoundary
  ≡ false
principlesNotAliceEmpiricalFindingsRegression = refl

principlesDoNotCreateSustainabilityEvidenceRegression :
  Principles.TransferablePrinciplesBoundary.principlesCreateSustainabilityEvidence
    Principles.canonicalTransferablePrinciplesBoundary
  ≡ false
principlesDoNotCreateSustainabilityEvidenceRegression = refl

coarseProxyDoesNotDetermineInterventionRegression :
  Principles.CoarseProxyDeterminesContextAdequateIntervention → ⊥
coarseProxyDoesNotDetermineInterventionRegression =
  Principles.coarseProxyDoesNotDetermineContextAdequateIntervention
