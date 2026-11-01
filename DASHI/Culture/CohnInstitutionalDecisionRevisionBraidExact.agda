module DASHI.Culture.CohnInstitutionalDecisionRevisionBraidExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Core.AppendOnlyEvidenceResidualRevisionExact as AppendOnly
import DASHI.Culture.CohnInstitutionalEpistemicConsequenceCrossPollinationExact as ConsequenceBridge
import DASHI.Culture.CohnInstitutionalNormReasonablenessEvidenceCrossPollinationExact as EvidenceBridge
import DASHI.Law.SensibLawExpertEvidenceProductionIntegrityExact as Expert
import DASHI.Law.SensibLawInstitutionalResponsibilityExact as Responsibility
import DASHI.Law.SensibLawOperationalLegalityExact as Operational
import DASHI.Reasoning.PNFRevisionSelectiveReopeningExact as PNFRevision

------------------------------------------------------------------------
-- COHN / INSTITUTIONAL DECISION / SELECTIVE REOPENING BRAID
--
-- Thin application adapter over canonical repository owners.  This module does
-- not introduce a new truth-maintenance calculus.  It only declares the
-- institutional dependency relation needed to compose existing proof-bearing
-- reopening obligations.
--
--   source genealogy
--       -> evidence adequacy
--       -> institutional decision
--       -> consequence
--
--   institutional normality
--       -> legal reasonableness
--       -> institutional decision
--
--   authority status
--       -> institutional decision
--
-- The arrows are dependencies for re-audit, not claims that an upstream
-- coordinate uniquely determines the downstream answer.
------------------------------------------------------------------------

data InstitutionalArtifact : Set where
  sourceGenealogyArtifact : InstitutionalArtifact
  evidenceAdequacyArtifact : InstitutionalArtifact
  institutionalNormalityArtifact : InstitutionalArtifact
  legalReasonablenessArtifact : InstitutionalArtifact
  authorityStatusArtifact : InstitutionalArtifact
  institutionalDecisionArtifact : InstitutionalArtifact
  consequenceArtifact : InstitutionalArtifact

------------------------------------------------------------------------
-- Proof-bearing dependency edges.
------------------------------------------------------------------------

data Depends : InstitutionalArtifact → InstitutionalArtifact → Set where
  sourceGenealogyFeedsEvidenceAdequacy :
    Depends sourceGenealogyArtifact evidenceAdequacyArtifact
  evidenceAdequacyFeedsDecision :
    Depends evidenceAdequacyArtifact institutionalDecisionArtifact
  institutionalNormalityFeedsLegalReasonableness :
    Depends institutionalNormalityArtifact legalReasonablenessArtifact
  legalReasonablenessFeedsDecision :
    Depends legalReasonablenessArtifact institutionalDecisionArtifact
  authorityStatusFeedsDecision :
    Depends authorityStatusArtifact institutionalDecisionArtifact
  decisionFeedsConsequence :
    Depends institutionalDecisionArtifact consequenceArtifact

------------------------------------------------------------------------
-- Direct reopening obligations.
------------------------------------------------------------------------

sourceGenealogyReopensEvidenceAdequacy :
  Dependency.ReopeningObligation
    Depends sourceGenealogyArtifact evidenceAdequacyArtifact
sourceGenealogyReopensEvidenceAdequacy =
  Dependency.oneEdgeCreatesReopeningObligation
    sourceGenealogyFeedsEvidenceAdequacy

evidenceAdequacyReopensDecision :
  Dependency.ReopeningObligation
    Depends evidenceAdequacyArtifact institutionalDecisionArtifact
evidenceAdequacyReopensDecision =
  Dependency.oneEdgeCreatesReopeningObligation
    evidenceAdequacyFeedsDecision

institutionalNormalityReopensLegalReasonableness :
  Dependency.ReopeningObligation
    Depends institutionalNormalityArtifact legalReasonablenessArtifact
institutionalNormalityReopensLegalReasonableness =
  Dependency.oneEdgeCreatesReopeningObligation
    institutionalNormalityFeedsLegalReasonableness

legalReasonablenessReopensDecision :
  Dependency.ReopeningObligation
    Depends legalReasonablenessArtifact institutionalDecisionArtifact
legalReasonablenessReopensDecision =
  Dependency.oneEdgeCreatesReopeningObligation
    legalReasonablenessFeedsDecision

authorityStatusReopensDecision :
  Dependency.ReopeningObligation
    Depends authorityStatusArtifact institutionalDecisionArtifact
authorityStatusReopensDecision =
  Dependency.oneEdgeCreatesReopeningObligation
    authorityStatusFeedsDecision

decisionReopensConsequence :
  Dependency.ReopeningObligation
    Depends institutionalDecisionArtifact consequenceArtifact
decisionReopensConsequence =
  Dependency.oneEdgeCreatesReopeningObligation decisionFeedsConsequence

------------------------------------------------------------------------
-- Transitive reopening paths.
------------------------------------------------------------------------

sourceGenealogyReopensDecision :
  Dependency.ReopeningObligation
    Depends sourceGenealogyArtifact institutionalDecisionArtifact
sourceGenealogyReopensDecision =
  Dependency.obligationsCompose
    sourceGenealogyReopensEvidenceAdequacy
    evidenceAdequacyReopensDecision

sourceGenealogyReopensConsequence :
  Dependency.ReopeningObligation
    Depends sourceGenealogyArtifact consequenceArtifact
sourceGenealogyReopensConsequence =
  Dependency.obligationsCompose
    sourceGenealogyReopensDecision
    decisionReopensConsequence

institutionalNormalityReopensDecision :
  Dependency.ReopeningObligation
    Depends institutionalNormalityArtifact institutionalDecisionArtifact
institutionalNormalityReopensDecision =
  Dependency.obligationsCompose
    institutionalNormalityReopensLegalReasonableness
    legalReasonablenessReopensDecision

institutionalNormalityReopensConsequence :
  Dependency.ReopeningObligation
    Depends institutionalNormalityArtifact consequenceArtifact
institutionalNormalityReopensConsequence =
  Dependency.obligationsCompose
    institutionalNormalityReopensDecision
    decisionReopensConsequence

authorityStatusReopensConsequence :
  Dependency.ReopeningObligation
    Depends authorityStatusArtifact consequenceArtifact
authorityStatusReopensConsequence =
  Dependency.obligationsCompose
    authorityStatusReopensDecision
    decisionReopensConsequence

------------------------------------------------------------------------
-- Canonical parent reuse.
------------------------------------------------------------------------

appendOnlyRevisionBoundary : AppendOnly.AppendOnlyEvidenceRevisionBoundary
appendOnlyRevisionBoundary = AppendOnly.canonicalAppendOnlyEvidenceRevisionBoundary

pnfRevisionBoundary : PNFRevision.PNFRevisionReopeningBoundary
pnfRevisionBoundary = PNFRevision.canonicalPNFRevisionReopeningBoundary

institutionalResponsibilityBoundary : Responsibility.InstitutionalResponsibilityBoundary
institutionalResponsibilityBoundary =
  Responsibility.canonicalInstitutionalResponsibilityBoundary

operationalLegalityBoundary : Operational.OperationalLegalityBoundary
operationalLegalityBoundary = Operational.canonicalOperationalLegalityBoundary

institutionalEvidenceBoundary :
  EvidenceBridge.CohnInstitutionalLegalEvidenceBoundary
institutionalEvidenceBoundary =
  EvidenceBridge.canonicalCohnInstitutionalLegalEvidenceBoundary

institutionalConsequenceBoundary :
  ConsequenceBridge.CohnInstitutionalEpistemicConsequenceBoundary
institutionalConsequenceBoundary =
  ConsequenceBridge.canonicalCohnInstitutionalEpistemicConsequenceBoundary

------------------------------------------------------------------------
-- Expert-report agreement remains genealogy-sensitive.
------------------------------------------------------------------------

agreementDoesNotCreateIndependentCorroboration :
  Expert.AgreementAutomaticallyIndependentCorroboration → ⊥
agreementDoesNotCreateIndependentCorroboration =
  Expert.agreementDoesNotAutomaticallyCreateIndependentCorroboration

sourceIndependenceCannotFactorThroughAgreement :
  Expert.SourceIndependenceQueryAdequate → ⊥
sourceIndependenceCannotFactorThroughAgreement =
  Expert.sourceIndependenceQueryNotAdequate

------------------------------------------------------------------------
-- Revision-status and no-promotion boundary.
--
-- Reopening is a current-use obligation.  It does not erase historical
-- evidence, convert stale material into refutation, manufacture authority, or
-- let consequence severity decide evidentiary truth.
------------------------------------------------------------------------

record InstitutionalDecisionRevisionBoundary : Set where
  constructor institutionalDecisionRevisionBoundary
  field
    appendOnlyEvidenceMayChangeCurrentConclusion : Bool
    appendOnlyEvidenceMayChangeCurrentConclusionIsTrue :
      appendOnlyEvidenceMayChangeCurrentConclusion ≡ true

    sourceGenealogyRevisionMayReopenDecisionTransitively : Bool
    sourceGenealogyRevisionMayReopenDecisionTransitivelyIsTrue :
      sourceGenealogyRevisionMayReopenDecisionTransitively ≡ true

    sourceGenealogyRevisionMayReopenConsequenceTransitively : Bool
    sourceGenealogyRevisionMayReopenConsequenceTransitivelyIsTrue :
      sourceGenealogyRevisionMayReopenConsequenceTransitively ≡ true

    authorityRevisionMayReopenDecision : Bool
    authorityRevisionMayReopenDecisionIsTrue :
      authorityRevisionMayReopenDecision ≡ true

    staleDecisionEqualsRefutedDecision : Bool
    staleDecisionEqualsRefutedDecisionIsFalse :
      staleDecisionEqualsRefutedDecision ≡ false

    reopeningDeletesHistoricalEvidence : Bool
    reopeningDeletesHistoricalEvidenceIsFalse :
      reopeningDeletesHistoricalEvidence ≡ false

    evidenceAdequacyCreatesAuthority : Bool
    evidenceAdequacyCreatesAuthorityIsFalse :
      evidenceAdequacyCreatesAuthority ≡ false

    consequenceSeverityCreatesEvidenceTruth : Bool
    consequenceSeverityCreatesEvidenceTruthIsFalse :
      consequenceSeverityCreatesEvidenceTruth ≡ false

    agreementCreatesIndependentGenealogy : Bool
    agreementCreatesIndependentGenealogyIsFalse :
      agreementCreatesIndependentGenealogy ≡ false

open InstitutionalDecisionRevisionBoundary public

canonicalInstitutionalDecisionRevisionBoundary :
  InstitutionalDecisionRevisionBoundary
canonicalInstitutionalDecisionRevisionBoundary =
  institutionalDecisionRevisionBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
