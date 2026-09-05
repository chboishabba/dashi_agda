module DASHI.Reasoning.JusticeLeeSensibLawAdversarialProofGraphBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.SensibLawResidualLattice as SL

------------------------------------------------------------------------
-- JUSTICE LEE / SENSIBLAW ADVERSARIAL PROOF GRAPH — BIDI OWNER
--
-- Source discipline:
--   * Justice Lee, "All the Right Notes: Artificial Intelligence and the
--     Future of the Common Law", Sixteenth Sir Harry Gibbs Memorial Oration,
--     22 August 2026, Federal Court of Australia.
--
-- Lee is used only as jurisprudential / procedural-design motivation for:
--   proposition-oriented interrogation of large evidentiary corpora;
--   source-linked structured synthesis;
--   preservation of original material and contestability; and
--   retention of human adjudicative judgment.
--
-- The proof-graph, BIDI compilation, response geometry, residual taxonomy and
-- search obligations below are DASHI / SensibLaw constructions.  No theorem
-- below is attributed mathematically to Justice Lee.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. A legal proposition is a fibre, not a naked Boolean.
------------------------------------------------------------------------

data PartyRole : Set where
  applicant respondent court externalWitness : PartyRole

data LegalRole : Set where
  pleadedFact evidentiaryFact legalProposition causalLink requestedOrder : LegalRole

data EpistemicStatus : Set where
  alleged admitted disputed supported proved rejected unresolved : EpistemicStatus

data EvidenceKind : Set where
  sourceText accountRecord message report testimony eventRecord otherEvidence : EvidenceKind

record PropositionFibre : Set where
  constructor propositionFibre
  field
    atom : SL.PredicatePNF
    party : PartyRole
    legalRole : LegalRole
    status : EpistemicStatus
    sourceReference : String
    evidenceKind : EvidenceKind
    temporalReference : String
    relationReference : String

open PropositionFibre public

------------------------------------------------------------------------
-- 2. Opposition is typed.  A respondent does not merely flip a predicate.
------------------------------------------------------------------------

data ResponseMode : Set where
  denyOccurrence
  admitOccurrenceDisputeCharacterisation
  admitConductAddContext
  disputeCausation
  challengeEvidenceReliability
  offerAlternativeEvent
  admitProposition
  : ResponseMode

record ResponseEdge : Set where
  constructor responseEdge
  field
    target : PropositionFibre
    response : PropositionFibre
    mode : ResponseMode
    responseReference : String

open ResponseEdge public

responseModesAreNotBooleanNegation :
  admitOccurrenceDisputeCharacterisation ≡ denyOccurrence → ⊥
responseModesAreNotBooleanNegation ()

contextualResponseIsNotPredicateFlip :
  admitConductAddContext ≡ denyOccurrence → ⊥
contextualResponseIsNotPredicateFlip ()

causalDisputeIsNotOccurrenceDenial :
  disputeCausation ≡ denyOccurrence → ⊥
causalDisputeIsNotOccurrenceDenial ()

------------------------------------------------------------------------
-- 3. The controversy residual is fibred across several disagreement kinds.
------------------------------------------------------------------------

data DisagreementKind : Set where
  nodeDisagreement
  relationDisagreement
  evidenceDisagreement
  characterisationDisagreement
  causalDisagreement
  legalConsequenceDisagreement
  : DisagreementKind

record ControversyResidual : Set where
  constructor controversyResidual
  field
    kind : DisagreementKind
    applicantNode : PropositionFibre
    respondentNode : PropositionFibre
    residualLevel : SL.ResidualLevel
    unresolvedQuestion : String

open ControversyResidual public

------------------------------------------------------------------------
-- 4. Proof obligations distinguish assertion, support, admission and proof.
------------------------------------------------------------------------

data ObligationKind : Set where
  premiseObligation
  evidenceObligation
  responseObligation
  discriminatorObligation
  adjudicativeObligation
  : ObligationKind

record ProofObligation : Set where
  constructor proofObligation
  field
    proposition : PropositionFibre
    obligationKind : ObligationKind
    requiredBy : String
    dischargeReference : String

open ProofObligation public

record ProofGraph : Set where
  constructor proofGraph
  field
    rootClaim : PropositionFibre
    propositions : List PropositionFibre
    responses : List ResponseEdge
    residuals : List ControversyResidual
    obligations : List ProofObligation
    graphReference : String

open ProofGraph public

------------------------------------------------------------------------
-- 5. Authority firewall.
------------------------------------------------------------------------

data MachineOperation : Set where
  parseSource
  linkProvenance
  constructChronology
  alignPredicates
  synthesizeControversy
  rankDiscriminator
  : MachineOperation

data AdjudicativeOperation : Set where
  determineCredibility
  determineUltimateFact
  assignNormativeWeight
  enterFinalJudgment
  : AdjudicativeOperation

record AuthorityBoundary : Set where
  constructor authorityBoundary
  field
    machineMayParseAndStructure : Bool
    machineMayParseAndStructureIsTrue : machineMayParseAndStructure ≡ true

    synthesisEqualsPartyAdmission : Bool
    synthesisEqualsPartyAdmissionIsFalse : synthesisEqualsPartyAdmission ≡ false

    synthesisEqualsProvedFact : Bool
    synthesisEqualsProvedFactIsFalse : synthesisEqualsProvedFact ≡ false

    epistemicCapabilityImpliesAdjudicativeAuthority : Bool
    epistemicCapabilityImpliesAdjudicativeAuthorityIsFalse :
      epistemicCapabilityImpliesAdjudicativeAuthority ≡ false

    partyConsentImpliesDelegability : Bool
    partyConsentImpliesDelegabilityIsFalse :
      partyConsentImpliesDelegability ≡ false

canonicalAuthorityBoundary : AuthorityBoundary
canonicalAuthorityBoundary =
  authorityBoundary
    true refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- 6. Forward direction: filing materials compile into a controversy graph.
------------------------------------------------------------------------

record FilingBundle : Set where
  constructor filingBundle
  field
    ordersSought : List PropositionFibre
    materialFacts : List PropositionFibre
    legalPropositions : List PropositionFibre
    supportingEvidence : List PropositionFibre
    filingReference : String

open FilingBundle public

record ForwardCompilation : Set where
  constructor forwardCompilation
  field
    applicantFiling : FilingBundle
    respondentFiling : FilingBundle
    compiledGraph : ProofGraph
    preservesSourceTrace : Bool
    preservesSourceTraceIsTrue : preservesSourceTrace ≡ true
    silentlyDeletesWeakArguments : Bool
    silentlyDeletesWeakArgumentsIsFalse : silentlyDeletesWeakArguments ≡ false
    permitsPartyCorrection : Bool
    permitsPartyCorrectionIsTrue : permitsPartyCorrection ≡ true
    compilationReference : String

open ForwardCompilation public

------------------------------------------------------------------------
-- 7. Reverse direction: a desired procedural decision compiles backwards to
-- unresolved proof/evidence/discriminator obligations.
------------------------------------------------------------------------

data ProceduralGoal : Set where
  identifyCommonGround
  isolateResidualControversy
  decideEvidenceNeeded
  prepareForAdjudication
  : ProceduralGoal

record ReverseProofSearch : Set where
  constructor reverseProofSearch
  field
    graph : ProofGraph
    goal : ProceduralGoal
    openObligations : List ProofObligation
    candidateResiduals : List ControversyResidual
    requestedDiscriminator : String
    targetEvidenceQuery : String
    reverseReference : String

open ReverseProofSearch public

record BidiLegalProofGraph : Set where
  constructor bidiLegalProofGraph
  field
    forward : ForwardCompilation
    reverse : ReverseProofSearch
    sameGraphObject :
      compiledGraph forward ≡ graph reverse
    bidiReference : String

open BidiLegalProofGraph public

------------------------------------------------------------------------
-- 8. Search boundary: retrieval proposes; proof admission decides.
------------------------------------------------------------------------

record SearchAdmissionBoundary : Set where
  constructor searchAdmissionBoundary
  field
    semanticSimilarityImpliesSupport : Bool
    semanticSimilarityImpliesSupportIsFalse :
      semanticSimilarityImpliesSupport ≡ false

    keywordMissImpliesIrrelevance : Bool
    keywordMissImpliesIrrelevanceIsFalse :
      keywordMissImpliesIrrelevance ≡ false

    documentVolumeImpliesSalienceCompleteness : Bool
    documentVolumeImpliesSalienceCompletenessIsFalse :
      documentVolumeImpliesSalienceCompleteness ≡ false

    targetedResidualSearchPreferredOverWholeCorpusRescan : Bool
    targetedResidualSearchPreferredOverWholeCorpusRescanIsTrue :
      targetedResidualSearchPreferredOverWholeCorpusRescan ≡ true

canonicalSearchAdmissionBoundary : SearchAdmissionBoundary
canonicalSearchAdmissionBoundary =
  searchAdmissionBoundary
    false refl
    false refl
    false refl
    true refl

------------------------------------------------------------------------
-- 9. Source / ownership boundary.
------------------------------------------------------------------------

record JusticeLeeSourceBoundary : Set where
  constructor justiceLeeSourceBoundary
  field
    leeSource : String
    leeMotivatesPropositionOrientedCorpusInterrogation : Bool
    leeMotivatesPropositionOrientedCorpusInterrogationIsTrue :
      leeMotivatesPropositionOrientedCorpusInterrogation ≡ true

    leeMotivatesSourceLinkedStructuredSynthesis : Bool
    leeMotivatesSourceLinkedStructuredSynthesisIsTrue :
      leeMotivatesSourceLinkedStructuredSynthesis ≡ true

    leeMotivatesHumanJudgmentBoundary : Bool
    leeMotivatesHumanJudgmentBoundaryIsTrue :
      leeMotivatesHumanJudgmentBoundary ≡ true

    leeClaimsDASHIBidiProofGraphTheorem : Bool
    leeClaimsDASHIBidiProofGraphTheoremIsFalse :
      leeClaimsDASHIBidiProofGraphTheorem ≡ false

canonicalJusticeLeeSourceBoundary : JusticeLeeSourceBoundary
canonicalJusticeLeeSourceBoundary =
  justiceLeeSourceBoundary
    "Justice Lee, All the Right Notes: Artificial Intelligence and the Future of the Common Law, Sixteenth Sir Harry Gibbs Memorial Oration, Federal Court of Australia, 22 August 2026"
    true refl
    true refl
    true refl
    false refl
