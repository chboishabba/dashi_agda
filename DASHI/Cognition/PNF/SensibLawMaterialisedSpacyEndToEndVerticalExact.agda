module DASHI.Cognition.PNF.SensibLawMaterialisedSpacyEndToEndVerticalExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawMaterialisedSpacyToOntologyVerticalExact as Producer
import DASHI.Cognition.PNF.SensibLawMaterialisedSpacyReferencePopulationLiveExact as Reference
import DASHI.Cognition.PNF.SensibLawAttributionPropositionOccurrenceBidiExact as Attribution
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as Legal
import DASHI.Reasoning.SpacyNegatedCoordinationScopeTraceExact as Trace
import DASHI.Interop.SensibLawOntologyTopology as Ontology

------------------------------------------------------------------------
-- FIRST MATERIALISED SPACY -> ONTOLOGY -> STATUS -> LEGAL-GATE VERTICAL
--
-- This is intentionally a candidate/legal-input specimen, not a legal
-- conclusion.  The parser-derived semantic fibre is retained all the way down.
------------------------------------------------------------------------

sourceProposition : Status.PropositionStatusProduct
sourceProposition = Attribution.proposition (Producer.weld Producer.readmeOutput)

sourceMentionedEvent : Status.EventStatusProduct
sourceMentionedEvent = Attribution.occurrence (Producer.weld Producer.readmeOutput)

------------------------------------------------------------------------
-- Source assertion upgrades only the discourse/occurrence-status coordinate:
-- "the source asserts this eventuality".  It does not establish world truth.
------------------------------------------------------------------------

sourceAssertedEvent : Status.EventStatusProduct
sourceAssertedEvent =
  Status.eventStatusProduct
    (Ontology.StableId.value (Ontology.Event.eventId Producer.readmeEvent))
    Status.assertedOccurrence
    Status.documentTime
    Status.scopeResolved

sourcePropositionReceipt : Status.PropositionResolutionReceipt
sourcePropositionReceipt =
  Status.propositionResolutionReceipt
    sourceProposition
    Status.assertedBySource
    Status.truthUnresolved
    "source-document perspective from explicit provenance input"
    ("materialised spaCy candidate fibre" ∷
     "reviewed PNF trace" ∷ [])
    "source-assertion-status:not-truth-admission"

sourceOccurrenceReceipt : Status.OccurrenceResolutionReceipt
sourceOccurrenceReceipt =
  Status.occurrenceResolutionReceipt
    sourceMentionedEvent
    Status.assertedOccurrence
    ("claim about same literal ITIR event" ∷
     "source proposition assertedBySource" ∷ [])
    ("materialised spaCy trace retained" ∷ [])
    "source-asserted-occurrence:not-occurrence-admission"

sourceAssertionTruthUnresolved :
  Status.resultingTruthStatus sourcePropositionReceipt ≡ Status.truthUnresolved
sourceAssertionTruthUnresolved = refl

sourceAssertionNotOccurrenceAdmission :
  Status.resultingOccurrenceStatus sourceOccurrenceReceipt ≡ Status.assertedOccurrence
sourceAssertionNotOccurrenceAdmission = refl

------------------------------------------------------------------------
-- Legal engine may reason ABOUT the source assertion, but only as candidate
-- applicability.  This is the existing fail-closed LegalEventUse constructor.
------------------------------------------------------------------------

sourceAssertionLegalGate : Legal.SemanticLegalInputGate Producer.readmeEvent
sourceAssertionLegalGate =
  Legal.semanticLegalInputGate
    sourceAssertedEvent
    sourceProposition
    refl
    Status.applicabilityCandidate
    Legal.assertionCandidateUse

sourceAssertionOnlyCandidateLegalUse :
  Legal.SemanticLegalInputGate.resultingApplicability sourceAssertionLegalGate
  ≡ Status.applicabilityCandidate
sourceAssertionOnlyCandidateLegalUse = refl

------------------------------------------------------------------------
-- One receipt packages the continuous live specimen, including reference
-- population from the SAME materialised sentence.
------------------------------------------------------------------------

record MaterialisedEndToEndReceipt : Set where
  constructor materialisedEndToEndReceipt
  field
    parserPredicateIsLiteralTraceToken :
      Producer.parserTokenPreserved Producer.readmeOutput ≡ Trace.mutateToken
    parserSemanticFibreIsLiteralTraceFibre :
      Producer.sourceFibrePreserved Producer.readmeOutput ≡ Trace.candidateFibre
    parserFormulaIsLiteralReviewedFormula :
      Producer.propositionFormulaPreserved Producer.readmeOutput ≡ Trace.finalFormula
    ontologyEvent : Ontology.Event
    ontologyClaim : Ontology.Claim
    ontologyPerspective : Ontology.Perspective
    claimAboutSameEvent :
      Ontology.Claim.aboutEvent ontologyClaim ≡ Ontology.Event.eventId ontologyEvent
    claimSameSpeakerAsPerspective :
      Ontology.Claim.assertedBy ontologyClaim
      ≡ Ontology.Perspective.speakerId ontologyPerspective
    referencePopulation : Reference.MaterialisedReferencePopulationReceipt
    propositionResolution : Status.PropositionResolutionReceipt
    occurrenceResolution : Status.OccurrenceResolutionReceipt
    legalInputGate : Legal.SemanticLegalInputGate ontologyEvent
    truthStillUnresolved :
      Status.resultingTruthStatus propositionResolution ≡ Status.truthUnresolved
    legalUseStillCandidate :
      Legal.SemanticLegalInputGate.resultingApplicability legalInputGate
      ≡ Status.applicabilityCandidate

open MaterialisedEndToEndReceipt public

canonicalMaterialisedEndToEnd : MaterialisedEndToEndReceipt
canonicalMaterialisedEndToEnd =
  materialisedEndToEndReceipt
    refl
    refl
    refl
    Producer.readmeEvent
    Producer.readmeClaim
    Producer.readmePerspective
    Producer.readmeClaimAboutSameEvent
    Producer.readmeClaimSameSpeakerAsPerspective
    Reference.canonicalMaterialisedReferencePopulation
    sourcePropositionReceipt
    sourceOccurrenceReceipt
    sourceAssertionLegalGate
    refl
    refl

------------------------------------------------------------------------
-- End-to-end no-collapse laws.
------------------------------------------------------------------------

data MaterialisedEndToEndMeansGeneralCorpusCompiler : Set where
data SourceAssertionMeansOccurrenceAdmitted : Set where
data SourceAssertionMeansTruthAdmitted : Set where
data CandidateLegalGateMeansApplicableLaw : Set where
data ReferenceCandidateMeansIdentityResolved : Set where

materialisedVerticalDoesNotMeanGeneralCompiler :
  MaterialisedEndToEndMeansGeneralCorpusCompiler → ⊥
materialisedVerticalDoesNotMeanGeneralCompiler ()

sourceAssertionDoesNotMeanOccurrenceAdmitted :
  SourceAssertionMeansOccurrenceAdmitted → ⊥
sourceAssertionDoesNotMeanOccurrenceAdmitted ()

sourceAssertionDoesNotMeanTruthAdmitted : SourceAssertionMeansTruthAdmitted → ⊥
sourceAssertionDoesNotMeanTruthAdmitted ()

candidateLegalGateDoesNotMeanApplicableLaw : CandidateLegalGateMeansApplicableLaw → ⊥
candidateLegalGateDoesNotMeanApplicableLaw ()

referenceCandidateDoesNotMeanIdentityResolved : ReferenceCandidateMeansIdentityResolved → ⊥
referenceCandidateDoesNotMeanIdentityResolved ()
