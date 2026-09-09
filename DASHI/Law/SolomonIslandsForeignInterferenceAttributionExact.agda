module DASHI.Law.SolomonIslandsForeignInterferenceAttributionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedPublicClaimExact as Public
import DASHI.Law.LegalAuthorityCitationExact as Legal

------------------------------------------------------------------------
-- SOLOMON ISLANDS / AUSTRALIA FOREIGN-INTERFERENCE ATTRIBUTION LANE
--
-- This module deliberately does NOT decide whether prohibited foreign
-- interference occurred.  It preserves the evidence / attribution / legal-
-- authority boundaries needed for that downstream consumer.
------------------------------------------------------------------------

data EventAtom : Set where
  australianDiplomaticCommunicationExists : EventAtom
  communicationContainsFundingCommitments : EventAtom
  communicationContainsHoldSteadyLanguage : EventAtom
  confidenceMotionTemporallyAssociated : EventAtom
  defeatMotionLanguageAuthenticatedToAustralianActor : EventAtom
  australianActorIntendedConfidenceVoteInfluence : EventAtom
  coerciveInterventionElementSatisfied : EventAtom
  diplomaticNonInterferenceDutyEngaged : EventAtom
  prohibitedForeignInterferenceLegallyEstablished : EventAtom
  confidenceMotionOutcomeCausedByAustralianConduct : EventAtom


data AtomStatus : Set where
  sourceSupported : AtomStatus
  allegationOnly : AtomStatus
  responseOnly : AtomStatus
  unresolved : AtomStatus
  legallyCharacterised : AtomStatus
  adjudicated : AtomStatus

record AttributedAtom : Set where
  constructor attributed-atom
  field
    atom : EventAtom
    status : AtomStatus
    source : Public.PublicArtifactCitation
    proposition : String
    promotedBeyondSource : Bool
    promotedBeyondSourceIsFalse : promotedBeyondSource ≡ false

open AttributedAtom public

------------------------------------------------------------------------
-- Public-source fixtures.
------------------------------------------------------------------------

abcVerifiedMessageReport : Public.PublicArtifactCitation
abcVerifiedMessageReport = Public.public-artifact-citation
  "Australian Broadcasting Corporation"
  "Australia strikes agreement with Solomon Islands over new treaty"
  "ABC News"
  2026
  "https://www.abc.net.au/news/2026-09-07/australia-strikes-agreement-with-solomon-islands-over-new-treaty/107125924"
  "verified leaked text-message discussion and quoted treaty/funding passages"
  Public.authenticatedArtifactReport
  Public.authenticatedByNamedReporter
  "ABC reports that it verified a message attributed to Australian High Commissioner Jeffrey Roach concerning treaty progress, Australian commitments, and holding steady ahead of the November budget session"

abcPacificOppositionReport : Public.PublicArtifactCitation
abcPacificOppositionReport = Public.public-artifact-citation
  "Australian Broadcasting Corporation"
  "Solomon Islands Opposition accuses Australia of foreign interference"
  "ABC Pacific"
  2026
  "https://www.abc.net.au/pacific/programs/pacificbeat/sols-treaty/107131744"
  "8:08 Pacific Beat audio segment and accompanying story text"
  Public.journalisticReport
  Public.institutionallyPublished
  "ABC Pacific reports the Solomon Islands Opposition allegation of Australian foreign interference"

------------------------------------------------------------------------
-- Legal calibration fixtures.
--
-- These are legal propositions and source locators, not findings that the
-- disputed conduct satisfies them.
------------------------------------------------------------------------

viennaDiplomaticRelationsArticle41 : Legal.LegalCitation
viennaDiplomaticRelationsArticle41 = Legal.legal-citation
  Legal.treaty
  Legal.bindingPrimaryAuthority
  "international law / receiving State"
  "United Nations treaty system"
  "Vienna Convention on Diplomatic Relations"
  1961
  (Legal.treatyCitation "UNTS vol. 500 p. 95; Article 41(1)")
  "Article 41(1)"
  "persons enjoying diplomatic privileges and immunities must respect the laws and regulations of the receiving State and have a duty not to interfere in its internal affairs"
  false refl

nicaraguaNonInterventionPara205 : Legal.LegalCitation
nicaraguaNonInterventionPara205 = Legal.legal-citation
  Legal.judgment
  Legal.persuasivePrimaryAuthority
  "customary international law"
  "International Court of Justice"
  "Military and Paramilitary Activities in and against Nicaragua (Nicaragua v United States), Merits"
  1986
  (Legal.neutralCitation "I.C.J. Reports 1986, p. 14")
  "paragraph 205"
  "prohibited intervention bears on matters a State is entitled to decide freely; coercion is the defining element of wrongful intervention in the Court's formulation"
  false refl

unCharterSovereignEquality : Legal.LegalCitation
unCharterSovereignEquality = Legal.legal-citation
  Legal.treaty
  Legal.bindingPrimaryAuthority
  "international law"
  "United Nations"
  "Charter of the United Nations"
  1945
  (Legal.treatyCitation "UN Charter Article 2(1)")
  "Article 2(1)"
  "the United Nations is based on the principle of the sovereign equality of all its Members"
  false refl

------------------------------------------------------------------------
-- Consumer-relative legal question.
------------------------------------------------------------------------

record ForeignInterferenceCharacterisationReceipt : Set where
  constructor foreign-interference-characterisation-receipt
  field
    communicationAuthenticated : Bool
    communicationAuthenticatedIsTrue : communicationAuthenticated ≡ true
    speakerAndRecipientAttributed : Bool
    speakerAndRecipientAttributedIsTrue : speakerAndRecipientAttributed ≡ true
    exactPoliticalRequestEstablished : Bool
    exactPoliticalRequestEstablishedIsTrue : exactPoliticalRequestEstablished ≡ true
    conditionalityOrCoercionAnalysed : Bool
    conditionalityOrCoercionAnalysedIsTrue : conditionalityOrCoercionAnalysed ≡ true
    confidenceVoteConnectionAnalysed : Bool
    confidenceVoteConnectionAnalysedIsTrue : confidenceVoteConnectionAnalysed ≡ true
    viennaArticle41FitReviewed : Bool
    viennaArticle41FitReviewedIsTrue : viennaArticle41FitReviewed ≡ true
    customaryNonInterventionFitReviewed : Bool
    customaryNonInterventionFitReviewedIsTrue : customaryNonInterventionFitReviewed ≡ true
    solomonDomesticLawReviewed : Bool
    solomonDomesticLawReviewedIsTrue : solomonDomesticLawReviewed ≡ true
    contraryGovernmentAccountReviewed : Bool
    contraryGovernmentAccountReviewedIsTrue : contraryGovernmentAccountReviewed ≡ true
    finalLegalConclusion : String

open ForeignInterferenceCharacterisationReceipt public

------------------------------------------------------------------------
-- No-collapse laws inherited from the Mabo/source-attribution discipline.
------------------------------------------------------------------------

data AuthenticatedMessageImpliesForeignInterference : Set where
data OppositionAllegationImpliesForeignInterference : Set where
data FundingCommitmentImpliesCoercion : Set where
data TemporalAssociationImpliesCausation : Set where
data DiplomaticCommunicationCannotBeInterference : Set where

authenticatedMessageDoesNotAutoCharacterise :
  AuthenticatedMessageImpliesForeignInterference → ⊥
authenticatedMessageDoesNotAutoCharacterise ()

oppositionAllegationDoesNotAdjudicate :
  OppositionAllegationImpliesForeignInterference → ⊥
oppositionAllegationDoesNotAdjudicate ()

fundingDoesNotAutoEstablishCoercion : FundingCommitmentImpliesCoercion → ⊥
fundingDoesNotAutoEstablishCoercion ()

timingDoesNotAutoEstablishCausation : TemporalAssociationImpliesCausation → ⊥
timingDoesNotAutoEstablishCausation ()

diplomaticFormDoesNotImmuniseCharacterisation :
  DiplomaticCommunicationCannotBeInterference → ⊥
diplomaticFormDoesNotImmuniseCharacterisation ()

------------------------------------------------------------------------
-- Current exact residual.
------------------------------------------------------------------------

record CurrentForeignInterferenceResidual : Set where
  constructor current-foreign-interference-residual
  field
    verifiedMessageAvailable : Bool
    verifiedMessageAvailableIsTrue : verifiedMessageAvailable ≡ true
    oppositionAllegationAvailable : Bool
    oppositionAllegationAvailableIsTrue : oppositionAllegationAvailable ≡ true
    legalCalibrationAvailable : Bool
    legalCalibrationAvailableIsTrue : legalCalibrationAvailable ≡ true
    exactDefeatMotionAttributionResolved : Bool
    exactDefeatMotionAttributionResolvedIsFalse :
      exactDefeatMotionAttributionResolved ≡ false
    coercionCoordinateResolved : Bool
    coercionCoordinateResolvedIsFalse : coercionCoordinateResolved ≡ false
    causalOutcomeCoordinateResolved : Bool
    causalOutcomeCoordinateResolvedIsFalse : causalOutcomeCoordinateResolved ≡ false
    nextAcquisition : String

open CurrentForeignInterferenceResidual public

currentResidual : CurrentForeignInterferenceResidual
currentResidual = current-foreign-interference-residual
  true refl
  true refl
  true refl
  false refl
  false refl
  false refl
  "Acquire/authenticate the complete communication chain containing any 'defeat this Motion' language and the relevant Solomon Islands domestic-law authorities before promoting the allegation to a legal conclusion"
