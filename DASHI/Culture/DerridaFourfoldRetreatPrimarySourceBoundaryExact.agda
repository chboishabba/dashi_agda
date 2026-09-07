module DASHI.Culture.DerridaFourfoldRetreatPrimarySourceBoundaryExact where

------------------------------------------------------------------------
-- DERRIDA PRIMARY-SOURCE BOUNDARY FOR FOURFOLD-RETREAT TESTING
--
-- Attribution discipline:
--   Derrida source proposition
--   != later interpretation
--   != DASHI axis appraisal
--   != whole-work doctrine
--   != empirical/historical population law.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Source metadata and carrier roles.
------------------------------------------------------------------------

data SourceRole : Set where
  primaryEssay : SourceRole
  primaryInterview : SourceRole
  publisherMetadata : SourceRole
  accessTranscript : SourceRole
  accessReproduction : SourceRole


record DerridaSourceReceipt : Set where
  constructor derrida-source-receipt
  field
    upstreamAuthor : String
    interlocutorOrEditor : String
    title : String
    publicationCarrier : String
    publicationYear : String
    doiOrStableIdentifier : String
    canonicalPublicationLocation : String
    accessLocation : String
    accessCarrierRole : SourceRole
    exactSourceLocation : String
    boundedProposition : String
    dashIInterpretation : String
    wholeDoctrineAuthority : Bool
    namedAxisClosureAuthority : Bool

open DerridaSourceReceipt public

------------------------------------------------------------------------
-- 1. Structure, Sign, and Play in the Discourse of the Human Sciences.
------------------------------------------------------------------------

structureSignPlayReceipt : DerridaSourceReceipt
structureSignPlayReceipt =
  derrida-source-receipt
    "Jacques Derrida"
    "lecture delivered at Johns Hopkins; later translated by Alan Bass"
    "Structure, Sign, and Play in the Discourse of the Human Sciences"
    "lecture 21 Oct 1966; later in Writing and Difference"
    "1966 / later book publication"
    "book chapter; no DOI asserted here"
    "Writing and Difference, trans. Alan Bass, Routledge"
    "hydra.humanities.uci.edu/derrida/sign-play.html"
    accessReproduction
    "opening pages on the centered structure, fixed origin and point of presence"
    "Derrida criticises the traditional centering of structure in a fixed origin or point of presence and analyzes the resulting limits on structural play."
    "This directly supports a critique of foundational centering; it does not by itself establish rejection of reason, truth, materiality or politics."
    false false

------------------------------------------------------------------------
-- 2. Force of Law.
------------------------------------------------------------------------

forceOfLawReceipt : DerridaSourceReceipt
forceOfLawReceipt =
  derrida-source-receipt
    "Jacques Derrida"
    "translated bilingual publication"
    "Force of Law: The Mystical Foundation of Authority"
    "Cardozo Law Review 11 (1989-1990), lecture/text published 1990"
    "1990"
    "no DOI asserted here"
    "Cardozo Law Review"
    "public reproduced bilingual text / indexed access copy"
    accessReproduction
    "discussion of calculable law and incalculable justice; later paragraph on juridico-political struggles"
    "Derrida distinguishes calculable law from incalculable justice, insists that justice requires calculation with the incalculable, and says the excess of justice over law cannot serve as an alibi for withdrawal from juridico-political struggles."
    "The source supplies direct counterevidence to a simple equation of deconstruction with rejection of calculation or political engagement."
    false false

------------------------------------------------------------------------
-- 3. Interview with Laure Zhang, 29 February 2000.
--
-- This is a primary interview utterance by Derrida.  The 2020 ITER page is an
-- access/publication carrier for the French version; the editors state that
-- the interview first appeared as the preface to the Chinese translation of
-- Writing and Difference (Beijing 2001; Taipei 2004).
------------------------------------------------------------------------

reasonNotIrrationalismReceipt : DerridaSourceReceipt
reasonNotIrrationalismReceipt =
  derrida-source-receipt
    "Jacques Derrida"
    "Laure Zhang (Zhang Ning), interviewer and Chinese translator"
    "Entretien avec Jacques Derrida en préface à la traduction chinoise de L’écriture et la différence"
    "preface to Chinese translation; French publication in Revue ITER no. 2"
    "interview 29 Feb 2000; French publication 2020"
    "no DOI asserted here"
    "Chinese translation preface: Beijing 2001 / Taipei 2004; French publication Revue ITER no. 2, 2020"
    "revue-iter.org/laure-zhang-entretien-avec-jacques-derrida-en-preface-a-la-traduction-chinoise-de-lecriture-et-la-difference/"
    accessTranscript
    "answer to question on the moving limit between philosophical and non-philosophical discourse; passage discussing reason and accusations of irrationalism"
    "Derrida explicitly distinguishes questioning the origin/history of reason from irrationalism and says such questioning is not thereby a rejection or denunciation of reason."
    "This is direct first-person source evidence against automatically promoting critique of reason to irrationalism."
    false false

------------------------------------------------------------------------
-- Axis-status language avoids premature Boolean closure.
------------------------------------------------------------------------

data AxisEvidenceStatus : Set where
  directCounterevidenceToSimpleRetreat : AxisEvidenceStatus
  critiquePresentButRetreatUnclosed : AxisEvidenceStatus
  openNeedsBroaderPrimaryCorpus : AxisEvidenceStatus


data FourfoldAxis : Set where
  classAxis : FourfoldAxis
  imperialismAxis : FourfoldAxis
  materialismScienceAxis : FourfoldAxis
  reasonAxis : FourfoldAxis

derridaAxisStatus : FourfoldAxis → AxisEvidenceStatus
derridaAxisStatus classAxis = openNeedsBroaderPrimaryCorpus
derridaAxisStatus imperialismAxis = openNeedsBroaderPrimaryCorpus
derridaAxisStatus materialismScienceAxis = openNeedsBroaderPrimaryCorpus
derridaAxisStatus reasonAxis = directCounterevidenceToSimpleRetreat

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data FoundationalCritiqueProvesIrrationalism : Set where
data IncalculableJusticeProvesAntiCalculation : Set where
data DeconstructionProvesPoliticalWithdrawal : Set where
data SelectedTextsCloseWholeDerridaDoctrine : Set where
data InterviewAccessCarrierOwnsUtterance : Set where

data ReasonCounterevidenceClosesAllFourAxes : Set where

foundationalCritiqueDoesNotProveIrrationalism :
  FoundationalCritiqueProvesIrrationalism → ⊥
foundationalCritiqueDoesNotProveIrrationalism ()

incalculableJusticeDoesNotProveAntiCalculation :
  IncalculableJusticeProvesAntiCalculation → ⊥
incalculableJusticeDoesNotProveAntiCalculation ()

deconstructionDoesNotProvePoliticalWithdrawal :
  DeconstructionProvesPoliticalWithdrawal → ⊥
deconstructionDoesNotProvePoliticalWithdrawal ()

selectedTextsDoNotCloseWholeDerridaDoctrine :
  SelectedTextsCloseWholeDerridaDoctrine → ⊥
selectedTextsDoNotCloseWholeDerridaDoctrine ()

interviewAccessCarrierDoesNotOwnUtterance :
  InterviewAccessCarrierOwnsUtterance → ⊥
interviewAccessCarrierDoesNotOwnUtterance ()

reasonCounterevidenceDoesNotCloseAllFourAxes :
  ReasonCounterevidenceClosesAllFourAxes → ⊥
reasonCounterevidenceDoesNotCloseAllFourAxes ()

record DerridaFourfoldSourceBoundary : Set where
  constructor derrida-fourfold-source-boundary
  field
    foundationalCenterCritiqueRecovered : Bool
    calculationRequiredWithinJusticeRecovered : Bool
    politicalWithdrawalDisclaimedInForceOfLaw : Bool
    reasonQuestioningDistinguishedFromIrrationalism : Bool
    irrationalismEstablished : Bool
    classRetreatClosed : Bool
    imperialismRetreatClosed : Bool
    materialismRetreatClosed : Bool
    allFourRetreatsClosed : Bool
    strongerAxisClaimsRequireMorePrimarySources : Bool

canonicalDerridaFourfoldSourceBoundary : DerridaFourfoldSourceBoundary
canonicalDerridaFourfoldSourceBoundary =
  derrida-fourfold-source-boundary
    true true true true false false false false false true
