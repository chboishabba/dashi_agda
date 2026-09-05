module DASHI.Cognition.PNF.SensibLawMaboPrimaryTextParserBatchMaterialisedExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.NumericAuthority as Authority
import DASHI.Cognition.PNF.SpacyNumericProjection as Spacy
import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as Candidate
import DASHI.Cognition.PNF.SensibLawPdfReportingAttributionMaterialisedLiveExact as Applicant

record PrimaryTextSpecimenReceipt : Set where
  constructor primaryTextSpecimenReceipt
  field
    specimenId sourcePdf sourcePassage reviewedContext fixtureSha256 : String
    bytes paragraphs sentences reportingPredicates : Nat
    authority : String
    parserModel : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    parserAloneAuthorizesTruth : Bool
    parserAloneAuthorizesTruthIsFalse : parserAloneAuthorizesTruth ≡ false
    parserAloneAuthorizesOccurrence : Bool
    parserAloneAuthorizesOccurrenceIsFalse : parserAloneAuthorizesOccurrence ≡ false
    governedAdmissionPresent : Bool
    governedAdmissionPresentIsFalse : governedAdmissionPresent ≡ false
open PrimaryTextSpecimenReceipt public

applicantSpecimen : PrimaryTextSpecimenReceipt
applicantSpecimen = primaryTextSpecimenReceipt
  "native-title-applicant-submission-context"
  "../ITIR-suite/SensibLaw/Native Title (New South Wales) Act 1994 (NSW).pdf"
  "Wilson v Anderson [2002] HCA 29, paragraph 62, reproduced in the NSW compilation"
  "party submission; not a court finding"
  "84eeb6e3b6900521796fd1d669b7f8b1998d652ce8fed0a98fc0486b01e2a01d"
  515 1 3 1
  "parser_observation_and_candidate_status_only" "en_core_web_sm"
  true refl false refl false refl false refl

brennanSpecimen : PrimaryTextSpecimenReceipt
brennanSpecimen = primaryTextSpecimenReceipt
  "mabo-brennan-majority-native-title"
  "../ITIR-suite/SensibLaw/Mabo [No 2] - [1992] HCA 23.pdf"
  "Mabo (No 2), Brennan J, paragraphs 61-62"
  "judicial reasoning; source attribution is metadata"
  "083461eb6f0431f88141df66d6108256c6ffc934d74c815566ecd5328a80f6dd"
  2022 2 8 2
  "parser_observation_and_candidate_status_only" "en_core_web_sm"
  true refl false refl false refl false refl

dawsonSpecimen : PrimaryTextSpecimenReceipt
dawsonSpecimen = primaryTextSpecimenReceipt
  "mabo-dawson-contrasting-native-title"
  "../ITIR-suite/SensibLaw/Mabo [No 2] - [1992] HCA 23.pdf"
  "Mabo (No 2), Dawson J, paragraphs 13-14"
  "contrasting judicial reasoning; source attribution is metadata"
  "3d9b01edfc4d5ee5a086079609017e464ff0da2c8d6a2e9efa30998d6fde4eb1"
  886 2 3 0
  "parser_observation_and_candidate_status_only" "en_core_web_sm"
  true refl false refl false refl false refl

applicantReportingWitness : Candidate.DependencyWitness
applicantReportingWitness = Applicant.reportingSourceWitness
applicantEmbeddedContentWitness : Candidate.DependencyWitness
applicantEmbeddedContentWitness = Applicant.embeddedCcompWitness

sym : Nat → Authority.SymbolId
sym = Authority.symbolId
ann : Nat → Spacy.NumericAnnotation
ann n = Spacy.annotationPresent (sym n)

brennanSentence0 : Authority.SentenceId
brennanSentence0 = Authority.sentenceId 0
brennanNotToken : Spacy.SpacyTokenObservation
brennanNotToken = Spacy.spacyTokenObservation
  (Authority.tokenId 61018) brennanSentence0 18 99 102 (sym 61018)
  (Spacy.parserLemma (sym 62018)) (ann 63018) (ann 64018) (ann 65018)
  Spacy.nothing (Spacy.declaredHeadAt 103 113)
brennanExtinguishToken : Spacy.SpacyTokenObservation
brennanExtinguishToken = Spacy.spacyTokenObservation
  (Authority.tokenId 61019) brennanSentence0 19 103 113 (sym 61019)
  (Spacy.parserLemma (sym 62019)) (ann 63019) (ann 64019) (ann 65019)
  Spacy.nothing (Spacy.declaredHeadAt 57 59)
brennanTitleToken : Spacy.SpacyTokenObservation
brennanTitleToken = Spacy.spacyTokenObservation
  (Authority.tokenId 61021) brennanSentence0 21 121 126 (sym 61021)
  (Spacy.parserLemma (sym 62021)) (ann 63021) (ann 64021) (ann 65021)
  Spacy.nothing (Spacy.declaredHeadAt 103 113)
brennanNegationWitness : Candidate.DependencyWitness
brennanNegationWitness = Candidate.dependencyWitness brennanNotToken brennanExtinguishToken Candidate.negation
  "receipt Brennan sentence 0: neg(extinguish, not), spans 99:102 -> 103:113"
brennanExtinguishObjectWitness : Candidate.DependencyWitness
brennanExtinguishObjectWitness = Candidate.dependencyWitness brennanTitleToken brennanExtinguishToken Candidate.directObject
  "receipt Brennan sentence 0: dobj(extinguish, title), spans 121:126 -> 103:113"

brennanSentence3 : Authority.SentenceId
brennanSentence3 = Authority.sentenceId 3
brennanIfToken : Spacy.SpacyTokenObservation
brennanIfToken = Spacy.spacyTokenObservation
  (Authority.tokenId 61300) brennanSentence3 0 788 790 (sym 61300)
  (Spacy.parserLemma (sym 62300)) (ann 63300) (ann 64300) (ann 65300)
  Spacy.nothing (Spacy.declaredHeadAt 804 812)
brennanSurvivesToken : Spacy.SpacyTokenObservation
brennanSurvivesToken = Spacy.spacyTokenObservation
  (Authority.tokenId 61303) brennanSentence3 3 804 812 (sym 61303)
  (Spacy.parserLemma (sym 62303)) (ann 63303) (ann 64303) (ann 65303)
  Spacy.nothing (Spacy.declaredHeadAt 880 882)
brennanRootIsToken : Spacy.SpacyTokenObservation
brennanRootIsToken = Spacy.spacyTokenObservation
  (Authority.tokenId 61320) brennanSentence3 20 880 882 (sym 61320)
  (Spacy.parserLemma (sym 62320)) (ann 63320) (ann 64320) (ann 65320)
  Spacy.nothing Spacy.declaredSelfHead
brennanConditionalClauseWitness : Candidate.DependencyWitness
brennanConditionalClauseWitness = Candidate.dependencyWitness brennanSurvivesToken brennanRootIsToken Candidate.adverbialClause
  "receipt Brennan sentence 3: advcl(root-is, survives), spans 804:812 -> 880:882; If marker span 788:790 retained separately"

brennanSentence6 : Authority.SentenceId
brennanSentence6 = Authority.sentenceId 6
brennanStateToken : Spacy.SpacyTokenObservation
brennanStateToken = Spacy.spacyTokenObservation
  (Authority.tokenId 61604) brennanSentence6 4 1533 1538 (sym 61604)
  (Spacy.parserLemma (sym 62604)) (ann 63604) (ann 64604) (ann 65604)
  Spacy.nothing (Spacy.declaredHeadAt 1519 1529)
brennanRejectsToken : Spacy.SpacyTokenObservation
brennanRejectsToken = Spacy.spacyTokenObservation
  (Authority.tokenId 61616) brennanSentence6 16 1588 1595 (sym 61616)
  (Spacy.parserLemma (sym 62616)) (ann 63616) (ann 64616) (ann 65616)
  Spacy.nothing (Spacy.declaredHeadAt 1533 1538)
brennanStateContentWitness : Candidate.DependencyWitness
brennanStateContentWitness = Candidate.dependencyWitness brennanRejectsToken brennanStateToken Candidate.clausalComplement
  "receipt Brennan sentence 6: ccomp(state, rejects), spans 1588:1595 -> 1533:1538"

dawsonSentence0 : Authority.SentenceId
dawsonSentence0 = Authority.sentenceId 0
dawsonIToken : Spacy.SpacyTokenObservation
dawsonIToken = Spacy.spacyTokenObservation
  (Authority.tokenId 71006) dawsonSentence0 6 24 25 (sym 71006)
  (Spacy.parserLemma (sym 72006)) (ann 73006) (ann 74006) (ann 75006)
  Spacy.nothing (Spacy.declaredHeadAt 26 31)
dawsonThinkToken : Spacy.SpacyTokenObservation
dawsonThinkToken = Spacy.spacyTokenObservation
  (Authority.tokenId 71007) dawsonSentence0 7 26 31 (sym 71007)
  (Spacy.parserLemma (sym 72007)) (ann 73007) (ann 74007) (ann 75007)
  Spacy.nothing (Spacy.declaredHeadAt 174 176)
dawsonBeToken : Spacy.SpacyTokenObservation
dawsonBeToken = Spacy.spacyTokenObservation
  (Authority.tokenId 71010) dawsonSentence0 10 40 42 (sym 71010)
  (Spacy.parserLemma (sym 72010)) (ann 73010) (ann 74010) (ann 75010)
  Spacy.nothing (Spacy.declaredHeadAt 26 31)
dawsonViewpointSubjectWitness : Candidate.DependencyWitness
dawsonViewpointSubjectWitness = Candidate.dependencyWitness dawsonIToken dawsonThinkToken Candidate.nominalSubject
  "receipt Dawson sentence 0: nsubj(think, I), spans 24:25 -> 26:31"
dawsonModalContentWitness : Candidate.DependencyWitness
dawsonModalContentWitness = Candidate.dependencyWitness dawsonBeToken dawsonThinkToken Candidate.clausalComplement
  "receipt Dawson sentence 0: ccomp(think, be), spans 40:42 -> 26:31; modal must attaches to embedded be"

data ParserBatchProvesJudicialHolding : Set where
data ReportingPredicateCountDeterminesDiscourseRole : Set where
data NoReportingPredicateMeansNoJudicialViewpoint : Set where
data FiveParagraphBatchIsGeneralParserCoverage : Set where
parserBatchDoesNotProveHolding : ParserBatchProvesJudicialHolding → ⊥
parserBatchDoesNotProveHolding ()
reportingCountDoesNotDetermineDiscourseRole : ReportingPredicateCountDeterminesDiscourseRole → ⊥
reportingCountDoesNotDetermineDiscourseRole ()
noReportingPredicateDoesNotEraseViewpoint : NoReportingPredicateMeansNoJudicialViewpoint → ⊥
noReportingPredicateDoesNotEraseViewpoint ()
fiveParagraphBatchDoesNotClaimGeneralCoverage : FiveParagraphBatchIsGeneralParserCoverage → ⊥
fiveParagraphBatchDoesNotClaimGeneralCoverage ()

record PrimaryTextBatchBoundary : Set where
  constructor primaryTextBatchBoundary
  field exactHashesRetained parserCandidatesOnly applicantSubmissionIsCourtFinding reportingLexiconIsSemanticAuthority zeroReportingPredicatesMeansNoDiscourseStructure fiveParagraphsClaimCorpusCoverage : Bool
canonicalPrimaryTextBatchBoundary : PrimaryTextBatchBoundary
canonicalPrimaryTextBatchBoundary = primaryTextBatchBoundary true true false false false false
