module DASHI.Governance.MostazafinRepresentedConstituencyDivergenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Governance.IRGCMostazafinInstitutionalGrammarMechanismExact as Grammar

------------------------------------------------------------------------
-- MOSTAZAFIN: REPRESENTED CONSTITUENCY / INSTITUTIONAL CARRIER /
-- EMPIRICAL COHORT / STATE-ACTION DIVERGENCE
------------------------------------------------------------------------

iranicaKhomeiniFoundation : Source.AttributedSource
iranicaKhomeiniFoundation = Source.mkNoDOISource
  "Encyclopaedia Iranica"
  "Khomeini i. Life"
  "Encyclopaedia Iranica"
  "2021"
  "https://www.iranicaonline.org/articles/khomeini-i-life/"
  (Source.namedSourceKind "reference work")
  "historical source: Khomeini ordered confiscated Pahlavi-associated assets into the Foundation for the Downtrodden, initially framed as serving the poor"
  Source.publicAttribution

iranicaBasij : Source.AttributedSource
iranicaBasij = Source.mkNoDOISource
  "Encyclopaedia Iranica"
  "Islam in Iran xiii. Islamic Political Movements in 20th Century Iran"
  "Encyclopaedia Iranica"
  "2008"
  "https://www.iranicaonline.org/articles/islam-in-iran-xiii-islamic-political-movements-in-20th-century-iran/"
  (Source.namedSourceKind "reference work")
  "historical source naming the Basij-e Mostazafin as an organization affiliated with the Revolutionary Guards"
  Source.publicAttribution

hrwLabour2022 : Source.AttributedSource
hrwLabour2022 = Source.mkNoDOISource
  "Human Rights Watch"
  "Iran: Labor Protests Surge"
  "Human Rights Watch"
  "2022-04-29"
  "https://www.hrw.org/news/2022/04/29/iran-labor-protests-surge"
  (Source.namedSourceKind "human-rights NGO report")
  "documents increased labor protests amid deteriorating economic conditions and repression/prosecution of labor activists"
  Source.publicAttribution

hrwIran2026 : Source.AttributedSource
hrwIran2026 = Source.mkNoDOISource
  "Human Rights Watch"
  "World Report 2026: Iran"
  "Human Rights Watch"
  "2026"
  "https://www.hrw.org/world-report/2026/country-chapters/iran"
  (Source.namedSourceKind "human-rights NGO report")
  "documents lethal crackdown, mass arrests, executions and repression of dissent; this source does not itself classify all victims as mostazafin"
  Source.publicAttribution

data RepresentedLayer : Set where
  revolutionarySubject : RepresentedLayer
  constitutionalForeignPolicySubject : RepresentedLayer
  charitableInstitutionName : RepresentedLayer
  securityInstitutionName : RepresentedLayer
  empiricalLabourCohort : RepresentedLayer
  empiricalProtestCohort : RepresentedLayer

record RepresentedConstituencyReceipt : Set where
  constructor represented-constituency-receipt
  field
    layer : RepresentedLayer
    sourceRef : String
    boundedReading : String
    sourcePaid : Bool
    sourcePaidIsTrue : sourcePaid ≡ true
    equalsEveryWorker : Bool
    equalsEveryWorkerIsFalse : equalsEveryWorker ≡ false
    equalsEveryProtester : Bool
    equalsEveryProtesterIsFalse : equalsEveryProtester ≡ false

open RepresentedConstituencyReceipt public

ideologicalMostazafin : RepresentedConstituencyReceipt
ideologicalMostazafin =
  represented-constituency-receipt
    revolutionarySubject
    "IRGCMostazafinInstitutionalGrammarMechanismExact.glombitza2026"
    "Shariati globalised the Quranic mostazafin category and Khomeini institutionalised an oppressed-versus-oppressor revolutionary grammar."
    true refl false refl false refl

foundationCarrier : RepresentedConstituencyReceipt
foundationCarrier =
  represented-constituency-receipt
    charitableInstitutionName
    "Encyclopaedia Iranica: Khomeini i. Life"
    "Foundation for the Downtrodden institutionalises the vocabulary in an economic/charitable body."
    true refl false refl false refl

basijCarrier : RepresentedConstituencyReceipt
basijCarrier =
  represented-constituency-receipt
    securityInstitutionName
    "Encyclopaedia Iranica: Islamic Political Movements"
    "Basij-e Mostazafin institutionalises the same lexical category in a security/mobilisation organisation."
    true refl false refl false refl

data OverlapStatus : Set where
  noIdentityClaim : OverlapStatus
  candidateOverlapRequiresCaseEvidence : OverlapStatus
  caseSpecificOverlapPaid : OverlapStatus

record StateActionDivergenceCandidate : Set where
  constructor state-action-divergence-candidate
  field
    representedReceipt : RepresentedConstituencyReceipt
    empiricalCohortRef : String
    stateActionRef : String
    overlapStatus : OverlapStatus
    institutionalVocabularyPersists : Bool
    institutionalVocabularyPersistsIsTrue :
      institutionalVocabularyPersists ≡ true
    repressionDocumented : Bool
    repressionDocumentedIsTrue : repressionDocumented ≡ true
    samePersonsProved : Bool
    samePersonsProvedIsFalse : samePersonsProved ≡ false
    semanticParadoxClosed : Bool
    semanticParadoxClosedIsFalse : semanticParadoxClosed ≡ false

open StateActionDivergenceCandidate public

labourDivergenceCandidate : StateActionDivergenceCandidate
labourDivergenceCandidate =
  state-action-divergence-candidate
    ideologicalMostazafin
    "HRW 2022: labor activists/workers protesting wages and living standards"
    "HRW 2022: arrests/prosecutions/repression of labor activists"
    candidateOverlapRequiresCaseEvidence
    true refl
    true refl
    false refl
    false refl

protestDivergenceCandidate : StateActionDivergenceCandidate
protestDivergenceCandidate =
  state-action-divergence-candidate
    ideologicalMostazafin
    "HRW 2026: nationwide protest participants and bystanders"
    "HRW 2026: lethal crackdown and mass arrests"
    candidateOverlapRequiresCaseEvidence
    true refl
    true refl
    false refl
    false refl

record MostazafinDivergenceBoundary : Set where
  constructor mostazafin-divergence-boundary
  field
    ideologyInstitutionSecurityLayersSeparated : Bool
    workerAndMostazafinSeparated : Bool
    protesterAndMostazafinSeparated : Bool
    vocabularyPersistenceDoesNotProveProtection : Bool
    repressionDoesNotEraseHistoricalMeaningAutomatically : Bool
    caseSpecificOverlapRequiredForStrongParadox : Bool

canonicalBoundary : MostazafinDivergenceBoundary
canonicalBoundary =
  mostazafin-divergence-boundary true true true true true true

data InstitutionalNameGuaranteesRepresentedSubjectProtection : Set where
data RepressedWorkerIsDefinitionallyMostazafin : Set where
data RepressionMeansTermLostAllMeaning : Set where

institutionalNameDoesNotGuaranteeProtection :
  InstitutionalNameGuaranteesRepresentedSubjectProtection → ⊥
institutionalNameDoesNotGuaranteeProtection ()

workerDoesNotDefinitionallyEqualMostazafin :
  RepressedWorkerIsDefinitionallyMostazafin → ⊥
workerDoesNotDefinitionallyEqualMostazafin ()

repressionDoesNotByItselfProveSemanticExtinction :
  RepressionMeansTermLostAllMeaning → ⊥
repressionDoesNotByItselfProveSemanticExtinction ()

grammarContinuity : Grammar.InstitutionalGrammarMechanism
grammarContinuity = Grammar.canonicalMostazafinContinuity

iranicaFoundationSnowball : Snowball.SourceRoleSnowballReceipt iranicaKhomeiniFoundation
iranicaFoundationSnowball = Snowball.canonicalSourceRoleSnowballReceipt iranicaKhomeiniFoundation

hrwLabourSnowball : Snowball.SourceRoleSnowballReceipt hrwLabour2022
hrwLabourSnowball = Snowball.canonicalSourceRoleSnowballReceipt hrwLabour2022
