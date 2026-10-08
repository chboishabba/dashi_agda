module DASHI.Biology.AutismVaccineClaimPromotionAuditExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import DASHI.Core.Prelude using (⊥)

------------------------------------------------------------------------
-- ATTRIBUTION-FIRST CLAIM AUDIT
------------------------------------------------------------------------

data ClaimSpeaker : Set where
  unidentifiedOct2026Speaker : ClaimSpeaker
  hbomberguy : ClaimSpeaker
  wakefield : ClaimSpeaker
  brianDeer : ClaimSpeaker
  quotedJournalist : ClaimSpeaker
  quotedParent : ClaimSpeaker
  quotedPaper : ClaimSpeaker
  externalScientificSource : ClaimSpeaker
  dashiSynthesis : ClaimSpeaker

data SourceSurface : Set where
  oct2026Transcript : SourceSurface
  measuredResponseTranscript : SourceSurface
  wakefieldLancet1998 : SourceSurface
  lancetRetraction2010 : SourceSurface
  bmjFraudInvestigation2011 : SourceSurface
  hviidDanishCohort2019 : SourceSurface
  cochraneMMRReview2020 : SourceSurface
  microbiomeTransferOpenLabelStudy : SourceSurface
  pronounDepressionMetaEvidence : SourceSurface
  synchronyBondingEvidence : SourceSurface
  otherExternalEvidence : SourceSurface

data ClaimKind : Set where
  fundingPurposeClaim : ClaimKind
  biomedicalAssociationClaim : ClaimKind
  causalMechanismClaim : ClaimKind
  interventionClaim : ClaimKind
  diagnosisClaim : ClaimKind
  individualPsychologyClaim : ClaimKind
  socialPropagationClaim : ClaimKind
  mediaRepresentationClaim : ClaimKind
  conflictOfInterestClaim : ClaimKind
  publicHealthClaim : ClaimKind

data ClaimStatus : Set where
  sourceReportedOnly : ClaimStatus
  supportedBounded : ClaimStatus
  associationOnly : ClaimStatus
  mechanismHypothesisOnly : ClaimStatus
  domainBridgeMissing : ClaimStatus
  claimBlockedPromotion : ClaimStatus
  independentlyCorroborated : ClaimStatus
  unsupported : ClaimStatus

record AttributedClaim : Set where
  constructor attributed-claim
  field
    claimKey : String
    claimSpeaker : ClaimSpeaker
    sourceSurface : SourceSurface
    claimKind : ClaimKind
    boundedReading : String
    status : ClaimStatus
    attributionBoundary : String

open AttributedClaim public

------------------------------------------------------------------------
-- OCTOBER 2026 TRANSCRIPT CLAIMS.
------------------------------------------------------------------------

octGrantFramingClaim : AttributedClaim
octGrantFramingClaim =
  attributed-claim "oct26-grant-depathologisation-framing"
    unidentifiedOct2026Speaker oct2026Transcript fundingPurposeClaim
    "The speaker frames the Australian $455,000 Reframing Autism grant as taxpayer funding to depathologise autism."
    claimBlockedPromotion
    "Amount/recipient and speaker framing remain separate from the government's stated programme purpose."

octGlymphaticAutismClaim : AttributedClaim
octGlymphaticAutismClaim =
  attributed-claim "oct26-glymphatic-autism-severity"
    unidentifiedOct2026Speaker oct2026Transcript biomedicalAssociationClaim
    "The speaker links autism severity to impaired glymphatic clearance and then to dementia risk."
    associationOnly
    "Imaging associations and population dementia-risk observations do not create a causal chain."

octEndogenousOpioidClaim : AttributedClaim
octEndogenousOpioidClaim =
  attributed-claim "oct26-endogenous-opioid-autism"
    unidentifiedOct2026Speaker oct2026Transcript causalMechanismClaim
    "The speaker proposes impaired endogenous-opioid-system function as an autism mechanism and individual explanation."
    claimBlockedPromotion
    "Mechanistic hypotheses do not license individual neurochemical diagnosis from advocacy language or distress."

octFMTAutismClaim : AttributedClaim
octFMTAutismClaim =
  attributed-claim "oct26-fmt-removes-autism-diagnosis"
    unidentifiedOct2026Speaker oct2026Transcript interventionClaim
    "The speaker treats microbiota-transfer results as evidence that autism diagnoses can disappear after FMT."
    claimBlockedPromotion
    "Small uncontrolled multicomponent intervention; symptom-scale cutoff is not diagnostic removal."

octPronounDepressionClaim : AttributedClaim
octPronounDepressionClaim =
  attributed-claim "oct26-pronoun-count-depression"
    unidentifiedOct2026Speaker oct2026Transcript individualPsychologyClaim
    "The speaker treats first-person pronoun frequency in a short quotation as a strong indicator of depression/defence cascade."
    claimBlockedPromotion
    "Weak group-level language correlations do not provide an individual diagnostic classifier."

octSynchronyFalseBeliefClaim : AttributedClaim
octSynchronyFalseBeliefClaim =
  attributed-claim "oct26-synchrony-endorphin-false-belief"
    unidentifiedOct2026Speaker oct2026Transcript individualPsychologyClaim
    "The speaker moves from synchronised bonding to the claim that people confuse pleasurable synchrony with proposition truth."
    claimBlockedPromotion
    "Bonding/pain-threshold evidence does not identify proposition truth or false-belief formation."

------------------------------------------------------------------------
-- ATTACHED H.BOMBERGUY TRANSCRIPT CLAIMS.
------------------------------------------------------------------------

hbombMMRNoLinkClaim : AttributedClaim
hbombMMRNoLinkClaim =
  attributed-claim "hbomb-mmr-autism-no-link"
    hbomberguy measuredResponseTranscript biomedicalAssociationClaim
    "The video states that large subsequent studies do not support an MMR-autism link."
    independentlyCorroborated
    "Independent cohort/review evidence remains separately attributed."

hbombWakefieldRetractionClaim : AttributedClaim
hbombWakefieldRetractionClaim =
  attributed-claim "hbomb-wakefield-paper-retracted"
    hbomberguy measuredResponseTranscript publicHealthClaim
    "The video states that the 1998 Lancet paper was retracted."
    independentlyCorroborated
    "The video claim remains separate from the Lancet/BMJ retraction record."

hbombParentalRecallBoundaryClaim : AttributedClaim
hbombParentalRecallBoundaryClaim =
  attributed-claim "hbomb-parental-temporal-attribution"
    hbomberguy measuredResponseTranscript biomedicalAssociationClaim
    "The video emphasizes that the original timing signal depended substantially on parental attribution of symptom onset after vaccination."
    supportedBounded
    "Temporal succession does not create a causal MMR-to-autism edge."

wakefieldGutOpioidMechanismClaim : AttributedClaim
wakefieldGutOpioidMechanismClaim =
  attributed-claim "wakefield-gut-morphine-like-autism-mechanism"
    wakefield measuredResponseTranscript causalMechanismClaim
    "Wakefield is quoted proposing a gut-derived morphine-like dietary-product mechanism linking vaccine-associated intestinal pathology to autism."
    claimBlockedPromotion
    "This remains Wakefield-attributed; no validated same-object mechanistic causal chain is imported."

hbombMediaAmplificationClaim : AttributedClaim
hbombMediaAmplificationClaim =
  attributed-claim "hbomb-media-amplification-vaccine-fear"
    hbomberguy measuredResponseTranscript socialPropagationClaim
    "The video argues that repeated media coverage amplified MMR-autism concern and vaccine hesitancy."
    mechanismHypothesisOnly
    "A population media-exposure to belief to uptake causal estimand requires its own design."

hbombAutismRepresentationClaim : AttributedClaim
hbombAutismRepresentationClaim =
  attributed-claim "hbomb-autism-tragedy-representation"
    hbomberguy measuredResponseTranscript mediaRepresentationClaim
    "The video criticises media selection of extreme suffering cases and tragedy framing of autism, and argues for accommodation."
    sourceReportedOnly
    "Normative/media-analysis claim; not biomedical vaccine-safety evidence."

hbombConflictOfInterestClaim : AttributedClaim
hbombConflictOfInterestClaim =
  attributed-claim "hbomb-wakefield-conflict-of-interest"
    hbomberguy measuredResponseTranscript conflictOfInterestClaim
    "The video attributes litigation, patent and business conflicts to Wakefield."
    independentlyCorroborated
    "Conflict evidence and biomedical no-association evidence remain separate."

hbombFraudClaim : AttributedClaim
hbombFraudClaim =
  attributed-claim "hbomb-wakefield-fraud"
    hbomberguy measuredResponseTranscript publicHealthClaim
    "The video characterises the Wakefield paper as fraudulent and discusses discrepancies in cases, pathology and recruitment."
    independentlyCorroborated
    "Independent BMJ investigation remains a separate source owner."

canonicalTranscriptClaims : List AttributedClaim
canonicalTranscriptClaims =
  octGrantFramingClaim ∷ octGlymphaticAutismClaim ∷ octEndogenousOpioidClaim ∷
  octFMTAutismClaim ∷ octPronounDepressionClaim ∷ octSynchronyFalseBeliefClaim ∷
  hbombMMRNoLinkClaim ∷ hbombWakefieldRetractionClaim ∷ hbombParentalRecallBoundaryClaim ∷
  wakefieldGutOpioidMechanismClaim ∷ hbombMediaAmplificationClaim ∷
  hbombAutismRepresentationClaim ∷ hbombConflictOfInterestClaim ∷ hbombFraudClaim ∷ []

------------------------------------------------------------------------
-- INDEPENDENT EVIDENCE RECEIPTS.
------------------------------------------------------------------------

data EvidenceShape : Set where
  governmentProgrammeDescription : EvidenceShape
  imagingAssociation : EvidenceShape
  populationCohort : EvidenceShape
  systematicReview : EvidenceShape
  uncontrolledMulticomponentIntervention : EvidenceShape
  caseReport : EvidenceShape
  languageCorrelation : EvidenceShape
  socialSynchronyExperiment : EvidenceShape
  regulatoryRetractionRecord : EvidenceShape
  investigativeRecord : EvidenceShape

record EvidenceReceipt : Set where
  constructor evidence-receipt
  field
    evidenceKey : String
    evidenceSource : SourceSurface
    evidenceShape : EvidenceShape
    paidClaim : String
    evidenceBoundary : String
    causalAuthority : Bool

open EvidenceReceipt public

hviid2019Receipt : EvidenceReceipt
hviid2019Receipt =
  evidence-receipt "hviid-2019-danish-mmr-autism" hviidDanishCohort2019 populationCohort
    "Nationwide Danish cohort: MMR vaccination was not associated with increased autism risk in the studied population."
    "Population observational no-association evidence; not a universal zero-risk theorem." false

cochrane2020Receipt : EvidenceReceipt
cochrane2020Receipt =
  evidence-receipt "cochrane-2020-mmr-autism" cochraneMMRReview2020 systematicReview
    "Review evidence found no evidence of increased autism risk after MMR/MMRV/MMR+V vaccination in included studies."
    "Bounded to included designs/populations and the MMR/autism question." false

lancetRetractionReceipt : EvidenceReceipt
lancetRetractionReceipt =
  evidence-receipt "lancet-2010-retraction" lancetRetraction2010 regulatoryRetractionRecord
    "The Lancet retracted the 1998 Wakefield paper in 2010."
    "Publication/governance fact, not the epidemiologic causal estimate." false

bmjFraudReceipt : EvidenceReceipt
bmjFraudReceipt =
  evidence-receipt "bmj-2011-fraud-investigation" bmjFraudInvestigation2011 investigativeRecord
    "BMJ investigation characterised the Wakefield article as fraudulent and documented discrepancies/conflicts."
    "Pays misconduct/fraud claims; epidemiologic no-association remains separately sourced." false

fmtExploratoryReceipt : EvidenceReceipt
fmtExploratoryReceipt =
  evidence-receipt "fmt-autism-exploratory-multicomponent" microbiomeTransferOpenLabelStudy uncontrolledMulticomponentIntervention
    "Small open-label microbiota-transfer programme reported durable symptom-scale changes in the followed cohort."
    "No randomised control; multicomponent package; symptom cutoff is not diagnosis removal." false

pronounCorrelationReceipt : EvidenceReceipt
pronounCorrelationReceipt =
  evidence-receipt "first-person-pronoun-negative-emotionality" pronounDepressionMetaEvidence languageCorrelation
    "First-person singular language has a small group-level association with depressive symptoms/negative emotionality."
    "Not an individual diagnostic classifier." false

synchronyBondingReceipt : EvidenceReceipt
synchronyBondingReceipt =
  evidence-receipt "social-synchrony-bonding-pain-threshold" synchronyBondingEvidence socialSynchronyExperiment
    "Synchronised group activity can increase bonding and pain-threshold measures used as indirect opioid proxies."
    "Does not measure proposition truth or demonstrate false-belief formation." false

canonicalEvidenceReceipts : List EvidenceReceipt
canonicalEvidenceReceipts =
  hviid2019Receipt ∷ cochrane2020Receipt ∷ lancetRetractionReceipt ∷ bmjFraudReceipt ∷
  fmtExploratoryReceipt ∷ pronounCorrelationReceipt ∷ synchronyBondingReceipt ∷ []

------------------------------------------------------------------------
-- SAME-OBJECT INDEXING.
------------------------------------------------------------------------

record BoundPromotionReceipt (claim : AttributedClaim) (evidence : EvidenceReceipt) : Set where
  constructor bound-promotion-receipt
  field
    claimObjectReference : String
    claimObjectMatches : claimObjectReference ≡ claimKey claim
    evidenceObjectReference : String
    evidenceObjectMatches : evidenceObjectReference ≡ evidenceKey evidence
    targetObjectReference : String
    sameObjectBindingReference : String
    causalIdentificationReference : String

open BoundPromotionReceipt public

------------------------------------------------------------------------
-- PROMOTION GRAPH.
------------------------------------------------------------------------

data PromotionEdge : Set where
  grantRecipientToGrantPurpose : PromotionEdge
  biologicalAssociationToCausalMechanism : PromotionEdge
  groupAssociationToIndividualDiagnosis : PromotionEdge
  autismToOpioidDeficit : PromotionEdge
  opioidHypothesisToIndividualDistress : PromotionEdge
  fmtPackageToFMTSpecificEffect : PromotionEdge
  symptomCutoffToDiagnosisRemoval : PromotionEdge
  pronounCorrelationToIndividualDepression : PromotionEdge
  synchronyToFalseBelief : PromotionEdge
  temporalSequenceToVaccineCausation : PromotionEdge
  caseSeriesToPopulationCausalEffect : PromotionEdge
  conflictOfInterestToBiomedicalNull : PromotionEdge
  mediaRepetitionToBiomedicalTruth : PromotionEdge
  autismRepresentationToVaccineSafety : PromotionEdge
  populationEvidenceToBoundedNoAssociation : PromotionEdge

data EdgeStatus : Set where
  paidBoundedEdge : EdgeStatus
  candidateOnlyEdge : EdgeStatus
  domainBridgeRequiredEdge : EdgeStatus
  blockedPromotion : EdgeStatus

record EdgeAudit : Set where
  constructor edge-audit
  field
    edge : PromotionEdge
    edgeStatus : EdgeStatus
    edgeReason : String

open EdgeAudit public

vaccineToAutismEdge : EdgeAudit
vaccineToAutismEdge = edge-audit temporalSequenceToVaccineCausation blockedPromotion
  "Temporal attribution does not identify an MMR-to-autism causal effect; population evidence independently fails to support the association."

caseSeriesPopulationEdge : EdgeAudit
caseSeriesPopulationEdge = edge-audit caseSeriesToPopulationCausalEffect blockedPromotion
  "A 12-child uncontrolled case series cannot identify a population causal effect."

fmtToDiagnosisRemovalEdge : EdgeAudit
fmtToDiagnosisRemovalEdge = edge-audit symptomCutoffToDiagnosisRemoval blockedPromotion
  "Symptom-scale cutoff after an uncontrolled multicomponent intervention is not diagnosis removal."

fmtSpecificEffectEdge : EdgeAudit
fmtSpecificEffectEdge = edge-audit fmtPackageToFMTSpecificEffect blockedPromotion
  "A multicomponent intervention cannot identify an FMT-specific effect without component-identifying design evidence."

pronounIndividualEdge : EdgeAudit
pronounIndividualEdge = edge-audit pronounCorrelationToIndividualDepression blockedPromotion
  "Weak group-level language correlation does not identify an individual's depression state."

synchronyToFalseBeliefEdge : EdgeAudit
synchronyToFalseBeliefEdge = edge-audit synchronyToFalseBelief blockedPromotion
  "Bonding/opioid-proxy effects do not identify proposition truth or false-belief formation."

conflictBiomedicalEdge : EdgeAudit
conflictBiomedicalEdge = edge-audit conflictOfInterestToBiomedicalNull blockedPromotion
  "Conflict/misconduct evidence does not itself prove the biomedical null."

mediaTruthEdge : EdgeAudit
mediaTruthEdge = edge-audit mediaRepetitionToBiomedicalTruth blockedPromotion
  "Media repetition may alter salience/belief but cannot determine biomedical truth."

autismRepresentationSafetyEdge : EdgeAudit
autismRepresentationSafetyEdge = edge-audit autismRepresentationToVaccineSafety blockedPromotion
  "Autism-representation critique is socially relevant but not vaccine-safety evidence."

boundedPopulationNoAssociationEdge : EdgeAudit
boundedPopulationNoAssociationEdge = edge-audit populationEvidenceToBoundedNoAssociation paidBoundedEdge
  "Large cohort and systematic-review evidence pay a bounded MMR/autism no-association conclusion."

canonicalEdgeAudit : List EdgeAudit
canonicalEdgeAudit =
  vaccineToAutismEdge ∷ caseSeriesPopulationEdge ∷ fmtToDiagnosisRemovalEdge ∷
  fmtSpecificEffectEdge ∷ pronounIndividualEdge ∷ synchronyToFalseBeliefEdge ∷
  conflictBiomedicalEdge ∷ mediaTruthEdge ∷ autismRepresentationSafetyEdge ∷
  boundedPopulationNoAssociationEdge ∷ []

------------------------------------------------------------------------
-- NO-GO PERMISSIONS.
------------------------------------------------------------------------

data TemporalSequenceCreatesVaccineCausationPermission : Set where
data SymptomCutoffCreatesDiagnosisRemovalPermission : Set where
data PronounCountCreatesIndividualDiagnosisPermission : Set where
data SynchronyCreatesFalseBeliefPermission : Set where
data ConflictCreatesBiomedicalNullPermission : Set where
data MediaRepetitionCreatesBiomedicalTruthPermission : Set where
data RepresentationCritiqueCreatesVaccineSafetyPermission : Set where

temporalSequenceDoesNotCreateVaccineCausation : TemporalSequenceCreatesVaccineCausationPermission → ⊥
temporalSequenceDoesNotCreateVaccineCausation ()
symptomCutoffDoesNotCreateDiagnosisRemoval : SymptomCutoffCreatesDiagnosisRemovalPermission → ⊥
symptomCutoffDoesNotCreateDiagnosisRemoval ()
pronounCountDoesNotCreateIndividualDiagnosis : PronounCountCreatesIndividualDiagnosisPermission → ⊥
pronounCountDoesNotCreateIndividualDiagnosis ()
synchronyDoesNotCreateFalseBelief : SynchronyCreatesFalseBeliefPermission → ⊥
synchronyDoesNotCreateFalseBelief ()
conflictDoesNotCreateBiomedicalNull : ConflictCreatesBiomedicalNullPermission → ⊥
conflictDoesNotCreateBiomedicalNull ()
mediaRepetitionDoesNotCreateBiomedicalTruth : MediaRepetitionCreatesBiomedicalTruthPermission → ⊥
mediaRepetitionDoesNotCreateBiomedicalTruth ()
representationCritiqueDoesNotCreateVaccineSafety : RepresentationCritiqueCreatesVaccineSafetyPermission → ⊥
representationCritiqueDoesNotCreateVaccineSafety ()

------------------------------------------------------------------------
-- STUDY SURFACES.
------------------------------------------------------------------------

record WakefieldCaseSeriesSurface : Set where
  constructor wakefield-case-series-surface
  field
    sampleSize : Nat
    hasConcurrentControlGroup : Bool
    parentalTemporalAttributionRepresented : Bool
    populationCausalEstimandIdentified : Bool
    paperRetracted : Bool
    independentPopulationNoAssociationEvidenceExists : Bool

open WakefieldCaseSeriesSurface public

canonicalWakefieldCaseSeriesSurface : WakefieldCaseSeriesSurface
canonicalWakefieldCaseSeriesSurface = wakefield-case-series-surface 12 false true false true true

record FMTAutismStudySurface : Set where
  constructor fmt-autism-study-surface
  field
    openLabel : Bool
    randomizedControl : Bool
    multicomponentTreatment : Bool
    symptomScaleObserved : Bool
    symptomScaleCutoffIsFormalDiagnosticRemoval : Bool
    fmtComponentSpecificCausalEffectIdentified : Bool

open FMTAutismStudySurface public

canonicalFMTAutismStudySurface : FMTAutismStudySurface
canonicalFMTAutismStudySurface = fmt-autism-study-surface true false true true false false

record InformationPropagationBoundary : Set where
  constructor information-propagation-boundary
  field
    sourceAuthorityCanChangeBelief : Bool
    repetitionCanChangeSalience : Bool
    mediaExposureCanBeCausalResearchQuestion : Bool
    repetitionDeterminesTruth : Bool
    authorityDeterminesTruth : Bool
    biomedicalTruthDeterminesEthicalRepresentation : Bool
    ethicalRepresentationDeterminesBiomedicalTruth : Bool

canonicalInformationPropagationBoundary : InformationPropagationBoundary
canonicalInformationPropagationBoundary = information-propagation-boundary true true true false false false false

------------------------------------------------------------------------
-- TERMINAL BOUNDARY.
------------------------------------------------------------------------

record AutismVaccineAuditBoundary : Set where
  constructor autism-vaccine-audit-boundary
  field
    sourceVoicesSeparated : Bool
    sourceVoicesSeparatedIsTrue : sourceVoicesSeparated ≡ true
    sourceReportCreatesTruth : Bool
    sourceReportCreatesTruthIsFalse : sourceReportCreatesTruth ≡ false
    independentEvidenceKeptSeparate : Bool
    independentEvidenceKeptSeparateIsTrue : independentEvidenceKeptSeparate ≡ true
    associationCreatesCausation : Bool
    associationCreatesCausationIsFalse : associationCreatesCausation ≡ false
    symptomCutoffEqualsDiagnosisRemoval : Bool
    symptomCutoffEqualsDiagnosisRemovalIsFalse : symptomCutoffEqualsDiagnosisRemoval ≡ false
    pronounCountDiagnosesIndividual : Bool
    pronounCountDiagnosesIndividualIsFalse : pronounCountDiagnosesIndividual ≡ false
    synchronyCreatesFalseBelief : Bool
    synchronyCreatesFalseBeliefIsFalse : synchronyCreatesFalseBelief ≡ false
    conflictOfInterestProvesBiomedicalNull : Bool
    conflictOfInterestProvesBiomedicalNullIsFalse : conflictOfInterestProvesBiomedicalNull ≡ false
    mediaPropagationDeterminesBiomedicalTruth : Bool
    mediaPropagationDeterminesBiomedicalTruthIsFalse : mediaPropagationDeterminesBiomedicalTruth ≡ false
    autismRepresentationDeterminesVaccineSafety : Bool
    autismRepresentationDeterminesVaccineSafetyIsFalse : autismRepresentationDeterminesVaccineSafety ≡ false
    mmrAutismNoAssociationBoundedEvidenceRepresented : Bool
    mmrAutismNoAssociationBoundedEvidenceRepresentedIsTrue : mmrAutismNoAssociationBoundedEvidenceRepresented ≡ true
    sameObjectBindingRequiredForPromotion : Bool
    sameObjectBindingRequiredForPromotionIsTrue : sameObjectBindingRequiredForPromotion ≡ true

open AutismVaccineAuditBoundary public

canonicalAuditBoundary : AutismVaccineAuditBoundary
canonicalAuditBoundary =
  autism-vaccine-audit-boundary
    true refl false refl true refl false refl false refl false refl false refl false refl false refl true refl true refl
