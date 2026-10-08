module DASHI.Biology.AutismVaccineClaimPromotionAuditExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import DASHI.Core.Prelude using (⊥)

------------------------------------------------------------------------
-- ATTRIBUTION-FIRST CLAIM AUDIT
--
-- This owner formalises two user-supplied transcript surfaces without
-- collapsing speaker, quoted source, external evidence, and DASHI synthesis.
-- Recording a source claim is not endorsement.  Independent evidence receipts
-- are separate objects and only pay the scope they explicitly name.
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
  blockedPromotion : ClaimStatus
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
-- ORIGINAL OCTOBER 2026 TRANSCRIPT: bounded claims from the prior fact-check.
------------------------------------------------------------------------

octGrantFramingClaim : AttributedClaim
octGrantFramingClaim =
  attributed-claim
    "oct26-grant-depathologisation-framing"
    unidentifiedOct2026Speaker
    oct2026Transcript
    fundingPurposeClaim
    "The speaker frames the Australian $455,000 Reframing Autism grant as taxpayer funding to depathologise autism."
    blockedPromotion
    "The amount/recipient and the speaker's framing are separate coordinates. The source report does not by itself establish the government's purpose; the prior audit found the official deliverable was diagnostic-information resources."

octGlymphaticAutismClaim : AttributedClaim
octGlymphaticAutismClaim =
  attributed-claim
    "oct26-glymphatic-autism-severity"
    unidentifiedOct2026Speaker
    oct2026Transcript
    biomedicalAssociationClaim
    "The speaker links autism severity to impaired glymphatic clearance and then to dementia risk."
    associationOnly
    "Imaging associations and population dementia-risk observations remain distinct. No causal autism -> glymphatic failure -> dementia chain is imported."

octEndogenousOpioidClaim : AttributedClaim
octEndogenousOpioidClaim =
  attributed-claim
    "oct26-endogenous-opioid-autism"
    unidentifiedOct2026Speaker
    oct2026Transcript
    causalMechanismClaim
    "The speaker proposes impaired endogenous-opioid-system function as an autism mechanism and uses it to explain an advocate's distress."
    blockedPromotion
    "A mechanistic hypothesis does not license individual neurochemical diagnosis from advocacy language or observed distress."

octFMTAutismClaim : AttributedClaim
octFMTAutismClaim =
  attributed-claim
    "oct26-fmt-removes-autism-diagnosis"
    unidentifiedOct2026Speaker
    oct2026Transcript
    interventionClaim
    "The speaker treats microbiota-transfer results as evidence that autism diagnoses can disappear after FMT."
    blockedPromotion
    "The cited exploratory programme was a small uncontrolled multicomponent intervention; symptom-scale cutoff and diagnostic removal are kept non-identical."

octPronounDepressionClaim : AttributedClaim
octPronounDepressionClaim =
  attributed-claim
    "oct26-pronoun-count-depression"
    unidentifiedOct2026Speaker
    oct2026Transcript
    individualPsychologyClaim
    "The speaker counts first-person pronouns in a short quotation and treats them as a strong indicator of the quoted person's depression/defence cascade."
    blockedPromotion
    "Group-level weak language correlations do not provide an individual diagnostic classifier, especially without context-sensitive calibration."

octSynchronyFalseBeliefClaim : AttributedClaim
octSynchronyFalseBeliefClaim =
  attributed-claim
    "oct26-synchrony-endorphin-false-belief"
    unidentifiedOct2026Speaker
    oct2026Transcript
    individualPsychologyClaim
    "The speaker moves from synchronised communal behaviour and opioid-linked bonding to the claim that participants confuse pleasurable synchrony with proposition truth."
    blockedPromotion
    "Bonding/pain-threshold evidence does not identify proposition truth-value or demonstrate false-belief formation."

------------------------------------------------------------------------
-- ATTACHED 'VACCINES AND AUTISM: A MEASURED RESPONSE' TRANSCRIPT.
--
-- Hbomberguy's narration, Wakefield's reported/quoted claims, media quotations,
-- Deer investigation, and independent scientific evidence remain separated.
------------------------------------------------------------------------

hbombMMRNoLinkClaim : AttributedClaim
hbombMMRNoLinkClaim =
  attributed-claim
    "hbomb-mmr-autism-no-link"
    hbomberguy
    measuredResponseTranscript
    biomedicalAssociationClaim
    "The video states that subsequent evidence involving very large populations does not support a link between MMR vaccination and autism."
    independentlyCorroborated
    "This is Hbomberguy's claim in the transcript. Independent cohort/review evidence is represented separately by hviid2019Receipt and cochrane2020Receipt rather than attributed back to him."

hbombWakefieldRetractionClaim : AttributedClaim
hbombWakefieldRetractionClaim =
  attributed-claim
    "hbomb-wakefield-paper-retracted"
    hbomberguy
    measuredResponseTranscript
    publicHealthClaim
    "The video states that the 1998 Lancet paper was retracted."
    independentlyCorroborated
    "The transcript claim is separate from the Lancet/BMJ retraction record."

hbombParentalRecallBoundaryClaim : AttributedClaim
hbombParentalRecallBoundaryClaim =
  attributed-claim
    "hbomb-parental-temporal-attribution"
    hbomberguy
    measuredResponseTranscript
    biomedicalAssociationClaim
    "The video emphasizes that the original paper's MMR timing signal depended substantially on parental attribution of symptom onset after vaccination."
    supportedBounded
    "Temporal attribution is preserved as reported observation. Temporal succession does not create a causal MMR -> autism edge."

wakefieldGutOpioidMechanismClaim : AttributedClaim
wakefieldGutOpioidMechanismClaim =
  attributed-claim
    "wakefield-gut-morphine-like-autism-mechanism"
    wakefield
    measuredResponseTranscript
    causalMechanismClaim
    "Wakefield is quoted proposing that vaccine-associated intestinal pathology could permit morphine-like dietary products from milk/wheat to reach the developing brain and cause autism."
    blockedPromotion
    "This claim remains Wakefield-attributed. The transcript does not provide a validated same-object mechanistic causal chain, and no such chain is imported by DASHI."

hbombMediaAmplificationClaim : AttributedClaim
hbombMediaAmplificationClaim =
  attributed-claim
    "hbomb-media-amplification-vaccine-fear"
    hbomberguy
    measuredResponseTranscript
    socialPropagationClaim
    "The video argues that repeated media coverage amplified MMR-autism concern and vaccine hesitancy."
    mechanismHypothesisOnly
    "The transcript supplies historical examples and a causal narrative. A population-level media-exposure -> belief -> uptake causal estimand requires its own design and is not inferred from repetition alone."

hbombAutismRepresentationClaim : AttributedClaim
hbombAutismRepresentationClaim =
  attributed-claim
    "hbomb-autism-tragedy-representation"
    hbomberguy
    measuredResponseTranscript
    mediaRepresentationClaim
    "The video criticises media selection of extreme suffering cases and portrayal of autism as a fate worse than vaccine-preventable disease, while arguing for accommodation of autistic people."
    sourceReportedOnly
    "This is a normative/media-analysis claim by Hbomberguy. It is not used as biomedical evidence for or against vaccine safety."

hbombConflictOfInterestClaim : AttributedClaim
hbombConflictOfInterestClaim =
  attributed-claim
    "hbomb-wakefield-conflict-of-interest"
    hbomberguy
    measuredResponseTranscript
    conflictOfInterestClaim
    "The video attributes financial and litigation conflicts to Wakefield and describes patents/business plans around alternative vaccines and diagnostic products."
    independentlyCorroborated
    "The transcript account is kept distinct from Deer's investigation and BMJ's later fraud analysis; conflict evidence does not itself prove the biomedical null, which is independently paid by epidemiology."

hbombFraudClaim : AttributedClaim
hbombFraudClaim =
  attributed-claim
    "hbomb-wakefield-fraud"
    hbomberguy
    measuredResponseTranscript
    publicHealthClaim
    "The video characterises the Wakefield paper as fraudulent and describes discrepancies in case histories, pathology and recruitment."
    independentlyCorroborated
    "Independent BMJ reporting is a separate source receipt; Hbomberguy is not silently made the owner of BMJ's findings."

canonicalTranscriptClaims : List AttributedClaim
canonicalTranscriptClaims =
  octGrantFramingClaim ∷
  octGlymphaticAutismClaim ∷
  octEndogenousOpioidClaim ∷
  octFMTAutismClaim ∷
  octPronounDepressionClaim ∷
  octSynchronyFalseBeliefClaim ∷
  hbombMMRNoLinkClaim ∷
  hbombWakefieldRetractionClaim ∷
  hbombParentalRecallBoundaryClaim ∷
  wakefieldGutOpioidMechanismClaim ∷
  hbombMediaAmplificationClaim ∷
  hbombAutismRepresentationClaim ∷
  hbombConflictOfInterestClaim ∷
  hbombFraudClaim ∷ []

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
  evidence-receipt
    "hviid-2019-danish-mmr-autism"
    hviidDanishCohort2019
    populationCohort
    "Nationwide Danish cohort: MMR vaccination was not associated with increased autism risk in the studied population."
    "Population observational evidence supports the no-association result; it is not a theorem that every vaccine has zero risk for every outcome."
    false

cochrane2020Receipt : EvidenceReceipt
cochrane2020Receipt =
  evidence-receipt
    "cochrane-2020-mmr-autism"
    cochraneMMRReview2020
    systematicReview
    "Review evidence found no evidence of increased autism risk after MMR/MMRV/MMR+V vaccination in the included studies."
    "The review pays the MMR/autism safety question within its included evidence; it does not license arbitrary claims about unrelated vaccines/outcomes."
    false

lancetRetractionReceipt : EvidenceReceipt
lancetRetractionReceipt =
  evidence-receipt
    "lancet-2010-retraction"
    lancetRetraction2010
    regulatoryRetractionRecord
    "The Lancet retracted the 1998 Wakefield paper in 2010."
    "Retraction status is a publication/governance fact. It is not itself the population causal estimate for MMR and autism."
    false

bmjFraudReceipt : EvidenceReceipt
bmjFraudReceipt =
  evidence-receipt
    "bmj-2011-fraud-investigation"
    bmjFraudInvestigation2011
    investigativeRecord
    "BMJ's investigation characterised the Wakefield article as fraudulent and documented case/recruitment discrepancies and conflicts."
    "Investigative evidence pays misconduct/fraud claims; epidemiologic no-association remains independently sourced."
    false

fmtExploratoryReceipt : EvidenceReceipt
fmtExploratoryReceipt =
  evidence-receipt
    "fmt-autism-exploratory-multicomponent"
    microbiomeTransferOpenLabelStudy
    uncontrolledMulticomponentIntervention
    "Small open-label microbiota-transfer programme reported durable symptom-scale changes in the followed cohort."
    "No randomised control, multicomponent treatment package, and symptom-scale threshold is not identical to removal of an autism diagnosis."
    false

pronounCorrelationReceipt : EvidenceReceipt
pronounCorrelationReceipt =
  evidence-receipt
    "first-person-pronoun-negative-emotionality"
    pronounDepressionMetaEvidence
    languageCorrelation
    "First-person singular language has a small group-level association with depressive symptoms/negative emotionality in pooled evidence."
    "A weak aggregate correlation is not an individual diagnostic classifier and is context-dependent."
    false

synchronyBondingReceipt : EvidenceReceipt
synchronyBondingReceipt =
  evidence-receipt
    "social-synchrony-bonding-pain-threshold"
    synchronyBondingEvidence
    socialSynchronyExperiment
    "Synchronised group activity can increase bonding and pain-threshold measures used as indirect opioid-system proxies in experimental settings."
    "This does not measure proposition truth, belief accuracy, or demonstrate that synchrony causes false beliefs."
    false

canonicalEvidenceReceipts : List EvidenceReceipt
canonicalEvidenceReceipts =
  hviid2019Receipt ∷ cochrane2020Receipt ∷ lancetRetractionReceipt ∷
  bmjFraudReceipt ∷ fmtExploratoryReceipt ∷ pronounCorrelationReceipt ∷
  synchronyBondingReceipt ∷ []

------------------------------------------------------------------------
-- SAME-OBJECT / SAME-SCOPE BINDING.
--
-- A promotion receipt must explicitly bind the claim object, evidence object,
-- target object and causal-identification surface.  This prevents an unrelated
-- validation receipt from paying a different association merely because the
-- evidence families have compatible types.
------------------------------------------------------------------------

record BoundPromotionReceipt
    (claim : AttributedClaim)
    (evidence : EvidenceReceipt) : Set where
  constructor bound-promotion-receipt
  field
    claimObjectReference : String
    evidenceObjectReference : String
    targetObjectReference : String
    sameObjectBindingReference : String
    sameObjectBound : Bool
    sameObjectBoundIsTrue : sameObjectBound ≡ true
    causalIdentificationReference : String
    causalIdentificationBound : Bool
    causalIdentificationBoundIsTrue : causalIdentificationBound ≡ true

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
  paidBounded : EdgeStatus
  candidateOnly : EdgeStatus
  domainBridgeRequired : EdgeStatus
  blockedPromotion : EdgeStatus

record EdgeAudit : Set where
  constructor edge-audit
  field
    edge : PromotionEdge
    edgeStatus : EdgeStatus
    edgeReason : String

open EdgeAudit public

vaccineToAutismEdge : EdgeAudit
vaccineToAutismEdge =
  edge-audit temporalSequenceToVaccineCausation blockedPromotion
    "Parental temporal attribution and post-vaccination timing do not identify a causal MMR -> autism effect; large population evidence independently fails to support the proposed association."

caseSeriesPopulationEdge : EdgeAudit
caseSeriesPopulationEdge =
  edge-audit caseSeriesToPopulationCausalEffect blockedPromotion
    "A 12-child uncontrolled case series cannot identify a population causal effect."

fmtToDiagnosisRemovalEdge : EdgeAudit
fmtToDiagnosisRemovalEdge =
  edge-audit symptomCutoffToDiagnosisRemoval blockedPromotion
    "Crossing a symptom-scale cutoff after an uncontrolled multicomponent intervention is not definitionally equivalent to removing an autism diagnosis."

fmtSpecificEffectEdge : EdgeAudit
fmtSpecificEffectEdge =
  edge-audit fmtPackageToFMTSpecificEffect blockedPromotion
    "A multicomponent intervention cannot attribute the observed change specifically to FMT without component-identifying design evidence."

pronounIndividualEdge : EdgeAudit
pronounIndividualEdge =
  edge-audit pronounCorrelationToIndividualDepression blockedPromotion
    "Weak group-level language correlation does not identify an individual's depression state."

synchronyToFalseBeliefEdge : EdgeAudit
synchronyToFalseBeliefEdge =
  edge-audit synchronyToFalseBelief blockedPromotion
    "Bonding/opioid-proxy effects do not identify proposition truth or false-belief formation."

conflictBiomedicalEdge : EdgeAudit
conflictBiomedicalEdge =
  edge-audit conflictOfInterestToBiomedicalNull blockedPromotion
    "Conflict/misconduct evidence can undermine a source but does not by itself prove the biomedical null; population evidence pays that separately."

mediaTruthEdge : EdgeAudit
mediaTruthEdge =
  edge-audit mediaRepetitionToBiomedicalTruth blockedPromotion
    "Media repetition may affect salience or belief but cannot determine whether the biomedical proposition is true."

autismRepresentationSafetyEdge : EdgeAudit
autismRepresentationSafetyEdge =
  edge-audit autismRepresentationToVaccineSafety blockedPromotion
    "A critique of ableist/autism-tragedy framing is normatively and socially relevant but is not vaccine-safety evidence."

boundedPopulationNoAssociationEdge : EdgeAudit
boundedPopulationNoAssociationEdge =
  edge-audit populationEvidenceToBoundedNoAssociation paidBounded
    "Large cohort and systematic-review evidence pay a bounded MMR/autism no-association conclusion within their studied populations and designs."

canonicalEdgeAudit : List EdgeAudit
canonicalEdgeAudit =
  vaccineToAutismEdge ∷ caseSeriesPopulationEdge ∷ fmtToDiagnosisRemovalEdge ∷
  fmtSpecificEffectEdge ∷ pronounIndividualEdge ∷ synchronyToFalseBeliefEdge ∷
  conflictBiomedicalEdge ∷ mediaTruthEdge ∷ autismRepresentationSafetyEdge ∷
  boundedPopulationNoAssociationEdge ∷ []

------------------------------------------------------------------------
-- STRUCTURAL NO-GO PERMISSIONS.
------------------------------------------------------------------------

data TemporalSequenceCreatesVaccineCausationPermission : Set where
data SymptomCutoffCreatesDiagnosisRemovalPermission : Set where
data PronounCountCreatesIndividualDiagnosisPermission : Set where
data SynchronyCreatesFalseBeliefPermission : Set where
data ConflictCreatesBiomedicalNullPermission : Set where
data MediaRepetitionCreatesBiomedicalTruthPermission : Set where
data RepresentationCritiqueCreatesVaccineSafetyPermission : Set where

temporalSequenceDoesNotCreateVaccineCausation :
  TemporalSequenceCreatesVaccineCausationPermission → ⊥
temporalSequenceDoesNotCreateVaccineCausation ()

symptomCutoffDoesNotCreateDiagnosisRemoval :
  SymptomCutoffCreatesDiagnosisRemovalPermission → ⊥
symptomCutoffDoesNotCreateDiagnosisRemoval ()

pronounCountDoesNotCreateIndividualDiagnosis :
  PronounCountCreatesIndividualDiagnosisPermission → ⊥
pronounCountDoesNotCreateIndividualDiagnosis ()

synchronyDoesNotCreateFalseBelief :
  SynchronyCreatesFalseBeliefPermission → ⊥
synchronyDoesNotCreateFalseBelief ()

conflictDoesNotCreateBiomedicalNull :
  ConflictCreatesBiomedicalNullPermission → ⊥
conflictDoesNotCreateBiomedicalNull ()

mediaRepetitionDoesNotCreateBiomedicalTruth :
  MediaRepetitionCreatesBiomedicalTruthPermission → ⊥
mediaRepetitionDoesNotCreateBiomedicalTruth ()

representationCritiqueDoesNotCreateVaccineSafety :
  RepresentationCritiqueCreatesVaccineSafetyPermission → ⊥
representationCritiqueDoesNotCreateVaccineSafety ()

------------------------------------------------------------------------
-- STUDY-SURFACE OBJECTS: the two strongest same-object lessons.
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
canonicalWakefieldCaseSeriesSurface =
  wakefield-case-series-surface 12 false true false true true

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
canonicalFMTAutismStudySurface =
  fmt-autism-study-surface true false true true false false

------------------------------------------------------------------------
-- INFORMATION-PROPAGATION / REPRESENTATION CROSS-POLLINATION.
------------------------------------------------------------------------

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

open InformationPropagationBoundary public

canonicalInformationPropagationBoundary : InformationPropagationBoundary
canonicalInformationPropagationBoundary =
  information-propagation-boundary true true true false false false false

record CrossPollinationMap : Set where
  constructor cross-pollination-map
  field
    attributionOwner : String
    genericImplicationConeOwner : String
    causalIdentificationOwner : String
    causalEstimandOwner : String
    observerPluralityOwner : String
    traumaMemoryDecisionOwner : String
    informationPropagationOwner : String
    biologyPromotionOwner : String
    reading : String

canonicalCrossPollinationMap : CrossPollinationMap
canonicalCrossPollinationMap =
  cross-pollination-map
    "DASHI.Core.AttributedSourceCore"
    "DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact"
    "DASHI.Biology.CausalIdentificationFamiliesExact"
    "DASHI.Biology.CausalEffectEstimandExact"
    "DASHI.Biology.AliceBrownThreadInquirySynthesisExact / multi-observer machinery"
    "existing trauma-memory-learning-decision machinery: temporal observation, salience and recall remain distinct from causal identification"
    "existing cognitive-warfare/FIMI and source-provenance machinery: propagation, coordination and belief effects do not determine proposition truth"
    "DASHI.Biology.GABAPhenotypeEvidenceExact / GABAPhenotypeBridgeExact"
    "The vaccine/autism and October-2026 transcript audits reuse attribution, implication, causal-ID, observer and propagation owners. New domain objects are only study/claim receipts and same-object promotion boundaries."

------------------------------------------------------------------------
-- TERMINAL AUDIT BOUNDARY.
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
    mmrAutismNoAssociationBoundedEvidenceRepresentedIsTrue :
      mmrAutismNoAssociationBoundedEvidenceRepresented ≡ true
    sameObjectBindingRequiredForPromotion : Bool
    sameObjectBindingRequiredForPromotionIsTrue : sameObjectBindingRequiredForPromotion ≡ true

open AutismVaccineAuditBoundary public

canonicalAuditBoundary : AutismVaccineAuditBoundary
canonicalAuditBoundary =
  autism-vaccine-audit-boundary
    true refl
    false refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
