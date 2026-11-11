module DASHI.Governance.CrenshawLegalAttributionCapstoneExact where

-- Explicit attribution ladder:
-- judicial opinion -> Crenshaw's academic interpretation -> DASHI model
-- -> DASHI mathematical construction -> external legal adjudication.
-- Crenshaw's featured 1989 cases are DeGraffenreid, Moore, Payne.\n-- Jefferies is Crenshaw-cited (1989 p.143 n.13), selected by DASHI\n-- for a detailed positive comparison, but not a featured case study.\n-- These stages are distinct. None is automatically promoted by a citation.
open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Law.LegalAuthorityCitationExact as Legal
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.CrenshawLegalPrimaryCaseAtlasExact as Cases
import DASHI.Governance.CrenshawLegalCaseComparisonExact as Comparison
import DASHI.Governance.CrenshawLegalRepresentationRemedyExact as Rep
import DASHI.Governance.Crenshaw1989PassageWeldExact as CrenshawSource
import DASHI.Governance.CrenshawJudicialDisagreementExact as Disagreement
import DASHI.Governance.CrenshawSituatedStandpointExact as Standpoint
import DASHI.Governance.CrenshawRightsReformDualEffectExact as Rights
import DASHI.Governance.CrenshawHistoricalCarceralSourceAtlasExact as HistSources
import DASHI.Governance.CrenshawCrossInstitutionalEvidenceExact as CrossInstitution
import DASHI.Governance.CrenshawCarceralMissingnessExact as Missingness
import DASHI.Governance.Crenshaw1988SituatedVoiceExact as Voice
import DASHI.Governance.BlackGirlsMatterStudyScopeExact as BGM
import DASHI.Governance.BlackGirlsMatterPublishedDisciplineArithmeticExact as BGMCounts
import DASHI.Governance.BlackGirlsMatterExpulsionDenominatorExact as BGMExpulsion
import DASHI.Governance.BlackGirlsMatterCRDCOriginalRowAdmissionExact as CRDC
import DASHI.Governance.BlackGirlsMatterCRDCAggregationBoundaryExact as CRDCAgg
import DASHI.Governance.BlackGirlsMatterDenominatorSensitivityExact as Sensitivity
import DASHI.Governance.BlackGirlsMatterSourceBoundRateOrderExact as RateOrder
import DASHI.Governance.SituatedCortisolAggregateNonIdentificationExact as CortisolAggregate
import DASHI.Governance.SituatedCortisolTrajectoryAdmissionExact as CortisolPerson
import DASHI.Governance.SituatedCortisolScaleIndexedAssayExact as AssayScale
import DASHI.Governance.SituatedHPARegimeFlexibilityExact as HPARegime
import DASHI.Governance.SituatedCortisolPNFAdmissibilityExact as PNF
import DASHI.Governance.SituatedBiomarkerPNFSourceWeldExact as BiomarkerWeld
import DASHI.Governance.SituatedBiomarkerObserverAgencyExact as Agency
import DASHI.Governance.SituatedCortisolAssayGluingExact as AssayGluing
import DASHI.Governance.SituatedCortisolReceptorDissipativeExact as Receptor
import DASHI.Governance.SituatedDevelopmentalUltrametricExact as Development
import DASHI.Governance.CognitiveWarfareSituatedPhysiologyWeldExact as CW
import DASHI.Governance.CrossDomainResidualConsumerPreservationExact as Residual
import DASHI.Governance.DevelopmentalTriadicFiniteQuotientWeldExact as DevTri
import DASHI.Governance.EpistemicHistoryResidualPayloadExact as WorkPayload

data AttributionStage : Set where
  judicialText scholarlyAnalysis finiteDASHIReconstruction
  formalDASHITheorem externallyAdjudicated : AttributionStage

courtTextIsNotCrenshawTheorem :
  judicialText ≡ formalDASHITheorem → ⊥
courtTextIsNotCrenshawTheorem ()

scholarlyAnalysisIsNotAdjudication :
  scholarlyAnalysis ≡ externallyAdjudicated → ⊥
scholarlyAnalysisIsNotAdjudication ()

record LegalCrossCaseCut : Set₁ where
  constructor legal-cross-case-cut
  field
    stageSeparation :
      Cases.districtCourt ≡ Cases.appellateCourt → ⊥
    recognisedClaimStillNeedsMerits :
      INF.FactorsThrough Comparison.observedRecognition
        Comparison.liability → ⊥
    classMembershipNotRepresentation :
      INF.FactorsThrough Rep.groupMember
        Rep.adequateRepresentation → ⊥
    classScopeNotRelief :
      INF.FactorsThrough Rep.classScope Rep.relief → ⊥
    combinationRecognitionPositiveControl :
      Comparison.boundedTreatment Comparison.jefferiesAppellateReading
        ≡ Comparison.recognisesCombinedCategory
    separateMoorePayneDispositions :
      Rep.reportedDisposition Rep.moore
        ≡ Rep.reportedDisposition Rep.payne → ⊥
    jefferiesCitedAsCounterexample :
      CrenshawSource.crenshaw1989Role CrenshawSource.jefferies
      ≡ CrenshawSource.citedContraryExample
    payneMajorityDisagreementNotCollapsed :
      INF.FactorsThrough
        Disagreement.caseOnly Disagreement.position → ⊥
    scholarRoleNotClientCounsel :
      Standpoint.authorityOfRole Standpoint.scholarRole
      ≡ Standpoint.authorityOfRole Standpoint.counselRole → ⊥
    rosterDoesNotPayVoice :
      INF.FactorsThrough
        Standpoint.reportedPeople Standpoint.effectiveVoice → ⊥
    formalRightsDoNotDetermineMaterialTransfer :
      INF.FactorsThrough
        Rights.formalRecognition Rights.materialReallocation → ⊥
    institutionalSchoolReceiptCannotPayCustody :
      CrossInstitution.Supports CrossInstitution.schoolRecord
        CrossInstitution.custodialOutcome → ⊥
    citedCarceralAtlasDoesNotCreateAuthority :
      Attr.atlasCreatesAuthority HistSources.historicalInstitutionalSourceAtlas
        ≡ false
    unrecordedDoesNotImplyNoPolicingHarm :
      INF.FactorsThrough
        Missingness.entryInSelectedCorpus Missingness.independentHarm → ⊥
    authorialSituatedVoiceNotRecoveredFromPublicationLabel :
      INF.FactorsThrough
        Voice.publicationLabel Voice.voice → ⊥
    administrativeDataCannotBeSubstitutedForFocusGroupTestimony :
      BGM.Supports BGM.districtAdministrativeData
        BGM.participantReportedSchoolExperience → ⊥
    missingDisabilityAnalysisCannotProveNoHarm :
      INF.FactorsThrough
        BGM.availableDisabilityResult BGM.actualDisabilityHarm → ⊥
    bostonDisciplineCountSourceArithmetic :
      BGMCounts.disciplineCases BGMCounts.boston BGMCounts.blackGirls ≡
        11 * BGMCounts.disciplineCases BGMCounts.boston BGMCounts.whiteGirls + 10
    newYorkDisciplineCountSourceArithmetic :
      BGMCounts.disciplineCases BGMCounts.newYorkCity BGMCounts.blackGirls ≡
        10 * BGMCounts.disciplineCases BGMCounts.newYorkCity BGMCounts.whiteGirls + 236
    crossYearEnrollmentTableNotEquivalent :
      BGMCounts.tableOnePeriod ≡ BGMCounts.disciplineFigurePeriod → ⊥
    zeroObservedExpulsionDenominatorBlocksRatio :
      BGMExpulsion.ObservedRatioAdmission BGMExpulsion.newYorkCity → ⊥
    rawSuppressionIsNotActualZero :
      CRDC.suppressed ≡ CRDC.observed 0 → ⊥
    originalOneSuspensionNotRepeated :
      CRDC.oneOutOfSchoolSuspension ≡
        CRDC.multipleOutOfSchoolSuspensions → ⊥
    crossIndicatorEventsAreNotUniqueStudents :
      CRDC.disciplinaryEvents ≡ CRDC.uniqueStudents → ⊥
    publishedCasesCannotDetermineRateDirection :
      INF.FactorsThrough Sensitivity.observedCountPair
        Sensitivity.syntheticDirection → ⊥
    conditionalSameYearPopulationRateReceipt :
      ∀ {src : CRDC.VerifiedCRDCSource}
        {d : CRDC.District}
        {e : CRDC.DisabilityScope}
        {m : CRDC.Measure} →
      RateOrder.CertifiedBlackHigher src d e m →
      CRDC.ComparableRatePair src d e m
    aggregateEnvironmentalAndCortisolTotalsCannotIdentifyPerson :
      INF.FactorsThrough
        CortisolAggregate.coarseEnvironmentAndAggregateTotal
        (CortisolAggregate.individualResponse CortisolAggregate.participantA) → ⊥
    aggregateLoadCannotIdentifySituatedAppraisal :
      INF.FactorsThrough
        CortisolPerson.aggregateLoad CortisolPerson.candidateAppraisal → ⊥
    cortisolModelAdmissionRequiresIndividualFit :
      ∀ {Person Time LatentState : Set}
        {model : CortisolPerson.CalibratedPersonalDynamics Person Time LatentState}
        {t : Time} →
      CortisolPerson.PersonSpecificAdmission model t →
      CortisolPerson.withinPersonCalibrationEvidence model
    integratedHairScaleCannotRecoverAcutePoint :
      INF.FactorsThrough
        AssayScale.twoPointIntegral AssayScale.acutePoint → ⊥
    sameExposureCannotIdentifyHPARegime :
      INF.FactorsThrough
        HPARegime.sameNominalExposure HPARegime.regime → ⊥
    preciselyKnownBiomarkerCannotAttributeDefendant :
      INF.FactorsThrough
        PNF.measurementValue PNF.causalAttribution → ⊥
    causalGovernanceRequiresCounterfactual :
      ∀ {Person Case : Set}
        {audit : PNF.ExternalGovernanceAudit Person Case}
        {person : Person} {legalCase : Case} →
      PNF.SourcePaidCausalFinding audit person legalCase →
      PNF.validatedCounterfactualComparison audit person legalCase
    legalGovernanceRequiresAdjudication :
      ∀ {Person Case : Set}
        {audit : PNF.ExternalGovernanceAudit Person Case}
        {person : Person} {legalCase : Case} →
      PNF.SeparatelyAdjudicatedLegalClaim audit person legalCase →
      PNF.legallyAuthorisedDetermination audit legalCase
    finiteDevelopmentalTreeStrongTriangle :
      (x y z : Development.DevelopmentalLeaf) →
      Development.treeDistance x z ≤
      (Development.treeDistance x y ⊔ Development.treeDistance y z)
    receptorClearanceIsNotInvertible :
      (undo : Receptor.HormoneReceptor → Receptor.HormoneReceptor) →
      ((s : Receptor.HormoneReceptor) →
        undo (Receptor.step Receptor.clearance s) ≡ s) → ⊥
    incompatibleToyAssaysDoNotGlue :
      AssayGluing.JointAssayExplanation 2 0 → ⊥
    optionalBiomarkerRefusalBlocksOptionalUse :
      Agency.OptionalBiomarkerPermission Agency.refuses → ⊥
    PNFNumericABIStillCannotPromote :
      BiomarkerWeld.NumericABI.PNFSpectralNumericABIPromotion → ⊥
    cognitiveWarfareContentConeNotProvenance :
      INF.FactorsThrough
        CW.Warfare.contentConeObserver CW.Warfare.provenance → ⊥
    cognitiveWarfareTasksNotIntent :
      INF.NonFactorabilityWitness
        CW.Work.observedTasks CW.Work.statedPurpose
    cognitiveWarfareBiomarkerNotCause :
      INF.FactorsThrough
        CW.Causal.measurementValue CW.Causal.causalAttribution → ⊥
    crossDomainIntegratedAssayNotAcuteRecovery :
      INF.FactorsThrough
        AssayGluing.integratedReadout AssayGluing.earlyReadout → ⊥
    developmentalCanonicalPrefixCannotRecoverLaterHistory :
      DevTri.encodeHistory Development.leafA
        ≡ DevTri.encodeHistory Development.leafB → ⊥
    epistemicWorkFullHistoryPayloadRoundTrip :
      (history : List CW.Work.EpistemicTask) →
      WorkPayload.decodeWork (WorkPayload.encodeWork history) ≡ history
    epistemicWorkPublicStatusCannotDecodeHistory :
      (decoder : CW.Work.PublicDisposition → List CW.Work.EpistemicTask) →
      ((history : List CW.Work.EpistemicTask) →
        decoder (CW.Work.visibleDisposition history) ≡ history) → ⊥
    citationDoesNotClaimBinding :
      Legal.bindingForceClaimed Cases.jefferiesAppeal ≡ false
    crenshawBibliographyNoProofPromotion :
      Attr.citationImportsProof Cases.crenshawDemarginalizing ≡ false

crenshawLegalCrossCaseCut : LegalCrossCaseCut
crenshawLegalCrossCaseCut =
  legal-cross-case-cut
    Cases.districtNotAppellate
    Comparison.recognitionDoesNotEstablishMerits
    Rep.classMembershipCannotDecideRepresentativeAdequacy
    Rep.classScopeCannotDetermineRemedy
    Comparison.jefferiesIntersectionalRecognitionPositiveControl
    Rep.mooreAndPayneHaveDistinctAppellateDispositions
    CrenshawSource.jefferiesIsCitedByCrenshaw
    Disagreement.caseCitationCannotSelectJudicialPosition
    Standpoint.scholarlyInterpretationIsNotClientRepresentation
    Standpoint.courtRosterNotSufficientToInferAuthority
    Rights.formalRightDoesNotGuaranteeMaterialTransformation
    CrossInstitution.schoolDisciplineDoesNotByItselfPayCustodialOutcome
    HistSources.historicalCitationDoesNotCreateAuthority
    Missingness.recordAbsenceDoesNotProveAbsenceOfHarm
    Voice.bibliographicLabelCannotRecoverSituatedVoice
    BGM.districtDataDoesNotPayParticipantTestimony
    BGM.reportScopeCannotDecideUnstudiedHarm
    BGMCounts.bostonGirlsCasesElevenfoldPlusTen
    BGMCounts.newYorkGirlsCasesTenfoldPlus236
    BGMCounts.tableOneIsNotDisciplineFigurePeriod
    BGMExpulsion.newYorkObservedExpulsionRatioBlocked
    CRDC.suppressedNotZero
    CRDC.oneAndRepeatedSuspensionAreDifferent
    CRDCAgg.differentUnitsAreNotDefinitionalEqual
    Sensitivity.caseCountsAloneDoNotDetermineRateOrder
    RateOrder.certifiedHigherRequiresSamePopulationRows
    CortisolAggregate.aggregateEnvironmentalExposureCannotDeterminePerson
    CortisolPerson.aggregateLoadDoesNotFixAppraisal
    CortisolPerson.admissionRequiresIndividualCalibration
    AssayScale.longWindowCannotIdentifyAcuteSurge
    HPARegime.exposureCannotDetermineHPARegime
    PNF.pointIdentifiedBiomarkerDoesNotIdentifyCause
    PNF.causalFindingRequiresCounterfactual
    PNF.legalFindingRequiresLegalAuthority
    Development.treeDistanceStrongTriangle
    Receptor.clearanceHasNoGlobalLeftInverse
    AssayGluing.noCommonHistoryForContradictoryReadings
    Agency.refusalBlocksOptionalBiomarkerUse
    BiomarkerWeld.noNumericAbiTruthPromotion
    CW.sameContentAndConeCannotDetermineProvenance
    CW.sameEpistemicTasksCannotIdentifyStrategicPurpose
    CW.cortisolDoesNotDetermineCausalAttribution
    Residual.integralDoesNotDetermineAcutePoint
    DevTri.laterHistoryReallyLost
    WorkPayload.workRoundTrip
    WorkPayload.noLosslessDecoderAfterDroppingSideInformation
    refl refl
