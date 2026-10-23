module DASHI.Cognition.PsychotronicsSuccorAttributionRegression where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Cognition.PsychotronicsSuccorSourceAtlasExact as Atlas
import DASHI.Cognition.PsychotronicsScreenshotDiscriminationExact as Frames
import DASHI.Culture.HoeMathLevelsSourceBoundaryExact as HoeMath
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.AnomalousConsciousnessResearchEvidenceContinuumExact as Evidence
import DASHI.Physics.QuantumVacuum.DiscriminatingExperiment as Experiment

------------------------------------------------------------------------
-- Definitional regressions for a historical source atlas, NOT an empirical
-- test and NOT a substitute for an Agda kernel check at the branch head.
------------------------------------------------------------------------

croftCoUseIsOnlyAnAttributedReport :
  Atlas.relationClass Atlas.croftCloudbusterRelation ≡
  Atlas.reportedCoUseByActor
croftCoUseIsOnlyAnAttributedReport = refl

lakhovskyIsOnlyAnalogy :
  Atlas.relationClass Atlas.lakhovskyCopperRelation ≡
  Atlas.hardwareAnalogyOnly
lakhovskyIsOnlyAnalogy = refl

gatewayMatrixIsOnlyTextualAnalogy :
  Atlas.relationClass Atlas.gatewayTimelineRelation ≡
  Atlas.thematicResemblanceOnly
gatewayMatrixIsOnlyTextualAnalogy = refl

mayAndJulyAreSameAuthorialRoot :
  Atlas.root Atlas.croftReportedEntities ≡
  Atlas.root Atlas.croftCircuitDescription
mayAndJulyAreSameAuthorialRoot = refl

julyAndAnthologyAreSameAuthorialRoot :
  Atlas.root Atlas.croftCircuitDescription ≡
  Atlas.root Atlas.croftCoLocatedDevice
julyAndAnthologyAreSameAuthorialRoot = refl

patentCannotImportProof :
  Attribution.citationImportsProof Atlas.lakhovskyPatent ≡ false
patentCannotImportProof =
  Atlas.allSourcesRemainNonPromoting Atlas.lakhovskyPatent

armyReportCannotCreateAuthority :
  Attribution.citationCreatesAuthority Atlas.gateway1983 ≡ false
armyReportCannotCreateAuthority =
  Atlas.allSourcesRemainNonAuthoritative Atlas.gateway1983

museumArticleCannotCreateAuthority :
  Attribution.citationCreatesAuthority Atlas.reichMuseum ≡ false
museumArticleCannotCreateAuthority =
  Atlas.allSourcesRemainNonAuthoritative Atlas.reichMuseum

croftLinkDoesNotCreateNewPhysics :
  Atlas.newPhysicsEstablished Atlas.croftCloudbusterRelation ≡ false
croftLinkDoesNotCreateNewPhysics = refl

gatewaySimilarityDoesNotProveTransmission :
  Atlas.historicalTransmissionProved Atlas.gatewayTimelineRelation ≡ false
gatewaySimilarityDoesNotProveTransmission = refl

archiveIsNotAnIndependentCroftReplication :
  Atlas.root Atlas.croftCoLocatedDevice ≡ Atlas.croftAuthorRoot
archiveIsNotAnIndependentCroftReplication = refl

-- The Ed Dames reference is documented by Croft but transmits neither
-- institutional authority nor any military-device design.
croftDamesIsOnlyNamedReference :
  Atlas.relationClass Atlas.croftRemoteViewingPersonMention ≡
  Atlas.namedPersonMentionOnly
croftDamesIsOnlyNamedReference = refl

croftDamesMentionSharesMaySourceRoot :
  Atlas.root Atlas.croftMentionsEdDames ≡
  Atlas.root Atlas.croftReportedEntities
croftDamesMentionSharesMaySourceRoot = refl

associationChronologyCannotPromoteMechanism :
  Attribution.citationCreatesAuthority Atlas.irvaTimeline ≡ false
associationChronologyCannotPromoteMechanism =
  Atlas.allSourcesRemainNonAuthoritative Atlas.irvaTimeline

------------------------------------------------------------------------
-- Max-cut 2: sourced explicit influences and same-object image guardrails.
------------------------------------------------------------------------

croftNamedReadingNotMerelyAnalogy :
  Atlas.relationClass Atlas.croftNamedBookRelation ≡
  Atlas.explicitlyAttributedReading
croftNamedReadingNotMerelyAnalogy = refl

croftStarIsNotInstagramIdentity :
  Atlas.relationClass Atlas.croftStarSymbolRelation ≡
  Atlas.namedSymbolOnly
croftStarIsNotInstagramIdentity = refl

croftNamedExemplarsNotTechnologyTransfer :
  Atlas.relationClass Atlas.croftNamedHistoricalExemplars ≡
  Atlas.namedExemplarsOnly
croftNamedExemplarsNotTechnologyTransfer = refl

croftBookClaimRemainsSameAuthorialRoot :
  Atlas.root Atlas.croftNamesKing ≡ Atlas.croftAuthorRoot
croftBookClaimRemainsSameAuthorialRoot = refl

screenshotCountIsTen :
  Frames.countStills Frames.stillAtlas ≡ 10
screenshotCountIsTen = Frames.stillAtlasHasTenFrames

separateCreatorForCopperCage :
  Frames.creator Frames.copperWide ≡ Frames.crystalPyramids96
separateCreatorForCopperCage = refl

separateCreatorForArc :
  Frames.creator Frames.curvedArcComment ≡
  Frames.colourTheoryInstallations
separateCreatorForArc = refl

stillDoesNotVerifyTemporalMotion :
  Frames.temporalMotionVerified Frames.curvedArcComment ≡ false
stillDoesNotVerifyTemporalMotion = refl

thermalScreenDoesNotVerifyCalibration :
  Frames.instrumentCalibrationVerified Frames.thermalScreen ≡ false
thermalScreenDoesNotVerifyCalibration = refl

-- The atlas deliberately has eleven source instances. The five named-source
-- / original-author Croft passages still share a single authorial root.
sourceAtlasCountIsThirtyEight :
  Attribution.sourceCount (Attribution.sources Atlas.sourceAtlas) ≡ 38
sourceAtlasCountIsThirtyEight = refl

------------------------------------------------------------------------
-- Max-cut 3: product-author identity and eight additional screenshot hashes
------------------------------------------------------------------------

secondImageBatchIsEight :
  Frames.countStills Frames.secondBatch ≡ 8
secondImageBatchIsEight = Frames.secondBatchHasEight

allScreenshotCountIsEighteen :
  Frames.countStills Frames.stillAtlas +
  Frames.countStills Frames.secondBatch ≡ 18
allScreenshotCountIsEighteen = Frames.bothBatchesHaveEighteen

aurumayaNamesCroftButNotAnEfficacyWitness :
  Atlas.relationClass Atlas.aurumayaSelfIdentifiesCroft ≡
  Atlas.contemporarySelfAttribution
aurumayaNamesCroftButNotAnEfficacyWitness = refl

iTorusSpecsAreMarketingNotFieldMapping :
  Atlas.relationClass Atlas.iTorusCommercialSpecOnly ≡
  Atlas.commercialSpecificationOnly
iTorusSpecsAreMarketingNotFieldMapping = refl

oudinPhotoIsOnlyHistoricalMechanismPrecedent :
  Atlas.relationClass Atlas.oudinHistoricalPrecedentOnly ≡
  Atlas.historicalMechanismPrecedentOnly
oudinPhotoIsOnlyHistoricalMechanismPrecedent = refl

torusPostAuthorRetained :
  Frames.creator Frames.itorusCase ≡ Frames.iPyramids
torusPostAuthorRetained = refl

oudinMakerPostAuthorRetained :
  Frames.creator Frames.oudinLoop ≡ Frames.berndNindl
oudinMakerPostAuthorRetained = refl

modernQuartzMakerAuthorRetained :
  Frames.creator Frames.aurumayaSuccor ≡ Frames.aurumaya
modernQuartzMakerAuthorRetained = refl

pignatelliLabelNotAnOriginalInventorReceipt :
  Frames.electromagneticSpectrumMeasured Frames.pignatelliCaptionedMotor ≡ false
pignatelliLabelNotAnOriginalInventorReceipt = refl

------------------------------------------------------------------------
-- Fifth-image source attribution: one maker-historical source lineage,
-- multiple apparatus examples, and screenshot ordinal ≠ circuit identity.
------------------------------------------------------------------------

fifthIsBerndTower :
  Frames.creator Frames.fifthImage ≡ Frames.berndNindl
fifthIsBerndTower = refl

fifthIsNotBerndLoop :
  Frames.scene Frames.fifthImage ≡ Frames.oudInAirDischarge
fifthIsNotBerndLoop = refl

towerOrdinalsCorrect :
  Frames.countStills Frames.displayOrder ≡ 8
towerOrdinalsCorrect = Frames.displayOrderEight

towerGeometryOnly :
  Atlas.relationClass Atlas.berndTowerGeometryAnalogy ≡
  Atlas.hardwareAnalogyOnly
towerGeometryOnly = refl

sphereAnalogyOnly :
  Atlas.relationClass Atlas.oudinSphereDisplayAnalogy ≡
  Atlas.hardwareAnalogyOnly
sphereAnalogyOnly = refl

beharyTwoExamplesOneRoot :
  Atlas.root Atlas.oudinSpacedWindingFamily ≡
  Atlas.root Atlas.oudinSphereStreamerFamily
beharyTwoExamplesOneRoot = refl

fifthImageHasNoMeasuredSpectrum :
  Frames.electromagneticSpectrumMeasured Frames.fifthImage ≡ false
fifthImageHasNoMeasuredSpectrum = refl

fifthImageNoNativeVideo :
  Frames.originalMediaURLInspected Frames.fifthImage ≡ false
fifthImageNoNativeVideo = refl

------------------------------------------------------------------------
-- Max-cut: separate historically real Oudin/electrostatic precedents from
-- SAME OBJECT identification and demonstrated power at the viral device.
------------------------------------------------------------------------

oudinOriginalIsAnalogyNotCircuitIdentification :
  Atlas.relationClass Atlas.historicTopologyComparisonOnly ≡
  Atlas.hardwareAnalogyOnly
oudinOriginalIsAnalogyNotCircuitIdentification = refl

jefimenkoReportedExperimentDoesNotIdentifyPignatelli :
  Atlas.relationClass Atlas.jefimenkoMotorClaimOnly ≡
  Atlas.historicalMechanismPrecedentOnly
jefimenkoReportedExperimentDoesNotIdentifyPignatelli = refl

historicalOudinHasSeparateSourceRoot :
  Atlas.root Atlas.oudinUnipolarHistoricalTopology ≡
  Atlas.guilleminotHistoricalManualRoot
historicalOudinHasSeparateSourceRoot = refl

jefimenkoRemainsOriginalAuthorReport :
  Atlas.ceiling Atlas.jefimenkoSmallMotorField ≡
  Atlas.attributedAuthorReport
jefimenkoRemainsOriginalAuthorReport = refl

jefimenkoCitationImportsNoExperimentForPignatelli :
  Attribution.citationImportsProof Atlas.jefimenkoElectrostaticMotors ≡ false
jefimenkoCitationImportsNoExperimentForPignatelli =
  Atlas.allSourcesRemainNonPromoting Atlas.jefimenkoElectrostaticMotors

------------------------------------------------------------------------
-- Same-family product text does not establish a common calibrated quantity.
-- Explicit Rife/Zero-point marketing is a bounded *cultural* attribution.
------------------------------------------------------------------------

itorusAppExplicitlyNamesRifeButNotMeasuredWaveform :
  Atlas.relationClass Atlas.itorusExplicitRifeBridge ≡
  Atlas.contemporarySelfAttribution
itorusAppExplicitlyNamesRifeButNotMeasuredWaveform = refl

resellerCopyDoesNotProveField :
  Atlas.relationClass Atlas.itorusRetailClaimsUncalibrated ≡
  Atlas.commercialSpecificationOnly
resellerCopyDoesNotProveField = refl

aurumayaCatalogueIsNotIndependentFromItsProducts :
  Atlas.root Atlas.aurumayaSharedVocabulary ≡
  Atlas.root Atlas.aurumayaCroftClaim
aurumayaCatalogueIsNotIndependentFromItsProducts = refl

jefimenko1971And1973SameAuthor :
  Atlas.root Atlas.jefimenko1971Bibliography ≡
  Atlas.root Atlas.jefimenkoSmallMotorField
jefimenko1971And1973SameAuthor = refl

jefimenko1971DOIDoesNotProveViralMotor :
  Attribution.citationImportsProof Atlas.jefimenko1971 ≡ false
jefimenko1971DOIDoesNotProveViralMotor =
  Atlas.allSourcesRemainNonPromoting Atlas.jefimenko1971

differentSourceRolesPreservedForImpedanceClaim :
  Atlas.root Atlas.itorusImpedanceVariants ≡ Atlas.itorusRetailCopyRoot
differentSourceRolesPreservedForImpedanceClaim = refl

appPublisherDoesNotCreateAuthority :
  Attribution.citationCreatesAuthority Atlas.itorusAppPublisher ≡ false
appPublisherDoesNotCreateAuthority =
  Atlas.allSourcesRemainNonAuthoritative Atlas.itorusAppPublisher

-- Same-maker shop and homepage are different documents, not independent
-- experimental corroboration; exact webpage 333MHz/369 locators retained.
aurumayaShopAndHomeShareMakerRoot :
  Atlas.root Atlas.aurumayaShop333Catalogue ≡
  Atlas.root Atlas.aurumayaSharedVocabulary
aurumayaShopAndHomeShareMakerRoot = refl

shop333IsOnlyContemporarySelfAttribution :
  Atlas.relationClass Atlas.aurumayaShopCoMarketing ≡
  Atlas.contemporarySelfAttribution
shop333IsOnlyContemporarySelfAttribution = refl

------------------------------------------------------------------------
-- Source-backed visual matching. Strong catalogue convergence is NOT
-- same-physical-SKU, native reel, a functioning medical modality or an
-- independently measured coil transfer function.
------------------------------------------------------------------------

copperStarNowHasBoundedSellerCandidate :
  Atlas.relationClass Atlas.candidateCopperStarIdentification ≡
  Atlas.multiFeatureCatalogueMatchUnconfirmed
copperStarNowHasBoundedSellerCandidate = refl

rodinTermPresentInMirroredCaption :
  Atlas.relationClass Atlas.rodinNamedBySocialRelay ≡
  Atlas.namedSymbolOnly
rodinTermPresentInMirroredCaption = refl

zeroPointTwoProductsShareOneCommercialRoot :
  Atlas.root Atlas.zeroPointMiniMagnetResponse ≡
  Atlas.root Atlas.zeroPointStarshipSphereClaim
zeroPointTwoProductsShareOneCommercialRoot = refl

retailerCatalogIsNotInstagramOwnerProof :
  Atlas.historicalTransmissionProved Atlas.candidateCopperStarIdentification ≡ false
retailerCatalogIsNotInstagramOwnerProof = refl

indexedSellerCannotCreateExperimentalAuthority :
  Attribution.citationCreatesAuthority Atlas.zeroPointStarshipProductIndexed ≡ false
indexedSellerCannotCreateExperimentalAuthority =
  Atlas.allSourcesRemainNonAuthoritative Atlas.zeroPointStarshipProductIndexed

rodinMirrorCannotBecomeSameCreatorReceipt :
  Atlas.historicalTransmissionProved Atlas.rodinNamedBySocialRelay ≡ false
rodinMirrorCannotBecomeSameCreatorReceipt = refl

------------------------------------------------------------------------
-- HOE_MATH / 5D SPIRITUALITY: NO NUMBER-ID OR ONTOLOGY TRANSFER
--
-- Original hoe_math Levels source and its Spiral Dynamics/AQAL lineage
-- are owned by Culture.HoeMathLevelsSourceBoundaryExact. We only import
-- that owner: do NOT copy the model into this psychotronics atlas.
------------------------------------------------------------------------

data FiveDUsageRegister : Set where
  spiritualFiveDClaim : FiveDUsageRegister
  hoeMathStageOrLevel : FiveDUsageRegister
  temporaryExperientialState : FiveDUsageRegister
  developmentalSkillLine : FiveDUsageRegister
  fifthSpacetimeCoordinate : FiveDUsageRegister
  toroidalMaterialGeometry : FiveDUsageRegister
  measuredElectromagneticField : FiveDUsageRegister

spiritualNumberIsNotHoeMathLevel :
  spiritualFiveDClaim ≡ hoeMathStageOrLevel → ⊥
spiritualNumberIsNotHoeMathLevel ()

spiritualNumberIsNotPhysicsCoordinate :
  spiritualFiveDClaim ≡ fifthSpacetimeCoordinate → ⊥
spiritualNumberIsNotPhysicsCoordinate ()

toroidalPhysicalShapeIsNotSpiritualStage :
  toroidalMaterialGeometry ≡ spiritualFiveDClaim → ⊥
toroidalPhysicalShapeIsNotSpiritualStage ()

observedMagneticFieldIsNotMysticalState :
  measuredElectromagneticField ≡ spiritualFiveDClaim → ⊥
observedMagneticFieldIsNotMysticalState ()

developmentalLineDistinctFromMomentaryState :
  developmentalSkillLine ≡ temporaryExperientialState → ⊥
developmentalLineDistinctFromMomentaryState ()

hoeMathDistinguishesStageFromState :
  HoeMath.coordinateRelation HoeMath.stateMode ≡
  HoeMath.fluctuatingStateRelation
hoeMathDistinguishesStageFromState = refl

hoeMathPreservesIndependentLines :
  HoeMath.coordinateRelation HoeMath.developmentalLine ≡
  HoeMath.independentlyDevelopingLine
hoeMathPreservesIndependentLines = refl

hoeMathOwnsOnlyItsPresentedStageChart :
  HoeMath.ownership HoeMath.simplifiedNineLevelPresentation ≡
  HoeMath.hoeMathPresentationOwnership
hoeMathOwnsOnlyItsPresentedStageChart = refl

hoeMathDoesNotOwnAQAL :
  HoeMath.ownership HoeMath.aqalQuadrants ≡
  HoeMath.underlyingNamedTradition
hoeMathDoesNotOwnAQAL = refl

openhandTorusFiveDIsOnlyAnAttributedAuthorDefinition :
  Atlas.relationClass Atlas.openhandTorusFiveDIsSpecificBeliefSource ≡
  Atlas.thematicResemblanceOnly
openhandTorusFiveDIsOnlyAnAttributedAuthorDefinition = refl

openhandTwoPostsShareOneSourceOrigin :
  Atlas.root Atlas.openhandFiveDTorusSource ≡
  Atlas.root Atlas.openhandRealitySplitClaim
openhandTwoPostsShareOneSourceOrigin = refl

appMarketerDoesNotMakeOpenhandOrigin :
  Atlas.historicalTransmissionProved Atlas.openhandTorusFiveDIsSpecificBeliefSource ≡ false
appMarketerDoesNotMakeOpenhandOrigin = refl

openhandDocumentDoesNotImportFieldMeasurement :
  Attribution.citationImportsProof Atlas.openhand2026FiveD ≡ false
openhandDocumentDoesNotImportFieldMeasurement =
  Atlas.allSourcesRemainNonPromoting Atlas.openhand2026FiveD

------------------------------------------------------------------------
-- ACTUAL SCIENTIFIC 5D-ASC ≠ SPIRITUAL 5D / 5TH SPACETIME COORDINATE
-- "5D" in the altered-states rating scale refers to five reported
-- dimensions. NADA, MEQ30, EDI, 5D-ASC measure partially overlapping,
-- nonidentical subjective constructs in validated populations.
-- None validates an iTorus field or an "ascension" endpoint.
------------------------------------------------------------------------

data FiveDLabelReferent : Set where
  openhandSpiritualFiveD : FiveDLabelReferent
  alteredStatesFiveFactorScale : FiveDLabelReferent
  physicalFifthDimension : FiveDLabelReferent
  hoeMathFifthNumberLabel : FiveDLabelReferent

fiveFactorScaleNotSpiritualDimension :
  alteredStatesFiveFactorScale ≡ openhandSpiritualFiveD → ⊥
fiveFactorScaleNotSpiritualDimension ()

fiveFactorScaleNotPhysicalFifthCoordinate :
  alteredStatesFiveFactorScale ≡ physicalFifthDimension → ⊥
fiveFactorScaleNotPhysicalFifthCoordinate ()

fiveFactorScaleNotHoeMathFifthLevel :
  alteredStatesFiveFactorScale ≡ hoeMathFifthNumberLabel → ⊥
fiveFactorScaleNotHoeMathFifthLevel ()

psychometricSourceIsScopedToReportedExperience :
  Atlas.ceiling Atlas.psychometricFiveDNotSpiritualFiveD ≡
  Atlas.scopedValidatedSelfReport
psychometricSourceIsScopedToReportedExperience = refl

nadaStateTraitAreSpecificReportedConstructs :
  Atlas.ceiling Atlas.nondualStateTraitMeasurement ≡
  Atlas.scopedValidatedSelfReport
nadaStateTraitAreSpecificReportedConstructs = refl

revisedAscIsIndependentResearchTeam :
  Atlas.root Atlas.psychometricFiveDNotSpiritualFiveD ≡
  Atlas.root Atlas.ascModelRevision → ⊥
revisedAscIsIndependentResearchTeam ()

ascNameDoesNotValidate5DMysticism :
  Atlas.relationClass Atlas.psychometricsNotSpiritualDimension ≡
  Atlas.documentaryDistinction
ascNameDoesNotValidate5DMysticism = refl

heartmathIsNotHoeMathSource :
  Atlas.relationClass Atlas.heartmathIsNotHoeMath ≡
  Atlas.documentaryDistinction
heartmathIsNotHoeMathSource = refl

------------------------------------------------------------------------
-- SAME REPORT SURFACE DOES NOT IDENTIFY CAUSE: a transparent SYNTHETIC
-- two-world counterexample (NOT two observed human results).
--
-- These world names represent possible intervention settings with an
-- indistinguishable unity self-report; hence a coarse report cannot
-- determine whether the physical coil was powered.
------------------------------------------------------------------------

data SyntheticUnityWorld : Set where
  reportedUnityWithSoundOnly : SyntheticUnityWorld
  reportedUnityWithPoweredCoil : SyntheticUnityWorld

data CoarseUnityResponse : Set where feltUnity : CoarseUnityResponse

observedUnity : SyntheticUnityWorld → CoarseUnityResponse
observedUnity _ = feltUnity

data PhysicalDriveStatus : Set where
  coilUnpowered : PhysicalDriveStatus
  coilPowered : PhysicalDriveStatus

physicalDriver : SyntheticUnityWorld → PhysicalDriveStatus
physicalDriver reportedUnityWithSoundOnly = coilUnpowered
physicalDriver reportedUnityWithPoweredCoil = coilPowered

differentDriverAtSameSubjectiveReport :
  physicalDriver reportedUnityWithSoundOnly ≡
  physicalDriver reportedUnityWithPoweredCoil → ⊥
differentDriverAtSameSubjectiveReport ()

unityReportCannotIdentifyDeviceDrive :
  INF.FactorsThrough observedUnity physicalDriver → ⊥
unityReportCannotIdentifyDeviceDrive =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      reportedUnityWithSoundOnly
      reportedUnityWithPoweredCoil
      refl
      differentDriverAtSameSubjectiveReport)

------------------------------------------------------------------------
-- EXPERIMENT CUT: no assignment, participant, observation, questionnaire
-- score, blinding success or measured coil field is fabricated.
-- Design types specify required source-backed receipt fields.
------------------------------------------------------------------------

data ControlledArm : Set where
  poweredCoilWithMatchedSound : ControlledArm
  nonpoweredCoilWithMatchedSound : ControlledArm
  soundOnlyNoActiveCoil : ControlledArm
  quietMeditationControl : ControlledArm

data OutcomeDomain : Set where
  immediateNondualReport : OutcomeDomain
  mysticalFourFactorExperience : OutcomeDomain
  egoDissolutionReport : OutcomeDomain
  alteredStateFactorReport : OutcomeDomain
  longerTermPsychologicalFunction : OutcomeDomain
  instrumentedMagneticField : OutcomeDomain
  expectancyAndBlinding : OutcomeDomain
  autonomicBreathingPhysiology : OutcomeDomain

candidateSource : OutcomeDomain → Attribution.AttributedSource
candidateSource immediateNondualReport = Atlas.hanleyNADA2018
candidateSource mysticalFourFactorExperience = Atlas.macleanMEQ2012
candidateSource egoDissolutionReport = Atlas.nourEDI2016
candidateSource alteredStateFactorReport = Atlas.kervadecFiveDASC2026
candidateSource longerTermPsychologicalFunction = Atlas.hanleyNADA2018
candidateSource instrumentedMagneticField = Atlas.ipyramidsI9
candidateSource expectancyAndBlinding = Atlas.stockerASCRevision2026
candidateSource autonomicBreathingPhysiology = Atlas.heartmathEnergeticCommunication

-- These are candidate *source locators*, not endorsements of these papers
-- as validated metrics for every outcome. In particular NADA is not a
-- validated longitudinal clinical-function instrument and HeartMath is not
-- an independent breath/HRV calibration paper. The trial designer must
-- establish instrument validity separately.

record TorusPhenomenologyProtocolDemand : Set where
  constructor torus-phenomenology-protocol-demand
  field
    ethicalApprovalAndConsent : String
    preregisteredQuestionAndAnalysis : String
    participantEligibilityAndAdverseEventMonitoring : String
    interventionArmsAndRandomisation : String
    maskingCredibilityAndExpectation : String
    actualCoilModelAndAmpWaveform : String
    independentlyCalibratedFieldMap : String
    audioAndVibrationMatching : String
    respirationAndMovementRecording : String
    validatedStateQuestionnaireAndTimepoint : String
    separateTraitOrFunctionalEndpoint : String
    sampleSizePowerAndMultiplicityPlan : String
    independentReproductionAndRawDataPlan : String

data AlternateMechanism : Set where
  suggestionOrExpectation : AlternateMechanism
  audibleToneOrVibration : AlternateMechanism
  breathingAndHeartRateCovariation : AlternateMechanism
  practiceTimeOrRelaxation : AlternateMechanism
  unblindingBySensoryCues : AlternateMechanism
  electromagneticInterventionSpecific : AlternateMechanism

-- Existing constructor is kept EMPTY: available literature validates
-- questionnaires in bounded populations, NOT a complete coil trial.
TorusPhenomenologyExperiment : Set₁
TorusPhenomenologyExperiment =
  Experiment.DiscriminatingExperiment
    TorusPhenomenologyProtocolDemand
    AlternateMechanism

data QuestionnaireScoreProvesCoilSpecificEffect : Set where
data HeartCoherenceProvesFifthDimension : Set where
data PsychometricValidationAutomaticallyTransfersToPEMF : Set where
data SyntheticCounterexampleIsRealParticipantData : Set where

noMagneticCauseFromStateScore :
  QuestionnaireScoreProvesCoilSpecificEffect → ⊥
noMagneticCauseFromStateScore ()

heartBiofieldDoesNotProveFifthDimension :
  HeartCoherenceProvesFifthDimension → ⊥
heartBiofieldDoesNotProveFifthDimension ()

instrumentValidatedElsewhereNeedsTransport :
  PsychometricValidationAutomaticallyTransfersToPEMF → ⊥
instrumentValidatedElsewhereNeedsTransport ()

syntheticContrastIsNotMeasuredPeople :
  SyntheticCounterexampleIsRealParticipantData → ⊥
syntheticContrastIsNotMeasuredPeople ()
