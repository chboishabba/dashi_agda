module DASHI.Cognition.PsychotronicsSuccorAttributionRegression where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Cognition.PsychotronicsSuccorSourceAtlasExact as Atlas
import DASHI.Cognition.PsychotronicsScreenshotDiscriminationExact as Frames
import DASHI.Culture.HoeMathLevelsSourceBoundaryExact as HoeMath
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.AnomalousConsciousnessResearchEvidenceContinuumExact as Evidence
import DASHI.Governance.AnomalousConsumerIndexedObligationFibreExact as Consumer
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

-- Original-published source instances are counted individually, including
-- different dated reprints. Common author roots do not become experiments.
-- Earlier 60-source Reddit/Guardian historical cut now has seven further
-- source carriers including real NOAA Bangor records, same-station metadata,
-- an earlier local press item and a Kansas location false-match control.
-- More source objects are NOT more independent weather experiments.
sourceAtlasCountIsEightyTwo :
  Attribution.sourceCount (Attribution.sources Atlas.sourceAtlas) ≡ 82
sourceAtlasCountIsEightyTwo = refl


-- Original NOAA OBS-TIME documentation is a *method*, not a 1953 sensor time;
-- publisher/custodian multiplicity does not add an independent weather trial.
noaaObservationClockSchemaDoesNotProveOnset :
  Attribution.citationImportsProof Atlas.noaaGHCNObsTimeSchema ≡ false
noaaObservationClockSchemaDoesNotProveOnset =
  Atlas.allSourcesRemainNonPromoting Atlas.noaaGHCNObsTimeSchema

noaaHOMRCustodyDoesNotProvideGaugeHour :
  Attribution.citationCreatesAuthority Atlas.noaaHOMRStationHistory ≡ false
noaaHOMRCustodyDoesNotProvideGaugeHour =
  Atlas.allSourcesRemainNonAuthoritative Atlas.noaaHOMRStationHistory

noaaOriginalCOOPFormAccessDoesNotRecoverOriginalForm :
  Attribution.citationImportsProof Atlas.noaaCOOPOriginalFormsGateway ≡ false
noaaOriginalCOOPFormAccessDoesNotRecoverOriginalForm =
  Atlas.allSourcesRemainNonPromoting Atlas.noaaCOOPOriginalFormsGateway

noaaClockAndCOOPAccessShareCustodialRoot :
  Atlas.root Atlas.noaaGHCNObservationClockAvailability ≡
  Atlas.root Atlas.noaaOriginalFormCustodyIsNotObservation
noaaClockAndCOOPAccessShareCustodialRoot = refl

bahramiOriginalAuthorsDoNotProveRodinComparison :
  Attribution.citationImportsProof Atlas.bahramiHelmholtz2025 ≡ false
bahramiOriginalAuthorsDoNotProveRodinComparison =
  Atlas.allSourcesRemainNonPromoting Atlas.bahramiHelmholtz2025


paperAndOriginalRepoAreOneOriginalStudyRoot :
  Atlas.root Atlas.bahramiPaperAndDataSameStudy ≡
  Atlas.root Atlas.bahramiWaterCooledHelmholtzPrecedent
paperAndOriginalRepoAreOneOriginalStudyRoot = refl

originalAuthorRepoCannotImportRodinSuperiority :
  Attribution.citationImportsProof Atlas.bioCoilOriginalAuthorRepository ≡ false
originalAuthorRepoCannotImportRodinSuperiority =
  Atlas.allSourcesRemainNonPromoting Atlas.bioCoilOriginalAuthorRepository


noaaArchiveFilenameDoesNotProveRainOnset :
  Attribution.citationImportsProof Atlas.noaaBangorISD1953Original ≡ false
noaaArchiveFilenameDoesNotProveRainOnset =
  Atlas.allSourcesRemainNonPromoting Atlas.noaaBangorISD1953Original

noaaHourArchiveAndDailyMethodHaveOneCustodialAttribution :
  Atlas.root Atlas.noaaISD1953YearArchivePresent ≡
  Atlas.root Atlas.noaaGHCNObservationClockAvailability
noaaHourArchiveAndDailyMethodHaveOneCustodialAttribution = refl


noaaOriginalISDFormatCannotImportRainHour :
  Attribution.citationImportsProof Atlas.noaaISD2018OriginalFormat ≡ false
noaaOriginalISDFormatCannotImportRainHour =
  Atlas.allSourcesRemainNonPromoting Atlas.noaaISD2018OriginalFormat

noaaNODDDistributionNoticeCannotImportRainHour :
  Attribution.citationImportsProof Atlas.noaaNESDIS2026ISDMigration ≡ false
noaaNODDDistributionNoticeCannotImportRainHour =
  Atlas.allSourcesRemainNonPromoting Atlas.noaaNESDIS2026ISDMigration

noaaSuccessorDataCatalogueCannotImportRainHour :
  Attribution.citationImportsProof Atlas.noaaGHCNh2023OriginalDataset ≡ false
noaaSuccessorDataCatalogueCannotImportRainHour =
  Atlas.allSourcesRemainNonPromoting Atlas.noaaGHCNh2023OriginalDataset

allNOAAMethodCarriersShareOneCustodialRoot :
  Atlas.root Atlas.noaaISDRecordLengthSourceCorrection ≡
  Atlas.root Atlas.noaaGHCNhSuccessorNotIndependentGauge
allNOAAMethodCarriersShareOneCustodialRoot = refl


noaaActual1953BangorHourlyReportNotCausalProof :
  Attribution.citationImportsProof Atlas.noaaBangor1953RealUploadedHourlyCSV ≡ false
noaaActual1953BangorHourlyReportNotCausalProof =
  Atlas.allSourcesRemainNonPromoting Atlas.noaaBangor1953RealUploadedHourlyCSV

noaaOriginalISDAndConverted1953HaveSameCustody :
  Atlas.root Atlas.noaaBangorJul1953HourlyRealWeatherBound ≡
  Atlas.root Atlas.noaaISD1953YearArchivePresent
noaaOriginalISDAndConverted1953HaveSameCustody = refl


noaaSynopticPressureAndRainHaveSameObserverRoot :
  Atlas.root Atlas.noaaBangor1953SynopticPressureBeforeRain ≡
  Atlas.root Atlas.noaaBangorJul1953HourlyRealWeatherBound
noaaSynopticPressureAndRainHaveSameObserverRoot = refl

noaaBangorWindAndClaimClockHaveSameObserverRoot :
  Atlas.root Atlas.noaaBangor1953WindsNotEllsworthOperation ≡
  Atlas.root Atlas.noaaBangorJul1953HourlyRealWeatherBound
noaaBangorWindAndClaimClockHaveSameObserverRoot = refl

noaaPressureJulyReferenceIsNotNewReplication :
  Atlas.root Atlas.noaaBangor1953OverlappingJulyPressureReference ≡
  Atlas.root Atlas.noaaBangor1953SynopticPressureBeforeRain
noaaPressureJulyReferenceIsNotNewReplication = refl

-- Additional original 1953 NOAA station does not change the publisher
-- denominator; observations must retain their actual distinct site keys.
barHarborJuly6Through8Equals130TenthsMm :
  Atlas.tenthsMillimetre Atlas.barHarborJuly6 +
  Atlas.tenthsMillimetre Atlas.barHarborJuly7 +
  Atlas.tenthsMillimetre Atlas.barHarborJuly8 ≡ 130
barHarborJuly6Through8Equals130TenthsMm = refl

twoMaineStationTotalsDifferBy175TenthsMm :
  (Atlas.tenthsMillimetre Atlas.bangorJuly6 +
   Atlas.tenthsMillimetre Atlas.bangorJuly7 +
   Atlas.tenthsMillimetre Atlas.bangorJuly8) ≡
  (Atlas.tenthsMillimetre Atlas.barHarborJuly6 +
   Atlas.tenthsMillimetre Atlas.barHarborJuly7 +
   Atlas.tenthsMillimetre Atlas.barHarborJuly8) + 175
twoMaineStationTotalsDifferBy175TenthsMm = refl

noaaTwoStationSourcesShareCustodialAttributionRoot :
  Atlas.root Atlas.noaaBarHarborRainSourceClaim ≡
  Atlas.root Atlas.noaaBangorRainSourceClaim
noaaTwoStationSourcesShareCustodialAttributionRoot = refl

barHarborPublisherMetadataDoesNotGrantCausality :
  Attribution.citationImportsProof Atlas.noaaBarHarborStationMetadata ≡ false
barHarborPublisherMetadataDoesNotGrantCausality =
  Atlas.allSourcesRemainNonPromoting Atlas.noaaBarHarborStationMetadata

-- Published numerical agreement is a property of printed papers, not
-- a source-native byte witness for two independently acquired 2013/2024 runs.
rodinRoundedMatchingPaperDoesNotTransferProof :
  Attribution.citationImportsProof Atlas.ramirezRodinRMF2024 ≡ false
rodinRoundedMatchingPaperDoesNotTransferProof =
  Atlas.allSourcesRemainNonPromoting Atlas.ramirezRodinRMF2024

rodinRawMeasurementIdentityNotFromCitation :
  Atlas.citationCreatesTruth Atlas.rodinRoundedTableDoesNotProveRawIdentity ≡ false
rodinRawMeasurementIdentityNotFromCitation = refl

-- RVML organiser archives and its uploader account represent one historical
-- programme origin; neither is Croft's narrator root or a verified transfer.
gentryRvmlMetadataIsSameOrganiserRoot :
  Atlas.root Atlas.rvmlGentryNamedEvent ≡
  Atlas.root Atlas.rvmlGentryFlanaganAdvertisedTopic
gentryRvmlMetadataIsSameOrganiserRoot = refl

rvmlCarrierCannotCreateProof :
  Attribution.citationImportsProof Atlas.rvmlGentryVideoMetadata ≡ false
rvmlCarrierCannotCreateProof =
  Atlas.allSourcesRemainNonPromoting Atlas.rvmlGentryVideoMetadata

rvmlProgrammeCannotCreateInstitutionalAuthority :
  Attribution.citationCreatesAuthority Atlas.rvmlGentry2003Programme ≡ false
rvmlProgrammeCannotCreateInstitutionalAuthority =
  Atlas.allSourcesRemainNonAuthoritative Atlas.rvmlGentry2003Programme

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
-- Recovering the original pictured copper-star manufacturer's 24-point
-- devices does not turn a dated third-party 14-point PATENT into proof
-- of inherited winding design or therapeutic/ion experiments.
------------------------------------------------------------------------

liveGoldeneyeAndIndexedDarkKnightShareSellerOnly :
  Atlas.root Atlas.zeroPointGoldeneyeMakerClaim ≡
  Atlas.root Atlas.zeroPointStarshipSphereClaim
liveGoldeneyeAndIndexedDarkKnightShareSellerOnly = refl

goldeneyeIsDifferentAdvertisedVersion :
  Atlas.relationClass Atlas.zeroPointMakerVersionsAreDistinct ≡
  Atlas.documentaryDistinction
goldeneyeIsDifferentAdvertisedVersion = refl

makerWebsiteDeclaresOriginalPosterHandle :
  Atlas.relationClass Atlas.zeroPointSiteExplicitlyLinksAccount ≡
  Atlas.contemporarySelfAttribution
makerWebsiteDeclaresOriginalPosterHandle = refl

makerSiteToHandleDoesNotProveOriginalVideoSKU :
  Atlas.historicalTransmissionProved Atlas.zeroPointSiteExplicitlyLinksAccount ≡ false
makerSiteToHandleDoesNotProveOriginalVideoSKU = refl

wongPatentIsOnlyDesignFamilyAnalogy :
  Atlas.relationClass Atlas.wongPatentIsNotStarshipInheritance ≡
  Atlas.hardwareAnalogyOnly
wongPatentIsOnlyDesignFamilyAnalogy = refl

wongPatentDoesNotProveHistoricalTransmission :
  Atlas.historicalTransmissionProved Atlas.wongPatentIsNotStarshipInheritance ≡ false
wongPatentDoesNotProveHistoricalTransmission = refl

wongApplicationCannotCreateScientificAuthority :
  Attribution.citationCreatesAuthority Atlas.wongStarAmplifierPatent ≡ false
wongApplicationCannotCreateScientificAuthority =
  Atlas.allSourcesRemainNonAuthoritative Atlas.wongStarAmplifierPatent

liveSellerListingCannotCreateScientificProof :
  Attribution.citationImportsProof Atlas.zeroPointGoldeneye24PointLive ≡ false
liveSellerListingCannotCreateScientificProof =
  Atlas.allSourcesRemainNonPromoting Atlas.zeroPointGoldeneye24PointLive

------------------------------------------------------------------------
-- Phase-1 dated-source and exact 2024 citation audit regression guards.
-- Definitional checks only, NOT journal/magnetometer re-analysis or CI.
------------------------------------------------------------------------

croftTwoSourceDatesShareAuthorialRoot :
  Atlas.root Atlas.croftAugustNoPublishedGuideClaim ≡
  Atlas.root Atlas.croftOriginalGuide2003Claim
croftTwoSourceDatesShareAuthorialRoot = refl

croftNamedGuideDoesNotProveGentryOriginalAuthorship :
  Atlas.historicalTransmissionProved Atlas.croftJanGuideNotGentryProof ≡ false
croftNamedGuideDoesNotProveGentryOriginalAuthorship = refl

croftAugustAndJanuaryPublicationClaimsDistinct :
  Atlas.relationClass Atlas.croftInstructionPublicationDatesDistinct ≡
  Atlas.documentaryDistinction
croftAugustAndJanuaryPublicationClaimsDistinct = refl

-- Tau electric-field cell-line measurements are attributed to RSC's
-- original study, never a 2024 Rodin/Helmholtz or clinical trial receipt.
pandeyTauOriginalPublicationDoesNotImportMagneticCoilProof :
  Attribution.citationImportsProof Atlas.pandeyTauEF2019 ≡ false
pandeyTauOriginalPublicationDoesNotImportMagneticCoilProof =
  Atlas.allSourcesRemainNonPromoting Atlas.pandeyTauEF2019

pandeyTauResearchProposalNotClinicalProof :
  Atlas.citationCreatesTruth Atlas.pandeyTau2019OriginalExperimentScope ≡ false
pandeyTauResearchProposalNotClinicalProof = refl

pandey2017OriginalFieldStudyDoesNotProve2024GeometryClaim :
  Attribution.citationImportsProof Atlas.pandeyFFField2017 ≡ false
pandey2017OriginalFieldStudyDoesNotProve2024GeometryClaim =
  Atlas.allSourcesRemainNonPromoting Atlas.pandeyFFField2017

pandey2017ClaimStaysSourceBound :
  Atlas.citationCreatesTruth Atlas.pandey2017FieldExperimentScope ≡ false
pandey2017ClaimStaysSourceBound = refl

-- Source-original patent and DOI-linked author declaration agree on
-- an application ID, not a clinical efficacy, grant or magnetic-coil effect.
saikiaPatentOriginalDoesNotTransferClinicalAuthority :
  Attribution.citationCreatesAuthority Atlas.saikiaFieldPatent2019 ≡ false
saikiaPatentOriginalDoesNotTransferClinicalAuthority =
  Atlas.allSourcesRemainNonAuthoritative Atlas.saikiaFieldPatent2019

saikiaPCTExactJoinDoesNotConstituteTherapeuticProof :
  Atlas.citationCreatesTruth Atlas.saikiaPCTExactPatentIdentityClaim ≡ false
saikiaPCTExactJoinDoesNotConstituteTherapeuticProof = refl

saikiaElectrodePatentDoesNotProveRodinComparison :
  Atlas.citationCreatesTruth Atlas.saikiaElectrodePatentDoesNotLicenseRodinBenefit ≡ false
saikiaElectrodePatentDoesNotProveRodinComparison = refl

saikiaOriginalResearchCannotCreateIndependentRodinComparison :
  Attribution.citationCreatesAuthority Atlas.saikiaAmyloid2019 ≡ false
saikiaOriginalResearchCannotCreateIndependentRodinComparison =
  Atlas.allSourcesRemainNonAuthoritative Atlas.saikiaAmyloid2019

-- 2024 Eq(7) operator scope: a genuine finite polynomial witness.
-- These definitions encode d(a+b*x)/dx=b. For the 3D potential
-- A=(0,x,0), B=curl A=(0,0,1) is constant and grad B = zero.
-- This is a toy exact algebraic witness, NOT an Agda continuum theorem
-- about the paper's actual geometry or measured Hall probe data.
record AffinePolynomialOneD : Set where
  constructor affinePolynomial
  field
    intercept slope : Nat
open AffinePolynomialOneD

differentiateAffine : AffinePolynomialOneD → Nat
differentiateAffine p = slope p

rodinToyPotentialAy : AffinePolynomialOneD
rodinToyPotentialAy = affinePolynomial 0 1

rodinToyMagneticFieldBz : AffinePolynomialOneD
rodinToyMagneticFieldBz =
  affinePolynomial (differentiateAffine rodinToyPotentialAy) 0

rodinEq7CurlValueNotFieldSpatialGradient :
  differentiateAffine rodinToyPotentialAy ≡ 1
rodinEq7CurlValueNotFieldSpatialGradient = refl

rodinToyFieldDerivativeIsZero :
  differentiateAffine rodinToyMagneticFieldBz ≡ 0
rodinToyFieldDerivativeIsZero = refl

rodinToyCurlAndFieldGradientCannotBeEqual :
  differentiateAffine rodinToyPotentialAy ≡
  differentiateAffine rodinToyMagneticFieldBz → ⊥
rodinToyCurlAndFieldGradientCannotBeEqual ()

rodin2024Eq7PaperClaimsDoNotTransferProof :
  Attribution.citationImportsProof Atlas.ramirezRodinRMF2024 ≡ false
rodin2024Eq7PaperClaimsDoNotTransferProof =
  Atlas.allSourcesRemainNonPromoting Atlas.ramirezRodinRMF2024

-- The ACS publisher's Supporting Information listing is a bibliographic
-- receipt, not a native SI PDF page or independent original experiment.
saikiaPublisherSITopicListingNotMeasuredCoilResult :
  Attribution.citationImportsProof Atlas.saikiaAmyloid2019 ≡ false
saikiaPublisherSITopicListingNotMeasuredCoilResult =
  Atlas.allSourcesRemainNonPromoting Atlas.saikiaAmyloid2019

saikiaSITopicListingDoesNotProveSixtyPercent :
  Atlas.citationCreatesTruth Atlas.saikia2019ACSOriginalSITopicListing ≡ false
saikiaSITopicListingDoesNotProveSixtyPercent = refl

------------------------------------------------------------------------
-- ACS SAiKIA ORIGINAL 2019 SI LISTING: AN IDENTIFIABILITY COUNTERMODEL
--
-- The publisher's original SI catalogue mentions a magnetic-field topic.
-- This finite *hypothetical* pair demonstrates nonidentification of a
-- **specific** matched Rodin/Helmholtz ~60%-comparator *from that listing*.
-- Neither model alleges what the actual unread PDF contains. Original
-- experimental credit remains Saikia et al. and Ramirez-Galindo et al.
------------------------------------------------------------------------

data PossibleSaikiaSIBody : Set where
  magneticSecondaryAggregationOnly : PossibleSaikiaSIBody
  magneticSecondaryAggregationWithMatchedCoils : PossibleSaikiaSIBody

siPublisherMFListing : PossibleSaikiaSIBody → Bool
siPublisherMFListing magneticSecondaryAggregationOnly = true
siPublisherMFListing magneticSecondaryAggregationWithMatchedCoils = true

siBodyHasNamedMatchedCoil60Percent : PossibleSaikiaSIBody → Bool
siBodyHasNamedMatchedCoil60Percent magneticSecondaryAggregationOnly = false
siBodyHasNamedMatchedCoil60Percent magneticSecondaryAggregationWithMatchedCoils = true

siSameListing : siPublisherMFListing magneticSecondaryAggregationOnly ≡
                siPublisherMFListing magneticSecondaryAggregationWithMatchedCoils
siSameListing = refl

siDifferentPotentialComparatorResult :
  siBodyHasNamedMatchedCoil60Percent magneticSecondaryAggregationOnly ≡
  siBodyHasNamedMatchedCoil60Percent magneticSecondaryAggregationWithMatchedCoils → ⊥
siDifferentPotentialComparatorResult ()

siListingDoesNotFactorSpecificComparator :
  (decoder : Bool → Bool) →
  (∀ w → decoder (siPublisherMFListing w) ≡
          siBodyHasNamedMatchedCoil60Percent w) →
  ⊥
siListingDoesNotFactorSpecificComparator decoder claimed
  with trans (sym (claimed magneticSecondaryAggregationOnly))
             (claimed magneticSecondaryAggregationWithMatchedCoils)
... | ()

------------------------------------------------------------------------
-- 2024 RODIN TABLE II: SAME CENTRE B, DIFFERENT LOCAL FIELD SLOPE.
--
-- These are exact *synthetic local linear field* families, not original
-- Hall-probe recordings or measured real-coil gradients.
-- The general field form is B=(g*z, 0, b+g*x) with b>0. Its spatial
-- divergence is zero and its curl is zero because dBx/dz=dBz/dx=g;
-- the centre has B=(0,0,b), even when g changes. At z=0 the Bz
-- slope is g; for b>0 the magnitude gradient at the centre is g.
-- The finite Nat representation below only certifies equality of
-- polynomial COEFFICIENTS and the centre-value collision, not full
-- 3D continuum Maxwell identities or actual SI metrology.
------------------------------------------------------------------------

record RodinLocalLinearMagneticField : Set where
  constructor local-linear-B
  field
    centreBz : Nat
    BxSlopeInZ : Nat
    BzSlopeInX : Nat
open RodinLocalLinearMagneticField

uniformSameCentreField : RodinLocalLinearMagneticField
uniformSameCentreField = local-linear-B 4 0 0

gradientSameCentreField : RodinLocalLinearMagneticField
gradientSameCentreField = local-linear-B 4 1 1

rodinCentreFieldsIdentical :
  centreBz uniformSameCentreField ≡ centreBz gradientSameCentreField
rodinCentreFieldsIdentical = refl

rodinSyntheticGradientCurlFreeCoefficients :
  BxSlopeInZ gradientSameCentreField ≡
  BzSlopeInX gradientSameCentreField
rodinSyntheticGradientCurlFreeCoefficients = refl

rodinSyntheticUniformCurlFreeCoefficients :
  BxSlopeInZ uniformSameCentreField ≡
  BzSlopeInX uniformSameCentreField
rodinSyntheticUniformCurlFreeCoefficients = refl

rodinCenterOnlyDoesNotDetermineSpatialSlope :
  BzSlopeInX uniformSameCentreField ≡
  BzSlopeInX gradientSameCentreField → ⊥
rodinCenterOnlyDoesNotDetermineSpatialSlope ()

ramirezRef24ComparisonNotProvenByCitation :
  Atlas.historicalTransmissionProved Atlas.ramirezRef24NotValidatedCoilComparison ≡ false
ramirezRef24ComparisonNotProvenByCitation = refl

ramirezRef12NotSamePerezCitation :
  Atlas.relationClass Atlas.ramirezRef12NotPerez2013 ≡
  Atlas.documentaryDistinction
ramirezRef12NotSamePerezCitation = refl

identicalSourceNumbersDoNotProveIndependentMeasurement :
  Atlas.historicalTransmissionProved Atlas.perezRamirezTableOverlapUnresolved ≡ false
identicalSourceNumbersDoNotProveIndependentMeasurement = refl

guanajuatoOriginalStudyFamilySharesResearchRoot :
  Atlas.root Atlas.perez2013TableClaim ≡
  Atlas.root Atlas.ramirez2024ReusedNumbersQuestion
guanajuatoOriginalStudyFamilySharesResearchRoot = refl

crofts2003SourceDoesNotEstablishPhysics :
  Attribution.citationImportsProof Atlas.croftPowerWand2003 ≡ false
crofts2003SourceDoesNotEstablishPhysics =
  Atlas.allSourcesRemainNonPromoting Atlas.croftPowerWand2003

------------------------------------------------------------------------
-- Exact source-status guards on the three unlike cloudbusting traditions.
-- These are source-written Agda definitional regression expressions, not
-- kernel receipts, controlled meteorology or human studies.
------------------------------------------------------------------------

reichAuthorAlsoRecordsNaturalWeatherFront :
  Atlas.relationClass Atlas.reichReportHasNaturalWeatherFront ≡
  Atlas.documentaryDistinction
reichAuthorAlsoRecordsNaturalWeatherFront = refl

reichReportedRainNotProofOfOrgoneCause :
  Atlas.newPhysicsEstablished Atlas.reichReportHasNaturalWeatherFront ≡ false
reichReportedRainNotProofOfOrgoneCause = refl

archivalFindingAidDoesNotPromoteToMeasuredRain :
  Atlas.historicalTransmissionProved Atlas.reichArchiveCatalogDoesNotProveRain ≡ false
archivalFindingAidDoesNotPromoteToMeasuredRain = refl

guardianRetellingNotAnotherMaineOperation :
  Atlas.relationClass Atlas.guardianRetellingNotSecond1953Trial ≡
  Atlas.documentaryDistinction
guardianRetellingNotAnotherMaineOperation = refl

modernResinQuartzBucketNotReichWaterPipes :
  Atlas.relationClass Atlas.guardianModernBucketNotReichSameApparatus ≡
  Atlas.documentaryDistinction
modernResinQuartzBucketNotReichWaterPipes = refl

croftChembusterAuthorialRootReused :
  Atlas.root Atlas.croftModernPipeSelfAttributionClaim ≡
  Atlas.root Atlas.croftOriginalGuide2003Claim
croftChembusterAuthorialRootReused = refl

adachiRetailCopyDoesNotVerifyWeatherControl :
  Atlas.historicalTransmissionProved Atlas.adachiSellerNotIndependentWeatherObservation ≡ false
adachiRetailCopyDoesNotVerifyWeatherControl = refl

redditMindCloudNotOriginalReichMachine :
  Atlas.relationClass Atlas.redditMindCloudNotReichPipeMachine ≡
  Atlas.documentaryDistinction
redditMindCloudNotOriginalReichMachine = refl

redditBookInfluenceNotMeteorologicalExperiment :
  Atlas.historicalTransmissionProved Atlas.redditBachReadingNotWeatherProof ≡ false
redditBookInfluenceNotMeteorologicalExperiment = refl

constableReaderTestimonyNotBookExperimentalReceipt :
  Atlas.historicalTransmissionProved Atlas.redditConstableReadingNotWeatherProof ≡ false
constableReaderTestimonyNotBookExperimentalReceipt = refl

sladeMentalClaimNotBrainPhysicsAuthority :
  Attribution.citationCreatesAuthority Atlas.sladeMindCloud1998 ≡ false
sladeMentalClaimNotBrainPhysicsAuthority =
  Atlas.allSourcesRemainNonAuthoritative Atlas.sladeMindCloud1998

bachLiteratureNotSladeInventorship :
  Atlas.relationClass Atlas.bachAndSladeNotDirectInventionChain ≡
  Atlas.thematicResemblanceOnly
bachLiteratureNotSladeInventorship = refl

kateBushLiteraryCreditDoesNotCertifyWeather :
  Atlas.historicalTransmissionProved Atlas.bushOriginalPeterMemoirAttribution ≡ false
kateBushLiteraryCreditDoesNotCertifyWeather = refl

wmoContextDoesNotPromoteOriginalReichWeatherCausation :
  Atlas.historicalTransmissionProved Atlas.wmoStatementCannotProveReichMechanism ≡ false
wmoContextDoesNotPromoteOriginalReichWeatherCausation = refl

originalWindingGuideSiteNotAnAtmosphericDevice :
  Atlas.relationClass Atlas.windingGuideDomainNotRainMachineProof ≡
  Atlas.documentaryDistinction
originalWindingGuideSiteNotAnAtmosphericDevice = refl

------------------------------------------------------------------------
-- Original Bangor weather receipt: arithmetic over quoted GHCN-Daily
-- tenths-mm values; the weather cause and source-endpoint remain external.
------------------------------------------------------------------------

independentBangorJuly6To8Precipitation : 
  Atlas.tenthsMillimetre Atlas.bangorJuly6 +
  Atlas.tenthsMillimetre Atlas.bangorJuly7 +
  Atlas.tenthsMillimetre Atlas.bangorJuly8 ≡ 305
independentBangorJuly6To8Precipitation =
  Atlas.bangorJuly6Through8TotalTenthsMm

noaaMeasuredRainDoesNotProveReichCause :
  Atlas.historicalTransmissionProved Atlas.bangorOriginalObservedRainNotRainmakingProof ≡ false
noaaMeasuredRainDoesNotProveReichCause = refl

noaaTwoPagesOneWeatherStation :
  Atlas.root Atlas.noaaBangorRainSourceClaim ≡
  Atlas.root Atlas.noaaBangorStationIdentityClaim
noaaTwoPagesOneWeatherStation = refl

noaaStationMetadataNotIndependentSecondRainTrial :
  Atlas.relationClass Atlas.noaaStationIdentityNotTwoWeatherExperiments ≡
  Atlas.documentaryDistinction
noaaStationMetadataNotIndependentSecondRainTrial = refl

july8NewspaperNotSecondRainstorm :
  Atlas.historicalTransmissionProved Atlas.ellsworthAmericanEarlierButNotIndependentWeatherTrial ≡ false
july8NewspaperNotSecondRainstorm = refl

ellsworthKansasNotOriginalMaineLocale :
  Atlas.relationClass Atlas.kansasWeatherIsNotMaineReichEvent ≡
  Atlas.documentaryDistinction
ellsworthKansasNotOriginalMaineLocale = refl

------------------------------------------------------------------------
-- RVML attributed 2003 publicity is one organiser root, not original
-- Gentry source plans, Navy employment records or Reich weather proof.
------------------------------------------------------------------------

rvmlPromoReichClassNotConstructedDeviceReceipt :
  Atlas.historicalTransmissionProved Atlas.rvmlPromotionalReichBuildNotVerifiedMechanism ≡ false
rvmlPromoReichClassNotConstructedDeviceReceipt = refl

rvmlFlanaganNamedTopicNotOriginalHandoff :
  Atlas.relationClass Atlas.rvmlFlanaganNamedTopicNotOriginalCoilHandoff ≡
  Atlas.documentaryDistinction
rvmlFlanaganNamedTopicNotOriginalHandoff = refl

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

-- Candidate psychometric tools have published *construct* validity within
-- their stated populations; other outcomes are not silently assigned an
-- unrelated questionnaire, retailer specification or commercial claim.
data PsychometricCandidate : OutcomeDomain → Set where
  nadaForNondualReport :
    PsychometricCandidate immediateNondualReport
  meqForMysticalExperience :
    PsychometricCandidate mysticalFourFactorExperience
  ediForSelfExperience :
    PsychometricCandidate egoDissolutionReport
  ascForAlteredState :
    PsychometricCandidate alteredStateFactorReport

candidatePsychometricSource :
  (d : OutcomeDomain) →
  PsychometricCandidate d →
  Attribution.AttributedSource
candidatePsychometricSource .immediateNondualReport nadaForNondualReport =
  Atlas.hanleyNADA2018
candidatePsychometricSource .mysticalFourFactorExperience meqForMysticalExperience =
  Atlas.macleanMEQ2012
candidatePsychometricSource .egoDissolutionReport ediForSelfExperience =
  Atlas.nourEDI2016
candidatePsychometricSource .alteredStateFactorReport ascForAlteredState =
  Atlas.kervadecFiveDASC2026

-- No instance asserts that NADA measures sustained clinical function,
-- that HeartMath's website validates HRV measurement, that a retailer
-- spec is a calibrated B-field meter, or that an ASC paper validates
-- blinding/expectancy assessment. Those require their own instruments.

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

------------------------------------------------------------------------
-- Cross-pollinate existing consumer-dependent evidence requirements:
-- a subjective state report is not a demonstrated induction mechanism.
-- This reuses the GOVERNANCE owner; no novel evidence ladder invented.
------------------------------------------------------------------------

meditativeAndPsychedelicInductionsStayDifferent :
  Evidence.inductionMethod Evidence.meditationWorld ≡
  Evidence.inductionMethod Evidence.psychedelicWorld → ⊥
meditativeAndPsychedelicInductionsStayDifferent = Evidence.methodDiffers

selfReportSupportCannotAutomaticallyCloseFieldMechanism :
  Consumer.PhenomenologyClosurePromotesMechanismClosure → ⊥
selfReportSupportCannotAutomaticallyCloseFieldMechanism =
  Consumer.phenomenologyClosureDoesNotPromoteMechanismClosure

psiClaimCannotFollowFromPsychedelicPhenomenology :
  Evidence.PsychedelicPhenomenologyPromotesRemoteViewing → ⊥
psiClaimCannotFollowFromPsychedelicPhenomenology =
  Evidence.psychedelicPhenomenologyDoesNotPromoteRemoteViewing

------------------------------------------------------------------------
-- PARETO COVARIATION COUNTEREXAMPLE, SOURCE-SPECIFIC AND SYNTHETIC.
--
-- If the coil drive and perceptible coil cues always switch together,
-- subjective improvement (even if genuine) cannot distinguish an
-- electromagnetic cause from the audible/tactile cue mechanism.
--
-- This is a different obstruction from the earlier coarse unity-report
-- nonfactorability witness: here even an active-vs-sham *difference*
-- fails causal attribution when the physical causes covary.
------------------------------------------------------------------------

data SyntheticCausalExplanation : Set where
  effectFromFieldOnly : SyntheticCausalExplanation
  effectFromSensoryCueOnly : SyntheticCausalExplanation

data SyntheticObservedTwoArmContrast : Set where
  activeBeatsShamBySameAmount : SyntheticObservedTwoArmContrast

-- Both models predict the same pairwise observation by construction.
predictedTwoArmContrast :
  SyntheticCausalExplanation → SyntheticObservedTwoArmContrast
predictedTwoArmContrast _ = activeBeatsShamBySameAmount

data AttributionTarget : Set where
  electromagneticAttribution : AttributionTarget
  audibleTactileAttribution : AttributionTarget

causalExplanation : SyntheticCausalExplanation → AttributionTarget
causalExplanation effectFromFieldOnly = electromagneticAttribution
causalExplanation effectFromSensoryCueOnly = audibleTactileAttribution

twoDistinctExplanationsSameContrast :
  causalExplanation effectFromFieldOnly ≡
  causalExplanation effectFromSensoryCueOnly → ⊥
twoDistinctExplanationsSameContrast ()

twoArmEffectDoesNotIdentifyPhysicalMechanism :
  INF.FactorsThrough predictedTwoArmContrast causalExplanation → ⊥
twoArmEffectDoesNotIdentifyPhysicalMechanism =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      effectFromFieldOnly
      effectFromSensoryCueOnly
      refl
      twoDistinctExplanationsSameContrast)

------------------------------------------------------------------------
-- No empirical trial is added. The factorial design is only a *proposed*
-- separation of electromagnetic drive and sensory cues, subject to a
-- bench-tested ability to manipulate or credibly mask those two channels
-- without differential expectation, heat, vibration, noise or risk.
------------------------------------------------------------------------

data NominalExposure : Set where
  noEmField emFieldOn : NominalExposure

data NominalCue : Set where
  noPerceptibleCue matchedSensoryCue : NominalCue

record SyntheticFactorialArm : Set where
  constructor synthetic-factorial-arm
  field
    electromagnetic : NominalExposure
    sensory : NominalCue
open SyntheticFactorialArm public

factorial00 factorial10 factorial01 factorial11 : SyntheticFactorialArm
factorial00 = synthetic-factorial-arm noEmField noPerceptibleCue
factorial10 = synthetic-factorial-arm emFieldOn noPerceptibleCue
factorial01 = synthetic-factorial-arm noEmField matchedSensoryCue
factorial11 = synthetic-factorial-arm emFieldOn matchedSensoryCue

fieldStatusDiffersWithCuesFixed :
  electromagnetic factorial00 ≡ electromagnetic factorial10 → ⊥
fieldStatusDiffersWithCuesFixed ()

cueStatusDiffersWithFieldFixed :
  sensory factorial00 ≡ sensory factorial01 → ⊥
cueStatusDiffersWithFieldFixed ()

-- These are mathematically distinct design cells; making them
-- acoustically indistinguishable, physically feasible and safe is
-- precisely the missing real-world receipt.
record DeviceExperimentFeasibility : Set where
  constructor device-experiment-feasibility
  field
    samePhysicalCoilIdentity : String
    activeShamFieldSensorTrace : String
    separateSensoryCueManipulation : String
    amplifierAndTransducerSpectra : String
    humanBlindingCredibilityAssessment : String
    independentElectricalSafetyApproval : String
    shamInterferenceAndLeakageAudit : String
    participantConsentAndOversight : String

data FactorialDesignProvesRealWorldManipulation : Set where
data MoreGroupsGuaranteeBlinding : Set where
data ActiveShamContrastProvesMagneticCause : Set where

formalCellsDoNotBuildPhysicalDevice :
  FactorialDesignProvesRealWorldManipulation → ⊥
formalCellsDoNotBuildPhysicalDevice ()

moreGroupsDoNotEnsureMasking :
  MoreGroupsGuaranteeBlinding → ⊥
moreGroupsDoNotEnsureMasking ()

confoundedContrastDoesNotProveFieldCause :
  ActiveShamContrastProvesMagneticCause → ⊥
confoundedContrastDoesNotProveFieldCause ()

------------------------------------------------------------------------
-- Two actual provenance instances of sham control: real measured trial
-- versus protocol proposing a later trial, distinct original author roots.
------------------------------------------------------------------------

clinicalSilentShamIsNotLoudCoilReceipt :
  Atlas.relationClass Atlas.silentShamDoesNotCertifyLoudCoil ≡
  Atlas.historicalMechanismPrecedentOnly
clinicalSilentShamIsNotLoudCoilReceipt = refl

proposedShamIsNotCompletedDeviceStudy :
  Atlas.relationClass Atlas.futureShamProposalDoesNotGiveObservedTrial ≡
  Atlas.thematicResemblanceOnly
proposedShamIsNotCompletedDeviceStudy = refl

clinicalAndProtocolSourcesDiffer :
  Atlas.root Atlas.shupakShamScope ≡
  Atlas.root Atlas.duShamDesignProposal → ⊥
clinicalAndProtocolSourcesDiffer ()

protocolCannotImportAClinicalResult :
  Attribution.citationImportsProof Atlas.duAssessorBlindedProtocol2026 ≡ false
protocolCannotImportAClinicalResult =
  Atlas.allSourcesRemainNonPromoting Atlas.duAssessorBlindedProtocol2026

------------------------------------------------------------------------
-- MINIMAL CONDITIONAL ESTIMAND: 01 VS 11 NEEDS NO FOUR-CELL FACTORIAL
-- WHEN THE SENSORY CUE IS TRULY THE SAME AND EM DIFFERS.
-- This mathematical possibility is NOT a real-world masking receipt.
-- Full 2x2 is needed to separately estimate EM main and EMxCue
-- interaction in the declared four-parameter model.
------------------------------------------------------------------------

matchedCueHasSameNominalSensoryState :
  sensory factorial01 ≡ sensory factorial11
matchedCueHasSameNominalSensoryState = refl

matchedCueChangesNominalEmExposure :
  electromagnetic factorial01 ≡ electromagnetic factorial11 → ⊥
matchedCueChangesNominalEmExposure ()

data MatchedNominalCueMeansInstrumentalMasking : Set where
data ConditionalFieldContrastEqualsFieldMainEffect : Set where

formalCueEqualityIsNotAnAcousticMeasurement :
  MatchedNominalCueMeansInstrumentalMasking → ⊥
formalCueEqualityIsNotAnAcousticMeasurement ()

oneConditionalContrastDoesNotIdentifyInteraction :
  ConditionalFieldContrastEqualsFieldMainEffect → ⊥
oneConditionalContrastDoesNotIdentifyInteraction ()
