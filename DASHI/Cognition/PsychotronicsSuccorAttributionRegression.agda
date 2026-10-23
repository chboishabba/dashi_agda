module DASHI.Cognition.PsychotronicsSuccorAttributionRegression where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Cognition.PsychotronicsSuccorSourceAtlasExact as Atlas
import DASHI.Cognition.PsychotronicsScreenshotDiscriminationExact as Frames

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
sourceAtlasCountIsSeventeen :
  Attribution.sourceCount (Attribution.sources Atlas.sourceAtlas) ≡ 17
sourceAtlasCountIsSeventeen = refl

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
