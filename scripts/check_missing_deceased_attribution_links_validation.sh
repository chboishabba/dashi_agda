#!/usr/bin/env bash
set -euo pipefail

# Focused source-attribution/static contract. This is not Agda/kernel CI.

grep -q 'liTorrPRB1992APS' DASHI/Physics/ExoticGravity/LiTorrPRB1992AttributedSourceExact.agda
grep -q '10.1103/PhysRevB.46.5489' DASHI/Physics/ExoticGravity/LiTorrPRB1992AttributedSourceExact.agda
grep -q 'apsLandingPaysExactEquationLocator = false' DASHI/Physics/ExoticGravity/LiTorrPRB1992AttributedSourceExact.agda
grep -q 'apsTheoryPaysExperimentalAntigravity = false' DASHI/Physics/ExoticGravity/LiTorrPRB1992AttributedSourceExact.agda

grep -q 'attachedDiscoveryLinksA' DASHI/Culture/MissingDeceasedInvestigativeDiscoveryLinksAExact.agda
grep -q 'link.aps.org/doi/10.1103/PhysRevB.46.5489' DASHI/Culture/MissingDeceasedInvestigativeDiscoveryLinksAExact.agda
grep -q 'attachedDiscoveryLinksB' DASHI/Culture/MissingDeceasedInvestigativeDiscoveryLinksBExact.agda
grep -q 'attachedDiscoveryLinksC' DASHI/Culture/MissingDeceasedInvestigativeDiscoveryLinksCExact.agda
grep -q 'SP23012p.pdf' DASHI/Culture/MissingDeceasedInvestigativeDiscoveryLinksCExact.agda

grep -q 'investigativeSourceAtlas' DASHI/Culture/MissingDeceasedInvestigativeAttributedSourceAtlasExact.agda
grep -q 'newMexicoClusterIsSourceBacked = true' DASHI/Culture/MissingDeceasedSouthwestGeographyDiscriminatorExact.agda
grep -q 'whiteSandsEventAnchorIsUnpaid = true' DASHI/Culture/MissingDeceasedSouthwestGeographyDiscriminatorExact.agda
grep -q 'lanlKirtlandWhiteSandsTriangleIsPaid = false' DASHI/Culture/MissingDeceasedSouthwestGeographyDiscriminatorExact.agda
grep -q 'secondaryReportDoesNotBecomePrimaryEventFact = true' DASHI/Culture/MissingDeceasedReportedAnomalyAttributionLedgerExact.agda

grep -q 'surp2023Maiwald' DASHI/Culture/MaiwaldSURPActionSpectroscopyManifestationSuccessionExact.agda
grep -q 'surp2024Nemchick' DASHI/Culture/MaiwaldSURPActionSpectroscopyManifestationSuccessionExact.agda
grep -q 'surp2025Nemchick' DASHI/Culture/MaiwaldSURPActionSpectroscopyManifestationSuccessionExact.agda
grep -q 'projectContinuityPaysRawDataCustody = false' DASHI/Culture/MaiwaldSURPActionSpectroscopyManifestationSuccessionExact.agda

# Full 71-page attachment accounting and promotion boundary.
grep -q 'attachmentPages1Through71AccountedFor = true' DASHI/Culture/MissingDeceasedFullAttachmentClaimAtlasExact.agda
grep -q 'engineeringStackConvergence' DASHI/Culture/MissingDeceasedFullAttachmentClaimAtlasExact.agda
grep -q 'timeCrystalPropulsion' DASHI/Culture/MissingDeceasedFullAttachmentClaimAtlasExact.agda
grep -q 'qetScaleUp' DASHI/Culture/MissingDeceasedFullAttachmentClaimAtlasExact.agda
grep -q 'wormholeScaleUp' DASHI/Culture/MissingDeceasedFullAttachmentClaimAtlasExact.agda
grep -q 'counterEspionageSweep' DASHI/Culture/MissingDeceasedFullAttachmentClaimAtlasExact.agda
grep -q 'singleCrystalMondaloyEquivalencePaid = false' DASHI/Culture/MissingDeceasedFullAttachmentClaimAtlasExact.agda

grep -q 'palantirAIPConClaim' DASHI/Culture/MissingDeceasedAttachmentSourcePromotionLedgerExact.agda
grep -q 'trinityClathrateQuasicrystalClaim' DASHI/Culture/MissingDeceasedAttachmentSourcePromotionLedgerExact.agda
grep -q 'projectAnchorClaim' DASHI/Culture/MissingDeceasedAttachmentSourcePromotionLedgerExact.agda
grep -q 'armyOTAClaim' DASHI/Culture/MissingDeceasedAttachmentSourcePromotionLedgerExact.agda
grep -q 'missingPrimaryCarrierDoesNotProveSuppression = true' DASHI/Culture/MissingDeceasedAttachmentSourcePromotionLedgerExact.agda

# Newly discovered exact-identifier collision must remain a same-object residual.
grep -q 'texasAuditAgreementNumberCollision' DASHI/Culture/NingLiArmyAgreementIdentifierCollisionExact.agda
grep -q 'agreementNumberCollisionDoesNotCreateSameObject = true' DASHI/Culture/NingLiArmyAgreementIdentifierCollisionExact.agda
grep -q 'lockheedPassThroughInterpretationPaid = false' DASHI/Culture/NingLiArmyAgreementIdentifierCollisionExact.agda
grep -q 'NingLiArmyAgreementIdentifierCollisionExact' DASHI/Culture/MissingDeceasedInvestigativeAttributionEverything.agda
grep -q 'ningLiAdministrativeIdentifierCollisionPareto' DASHI/Culture/NingLiAdministrativeIdentifierCollisionParetoExact.agda

# Primary Texas audit recurrence repair: FY2005 + FY2006 Lockheed pass-through appearances.
grep -q 'texasFY2005LockheedAppearance' DASHI/Culture/NingLiArmyTexasAuditPrimaryInspectionExact.agda
grep -q 'texasFY2006LockheedAppearance' DASHI/Culture/NingLiArmyTexasAuditPrimaryInspectionExact.agda
grep -q 'fy2005DisplayedAmount = "17529"' DASHI/Culture/NingLiArmyTexasAuditPrimaryInspectionExact.agda
grep -q 'fy2006DisplayedAmount = "477"' DASHI/Culture/NingLiArmyTexasAuditPrimaryInspectionExact.agda
grep -q 'twoYearRecurrencePaysSameArmyObject = false' DASHI/Culture/NingLiArmyTexasAuditPrimaryInspectionExact.agda
grep -q 'twoYearRecurrenceWeakensPureOCRHypothesis = true' DASHI/Culture/NingLiArmyTexasAuditPrimaryInspectionExact.agda
grep -q 'NingLiArmyTexasAuditPrimaryInspectionExact' DASHI/Culture/MissingDeceasedInvestigativeAttributionEverything.agda
grep -q 'two-year Texas recurrence' DASHI/Culture/NingLiAdministrativeIdentifierCollisionParetoExact.agda

# FOIA procedural history must not be misread as a substantive no-records result.
grep -q 'foiaTrackingNumber = "23-F-0043"' DASHI/Culture/NingLiArmyFOIAProceduralHistoryExact.agda
grep -q 'administrativelyClosedForNoResponse = true' DASHI/Culture/NingLiArmyFOIAProceduralHistoryExact.agda
grep -q 'foiaClosurePaysNoRecordsFinding = false' DASHI/Culture/NingLiArmyFOIAProceduralHistoryExact.agda
grep -q 'reformulationWasExplicitlyInvited = true' DASHI/Culture/NingLiArmyFOIAProceduralHistoryExact.agda
grep -q 'NingLiArmyFOIAProceduralHistoryExact' DASHI/Culture/MissingDeceasedInvestigativeAttributionEverything.agda

# Primary/captured government request logs nominate response-package acquisitions.
grep -q 'dtic2019NingLiACGravityRequest' DASHI/Culture/NingLiGovernmentRequestLogSnowballExact.agda
grep -q 'fbi2021ACGravityRequest' DASHI/Culture/NingLiGovernmentRequestLogSnowballExact.agda
grep -q 'dodOIG2022ACGravityRequest' DASHI/Culture/NingLiGovernmentRequestLogSnowballExact.agda
grep -q 'fbiCaseNumber = "1499382-000"' DASHI/Culture/NingLiGovernmentRequestLogSnowballExact.agda
grep -q 'dodOIGCaseNumber = "DODOIG-2022-001077"' DASHI/Culture/NingLiGovernmentRequestLogSnowballExact.agda
grep -q 'requestLogPaysResponseContents = false' DASHI/Culture/NingLiGovernmentRequestLogSnowballExact.agda
grep -q 'NingLiGovernmentRequestLogSnowballExact' DASHI/Culture/MissingDeceasedInvestigativeAttributionEverything.agda

# Round-robin scientific cohort invariant: 11 U.S. + 9 Chinese scientists.
grep -q 'twentyScientistRoundProgress' DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinProgressExact.agda
grep -q 'scientificCohortCount = 20' DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinProgressExact.agda
grep -q 'usScientificCohortCount = 11' DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinProgressExact.agda
grep -q 'chineseScientificCohortCount = 9' DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinProgressExact.agda
grep -q 'everyRetainedScientistHasRoundTarget = true' DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinProgressExact.agda
grep -q 'roundTargetPaysLeaf = false' DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinProgressExact.agda
for name in \
  'Nuno F. G. Loureiro' 'Joshua Kyle LeBlanc' 'Frank W. Maiwald' \
  'Monica Jacinto / Monica Reza' 'Carl J. Grillmair' 'Michael David Hicks' \
  'William Neil McCasland' 'Anthony Chavez' 'Jason R. Thomas' 'Amy Eskridge' \
  'Ning Li' 'Chen Shuming' 'Feng Yanghe' 'Zhou Guangyuan' 'Liu Donghao' \
  'Zhang Xiaoxin' 'Zhang Daibing' 'Li Minyong' 'Fang Daining' 'Yan Hong'; do
  grep -q "$name" DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinProgressExact.agda
done
grep -q 'MissingDeceasedTwentyScientistRoundRobinProgressExact' DASHI/Culture/MissingDeceasedScientificWorkEverything.agda

# Second round must again touch all twenty scientists with fresh or retained residuals.
grep -q 'twentyScientistRound2Progress' DASHI/Culture/MissingDeceasedTwentyScientistRound2ProgressExact.agda
grep -q 'round2ScientificCohortCount = 20' DASHI/Culture/MissingDeceasedTwentyScientistRound2ProgressExact.agda
grep -q 'round2EveryScientistTouched = true' DASHI/Culture/MissingDeceasedTwentyScientistRound2ProgressExact.agda
grep -q 'round2PromotionRequiresSourceReceipt = true' DASHI/Culture/MissingDeceasedTwentyScientistRound2ProgressExact.agda
for name in \
  'Nuno F. G. Loureiro' 'Joshua Kyle LeBlanc' 'Frank W. Maiwald' \
  'Monica Jacinto / Monica Reza' 'Carl J. Grillmair' 'Michael David Hicks' \
  'William Neil McCasland' 'Anthony Chavez' 'Jason R. Thomas' 'Amy Eskridge' \
  'Ning Li' 'Chen Shuming' 'Feng Yanghe' 'Zhou Guangyuan' 'Liu Donghao' \
  'Zhang Xiaoxin' 'Zhang Daibing' 'Li Minyong' 'Fang Daining' 'Yan Hong'; do
  grep -q "$name" DASHI/Culture/MissingDeceasedTwentyScientistRound2ProgressExact.agda
done
grep -q 'MissingDeceasedTwentyScientistRound2ProgressExact' DASHI/Culture/MissingDeceasedScientificWorkEverything.agda

grep -q 'armyCommercialTransfer' DASHI/Culture/MissingDeceasedUAPAdversarialClaimDiscriminatorExact.agda
grep -q 'engineeringStackConvergence' DASHI/Culture/MissingDeceasedUAPAdversarialClaimDiscriminatorExact.agda
grep -q 'informationPoisoning' DASHI/Culture/MissingDeceasedUAPAdversarialClaimDiscriminatorExact.agda
grep -q 'declassificationAcclimatisation' DASHI/Culture/MissingDeceasedUAPAdversarialClaimDiscriminatorExact.agda
grep -q 'timeCrystalPropulsion' DASHI/Culture/MissingDeceasedUAPAdversarialClaimDiscriminatorExact.agda
grep -q 'qetScaleUp' DASHI/Culture/MissingDeceasedUAPAdversarialClaimDiscriminatorExact.agda
grep -q 'wormholeScaleUp' DASHI/Culture/MissingDeceasedUAPAdversarialClaimDiscriminatorExact.agda
grep -q 'anomalousMaterialSample' DASHI/Culture/MissingDeceasedUAPAdversarialClaimDiscriminatorExact.agda
grep -q 'counterEspionageSweep' DASHI/Culture/MissingDeceasedUAPAdversarialClaimDiscriminatorExact.agda
grep -q 'timeCrystalDoesNotCreatePropulsion = true' DASHI/Culture/MissingDeceasedUAPAdversarialClaimDiscriminatorExact.agda
grep -q 'qetDoesNotCreateVacuumThrust = true' DASHI/Culture/MissingDeceasedUAPAdversarialClaimDiscriminatorExact.agda
grep -q 'wormholeSimulationDoesNotCreateTraversableSpacetime = true' DASHI/Culture/MissingDeceasedUAPAdversarialClaimDiscriminatorExact.agda
grep -q 'technicalAdjacencyDoesNotCreateEngineeringStack = true' DASHI/Culture/MissingDeceasedUAPAdversarialClaimDiscriminatorExact.agda

# Dynamic YBCO regime between the 1997 static constraint and later programme work.
grep -q 'ntrs19990019627' DASHI/Physics/ExoticGravity/NingLiYBCORotatingFieldConstraintExact.agda
grep -q 'AIAA-98-3139' DASHI/Physics/ExoticGravity/NingLiYBCORotatingFieldConstraintExact.agda
grep -q 'rotatingFieldPaysPositiveGravityEffect = false' DASHI/Physics/ExoticGravity/NingLiYBCORotatingFieldConstraintExact.agda
grep -q 'NingLiYBCORotatingFieldConstraintExact' DASHI/Culture/MissingDeceasedScientificWorkEverything.agda

grep -q 'attachmentCompletionPareto' DASHI/Culture/MissingDeceasedIbrahimInvestigativeParetoUAPChineseExact.agda
grep -q 'MissingDeceasedFullAttachmentClaimAtlasExact' DASHI/Culture/MissingDeceasedScientificWorkEverything.agda
grep -q 'MissingDeceasedAttachmentSourcePromotionLedgerExact' DASHI/Culture/MissingDeceasedScientificWorkEverything.agda

grep -q 'LiTorrPRB1992AttributedSourceExact' DASHI/Culture/MissingDeceasedScientificWorkEverything.agda
grep -q 'MissingDeceasedInvestigativeDiscoveryLinksAExact' DASHI/Culture/MissingDeceasedScientificWorkEverything.agda
grep -q 'MissingDeceasedInvestigativeDiscoveryLinksBExact' DASHI/Culture/MissingDeceasedScientificWorkEverything.agda
grep -q 'MissingDeceasedInvestigativeDiscoveryLinksCExact' DASHI/Culture/MissingDeceasedScientificWorkEverything.agda

echo 'missing/deceased attribution-link static check: ok'
