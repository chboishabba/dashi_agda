#!/usr/bin/env bash
set -euo pipefail

# Focused static contract for the missing/deceased UAP + Chinese strategic lane.
# Source integration only; this script is not a substitute for Agda/kernel CI.

grep -q 'data ObserverPolarity' DASHI/Culture/MissingDeceasedTernaryAdversarialObserverExact.agda
grep -q 'polaritySwapInvolution' DASHI/Culture/MissingDeceasedTernaryAdversarialObserverExact.agda
grep -q 'identityObserverMapsToZero' DASHI/Culture/MissingDeceasedTernaryAdversarialObserverExact.agda

grep -q 'record RoleCapabilityFibre' DASHI/Culture/MissingDeceasedStrategicRoleCapabilityFibreExact.agda
grep -q 'managerMayExceedScientistOnProgrammeCoordination' DASHI/Culture/MissingDeceasedStrategicRoleCapabilityFibreExact.agda
grep -q 'roleLabelDoesNotDetermineCapability' DASHI/Culture/MissingDeceasedStrategicRoleCapabilityFibreExact.agda

grep -q 'chenShuming' DASHI/Culture/ChineseStrategicScientistRosterSnowballExact.agda
grep -q 'zhangDaibing' DASHI/Culture/ChineseStrategicScientistRosterSnowballExact.agda
grep -q 'fangDaining' DASHI/Culture/ChineseStrategicScientistRosterSnowballExact.agda
grep -q 'yanHong' DASHI/Culture/ChineseStrategicScientistRosterSnowballExact.agda
grep -q 'ninthNamedCaseDoesNotCreateTenth' DASHI/Culture/ChineseStrategicScientistRosterSnowballExact.agda
grep -q 'record RosterCardinalityClaim' DASHI/Culture/ChineseStrategicScientistRosterSnowballExact.agda
grep -q 'newsNationAtLeastTenClaim' DASHI/Culture/ChineseStrategicScientistRosterSnowballExact.agda
grep -q 'enumeratedNineClaim' DASHI/Culture/ChineseStrategicScientistRosterSnowballExact.agda
grep -q 'tenthIdentityUnresolved' DASHI/Culture/ChineseStrategicScientistRosterSnowballExact.agda

grep -q 'ActiveMechanicalMetamaterialScience' DASHI/Physics/Materials/FangDainingActiveMechanicalMetamaterialBidiExact.agda
grep -q 'phaseTransition' DASHI/Physics/Materials/FangDainingActiveMechanicalMetamaterialBidiExact.agda
grep -q 'metamaterialMeansExtraterrestrialMaterial' DASHI/Physics/Materials/FangDainingActiveMechanicalMetamaterialBidiExact.agda

grep -q 'MaterialObjectClass' DASHI/Physics/Materials/RezaFangAlloyMetamaterialDiscriminationExact.agda
grep -q 'mondaloyMetamaterialBridge' DASHI/Physics/Materials/RezaFangAlloyMetamaterialDiscriminationExact.agda
grep -q 'alloyPropertyDoesNotImplyMetamaterial' DASHI/Physics/Materials/RezaFangAlloyMetamaterialDiscriminationExact.agda

grep -q 'warSkullIIReceipt' DASHI/GameTheory/FengYangheMilitaryAIGameStatisticsBidiExact.agda
grep -q 'bayesianClassificationReceipt' DASHI/GameTheory/FengYangheMilitaryAIGameStatisticsBidiExact.agda
grep -q 'noisyLabelClassificationReceipt' DASHI/GameTheory/FengYangheMilitaryAIGameStatisticsBidiExact.agda

grep -q 'mondaloyToMetamaterialBridgeUnpaid' DASHI/Culture/MissingDeceasedUAPAdversarialClaimDiscriminatorExact.agda
grep -q 'zeroPointSuppressionIsNotVacuumThrust' DASHI/Culture/MissingDeceasedUAPAdversarialClaimDiscriminatorExact.agda
grep -q 'houseInquiryDoesNotPayCommonCause' DASHI/Culture/MissingDeceasedUAPAdversarialClaimDiscriminatorExact.agda
grep -q 'existingAlloyMetamaterialBoundary' DASHI/Culture/MissingDeceasedUAPAdversarialClaimDiscriminatorExact.agda

grep -q 'existingStrategicBoundary' DASHI/Culture/MissingDeceasedGameTheoryParetoProofSearchCrossPollinationExact.agda
grep -q 'existingEnrichmentBoundary' DASHI/Culture/MissingDeceasedGameTheoryParetoProofSearchCrossPollinationExact.agda
grep -q 'existingParetoBoundary' DASHI/Culture/MissingDeceasedGameTheoryParetoProofSearchCrossPollinationExact.agda
grep -q 'existingProofSearchParetoBoundary' DASHI/Culture/MissingDeceasedGameTheoryParetoProofSearchCrossPollinationExact.agda
grep -q 'gamePayoffDoesNotBecomeEvidence' DASHI/Culture/MissingDeceasedGameTheoryParetoProofSearchCrossPollinationExact.agda

grep -q 'Chinese strategic scientist acquisition' DASHI/Culture/MissingDeceasedIbrahimInvestigativeParetoUAPChineseExact.agda
grep -q 'UAP/adversarial discriminator' DASHI/Culture/MissingDeceasedIbrahimInvestigativeParetoUAPChineseExact.agda
grep -q 'Chinese roster-cardinality resolution' DASHI/Culture/MissingDeceasedIbrahimInvestigativeParetoUAPChineseExact.agda

grep -q 'MissingDeceasedTernaryAdversarialObserverExact' DASHI/Culture/MissingDeceasedScientificWorkEverything.agda
grep -q 'ChineseStrategicScientistRosterSnowballExact' DASHI/Culture/MissingDeceasedScientificWorkEverything.agda
grep -q 'MissingDeceasedGameTheoryParetoProofSearchCrossPollinationExact' DASHI/Culture/MissingDeceasedScientificWorkEverything.agda
grep -q 'FangDainingActiveMechanicalMetamaterialBidiExact' DASHI/Culture/MissingDeceasedScientificWorkEverything.agda
grep -q 'RezaFangAlloyMetamaterialDiscriminationExact' DASHI/Culture/MissingDeceasedScientificWorkEverything.agda
grep -q 'FengYangheMilitaryAIGameStatisticsBidiExact' DASHI/Culture/MissingDeceasedScientificWorkEverything.agda
grep -q 'FengYangheMilitaryAIGameStatisticsBidiExact' DASHI/GameTheory/Everything.agda

echo 'missing/deceased UAP Chinese strategic static check: ok'
