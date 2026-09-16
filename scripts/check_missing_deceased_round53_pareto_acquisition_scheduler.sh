#!/usr/bin/env bash
set -euo pipefail

OWNER="DASHI/Culture/MissingDeceasedTwentyScientistRound53ParetoAcquisitionSchedulerExact.agda"

[ -f "$OWNER" ]
grep -q "AcquisitionTask" "$OWNER"
grep -q "SchedulerAxis" "$OWNER"
grep -q "promotionResidualAxis" "$OWNER"
grep -q "sourceOriginClosureAxis" "$OWNER"
grep -q "professionalGateClosureAxis" "$OWNER"
grep -q "acquisitionBurdenAxis" "$OWNER"
grep -q "schedulerProblem" "$OWNER"
grep -q "rezaMcCaslandTask" "$OWNER"
grep -q "ningPrimaryBytesTask" "$OWNER"
grep -q "amyReferentWeldTask" "$OWNER"
grep -q "chavezScorpiusCrossingTask" "$OWNER"
grep -q "chineseClusterOriginTask" "$OWNER"
grep -q "garciaRoleWeldTask" "$OWNER"
grep -q "paretoFrontierDoesNotCreateTruth" "$OWNER"
grep -q "dominatedInterestingResearchStaysOffCriticalPath" "$OWNER"
grep -q "scheduledAcquisitionMustBindToSelectedResidual" "$OWNER"
grep -q "round53H2PaidCount" "$OWNER"
grep -q "round53H3PaidCount" "$OWNER"
