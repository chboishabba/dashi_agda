#!/usr/bin/env bash
set -euo pipefail

FILES=(
  DASHI/Cognition/PNF/RuntimeThroughputConstitution.agda
  DASHI/Cognition/PNF/SensibLawWorkerScalingRegression.agda
  DASHI/Cognition/PNF/SensibLawProductionScaleAcceptanceExact.agda
  DASHI/Cognition/PNF/SensibLawProductionScaleAcceptanceRegression.agda
  DASHI/Cognition/PNF/SensibLawSemanticBidiCampaignEverything.agda
)

for file in "${FILES[@]}"; do
  [[ -f "$file" ]] || { echo "missing SCALE-1.W Agda source: $file" >&2; exit 1; }
  if grep -nE '\b(postulate|{-# *TERMINATING *#}|{-# *NON_TERMINATING *#})\b' "$file"; then
    echo "forbidden proof escape found in $file" >&2
    exit 1
  fi
done

agda DASHI/Cognition/PNF/RuntimeThroughputConstitution.agda
agda DASHI/Cognition/PNF/SensibLawWorkerScalingRegression.agda
agda DASHI/Cognition/PNF/SensibLawProductionScaleAcceptanceExact.agda
agda DASHI/Cognition/PNF/SensibLawProductionScaleAcceptanceRegression.agda
agda DASHI/Cognition/PNF/SensibLawSemanticBidiCampaignEverything.agda

grep -q 'record WorkerScalePoint'   DASHI/Cognition/PNF/RuntimeThroughputConstitution.agda
grep -q 'record WorkerScalingReceipt'   DASHI/Cognition/PNF/RuntimeThroughputConstitution.agda
grep -q 'singleWorkerCountIsOne'   DASHI/Cognition/PNF/RuntimeThroughputConstitution.agda
grep -q 'parallelWorkerCountIsAtLeastTwo'   DASHI/Cognition/PNF/RuntimeThroughputConstitution.agda
grep -q 'workerScalingReceiptDoesNotCreateSemanticAuthority'   DASHI/Cognition/PNF/RuntimeThroughputConstitution.agda
grep -q 'fixtureBaselineIsOneWorker'   DASHI/Cognition/PNF/SensibLawWorkerScalingRegression.agda
grep -q 'fixtureParallelPointIsFourWorkers'   DASHI/Cognition/PNF/SensibLawWorkerScalingRegression.agda
grep -q 'parallelObservationUsesMoreThanOneWorker'   DASHI/Cognition/PNF/SensibLawProductionScaleAcceptanceExact.agda
grep -q 'declaredWorkPerCarrierBudgetMet'   DASHI/Cognition/PNF/SensibLawProductionScaleAcceptanceExact.agda
grep -q 'declaredMinimumSpanRatioMet'   DASHI/Cognition/PNF/SensibLawProductionScaleAcceptanceExact.agda
grep -q 'baselineOnlyDoesNotProveWorkerScaling'   DASHI/Cognition/PNF/SensibLawSemanticBidiCampaignEverything.agda
grep -q 'workerScalingReceiptCannotCreateSemanticAuthority'   DASHI/Cognition/PNF/SensibLawSemanticBidiCampaignEverything.agda

echo 'SCALE-1.W worker/archive throughput Agda checks passed'
