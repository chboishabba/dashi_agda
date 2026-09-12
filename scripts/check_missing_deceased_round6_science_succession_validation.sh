#!/usr/bin/env bash
set -euo pipefail

TARGET='DASHI/Culture/MissingDeceasedTwentyScientistRound6ScienceSuccessionExact.agda'

grep -q 'twentyScientistRound6Progress' "$TARGET"
grep -q 'round6ScientificCohortCount = 20' "$TARGET"
grep -q 'round6EveryScientistHasScienceKernel = true' "$TARGET"
grep -q 'round6EveryScientistHasScienceProofLeaf = true' "$TARGET"
grep -q 'round6EveryScientistHasSuccessionLeaf = true' "$TARGET"
grep -q 'round6ScienceAdjacencyCreatesCommonCause = false' "$TARGET"
grep -q 'round6InstitutionContinuityPaysExactCapabilityTransfer = false' "$TARGET"

for name in \
  'Nuno F. G. Loureiro' 'Joshua Kyle LeBlanc' 'Frank W. Maiwald' \
  'Monica Jacinto / Monica Reza' 'Carl J. Grillmair' 'Michael David Hicks' \
  'William Neil McCasland' 'Anthony Chavez' 'Jason R. Thomas' 'Amy Eskridge' \
  'Ning Li' 'Chen Shuming' 'Feng Yanghe' 'Zhou Guangyuan' 'Liu Donghao' \
  'Zhang Xiaoxin' 'Zhang Daibing' 'Li Minyong' 'Fang Daining' 'Yan Hong'; do
  grep -q "$name" "$TARGET"
done

grep -q 'MissingDeceasedTwentyScientistRound6ScienceSuccessionExact' DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinEverything.agda

echo 'missing/deceased round-6 science+succession static check: ok'
