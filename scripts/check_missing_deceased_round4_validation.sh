#!/usr/bin/env bash
set -euo pipefail

TARGET='DASHI/Culture/MissingDeceasedTwentyScientistRound4ProgressExact.agda'

grep -q 'twentyScientistRound4Progress' "$TARGET"
grep -q 'round4ScientificCohortCount = 20' "$TARGET"
grep -q 'round4EveryScientistTouched = true' "$TARGET"
grep -q 'round4PromotionRequiresSourceReceipt = true' "$TARGET"
grep -q 'round4SearchResidualCreatesKnownAbsence = false' "$TARGET"
grep -q 'round4StaleSurfacePaysSuccession = false' "$TARGET"
for name in \
  'Nuno F. G. Loureiro' 'Joshua Kyle LeBlanc' 'Frank W. Maiwald' \
  'Monica Jacinto / Monica Reza' 'Carl J. Grillmair' 'Michael David Hicks' \
  'William Neil McCasland' 'Anthony Chavez' 'Jason R. Thomas' 'Amy Eskridge' \
  'Ning Li' 'Chen Shuming' 'Feng Yanghe' 'Zhou Guangyuan' 'Liu Donghao' \
  'Zhang Xiaoxin' 'Zhang Daibing' 'Li Minyong' 'Fang Daining' 'Yan Hong'; do
  grep -q "$name" "$TARGET"
done
grep -q 'MissingDeceasedTwentyScientistRound4ProgressExact' DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinEverything.agda

echo 'missing/deceased round-4 static check: ok'
