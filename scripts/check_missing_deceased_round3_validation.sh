#!/usr/bin/env bash
set -euo pipefail

# Round-3 all-scientist static contract. This is not Agda/kernel CI.

TARGET='DASHI/Culture/MissingDeceasedTwentyScientistRound3ProgressExact.agda'
AGG='DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinEverything.agda'

grep -q 'twentyScientistRound3Progress' "$TARGET"
grep -q 'round3ScientificCohortCount = 20' "$TARGET"
grep -q 'round3EveryScientistTouched = true' "$TARGET"
grep -q 'round3PromotionRequiresSourceReceipt = true' "$TARGET"
grep -q 'round3SearchResidualCreatesKnownAbsence = false' "$TARGET"

for name in \
  'Nuno F. G. Loureiro' 'Joshua Kyle LeBlanc' 'Frank W. Maiwald' \
  'Monica Jacinto / Monica Reza' 'Carl J. Grillmair' 'Michael David Hicks' \
  'William Neil McCasland' 'Anthony Chavez' 'Jason R. Thomas' 'Amy Eskridge' \
  'Ning Li' 'Chen Shuming' 'Feng Yanghe' 'Zhou Guangyuan' 'Liu Donghao' \
  'Zhang Xiaoxin' 'Zhang Daibing' 'Li Minyong' 'Fang Daining' 'Yan Hong'; do
  grep -q "$name" "$TARGET"
done

grep -q 'MissingDeceasedTwentyScientistRoundRobinProgressExact' "$AGG"
grep -q 'MissingDeceasedTwentyScientistRound2ProgressExact' "$AGG"
grep -q 'MissingDeceasedTwentyScientistRound3ProgressExact' "$AGG"

echo 'missing/deceased round-3 static check: ok'
