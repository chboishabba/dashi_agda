#!/usr/bin/env bash
set -euo pipefail

root="${1:-.}"
acq="$root/DASHI/Culture/MissingDeceasedPrimaryObjectAcquisitionExact.agda"
round21="$root/DASHI/Culture/MissingDeceasedTwentyScientistRound21PrimaryObjectAcquisitionExact.agda"
agg="$root/DASHI/Culture/MissingDeceasedCommonObjectProgrammeEverything.agda"

test -f "$acq"
test -f "$round21"
test -f "$agg"

grep -q 'data AcquisitionStatus' "$acq"
grep -q 'ningArmyOriginalRow' "$acq"
grep -q 'rezaMondaloy2020Procurement' "$acq"
grep -q 'mccaslandCommandChronology' "$acq"
grep -q 'amyNingHistoricalReference' "$acq"
grep -q 'primaryObjectIdentifierPaysCrossPersonH2 = false' "$acq"
grep -q 'laterProgrammePersistencePaysEarlierPersonalInvolvement = false' "$acq"
grep -q 'secondaryTranscriptionPaysPrimaryCustody = false' "$acq"
grep -q 'currentLiteralCrossPersonSameObjectCount = 0' "$acq"
grep -q 'currentPreEventOperationalLinkCount = 0' "$acq"

grep -q 'round21ScientificCohortCount = 20' "$round21"
grep -q 'round21EveryScientistTouched = true' "$round21"
grep -q 'round21H2PromotionCount = 0' "$round21"
grep -q 'round21H3PromotionCount = 0' "$round21"
grep -q 'round21PrimaryObjectAcquisitionDoesNotCreateCommonCause = false' "$round21"
grep -q 'round21SearchResidualCreatesKnownAbsence = false' "$round21"

for name in \
  'Nuno F. G. Loureiro' 'Joshua Kyle LeBlanc' 'Frank W. Maiwald' \
  'Monica Jacinto / Monica Reza' 'Carl J. Grillmair' 'Michael David Hicks' \
  'William Neil McCasland' 'Anthony Chavez' 'Jason R. Thomas' 'Amy Eskridge' \
  'Ning Li' 'Chen Shuming' 'Feng Yanghe' 'Zhou Guangyuan' 'Liu Donghao' \
  'Zhang Xiaoxin' 'Zhang Daibing' 'Li Minyong' 'Fang Daining' 'Yan Hong'; do
  grep -q "$name" "$round21"
done

grep -q 'MissingDeceasedPrimaryObjectAcquisitionExact' "$agg"
grep -q 'MissingDeceasedTwentyScientistRound21PrimaryObjectAcquisitionExact' "$agg"

echo 'Round21 primary-object acquisition static contract: OK'
