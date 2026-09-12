#!/usr/bin/env bash
set -euo pipefail
TARGET='DASHI/Culture/MissingDeceasedTwentyScientistScienceImplementationCoverageExact.agda'

grep -q 'data ScienceImplementationDepth' "$TARGET"
grep -q 'twentyScientistScienceImplementationCoverage' "$TARGET"
grep -q 'scienceImplementationCoverageCount = 20' "$TARGET"
grep -q 'allTwentyHaveDomainOwner = true' "$TARGET"
grep -q 'typedMechanismDoesNotEqualExecutableWitness = true' "$TARGET"
grep -q 'sourceAttributionDoesNotEqualMechanismProof = true' "$TARGET"
for name in \
  'Nuno F. G. Loureiro' 'Joshua Kyle LeBlanc' 'Frank W. Maiwald' \
  'Monica Jacinto / Monica Reza' 'Carl J. Grillmair' 'Michael David Hicks' \
  'William Neil McCasland' 'Anthony Chavez' 'Jason R. Thomas' 'Amy Eskridge' \
  'Ning Li' 'Chen Shuming' 'Feng Yanghe' 'Zhou Guangyuan' 'Liu Donghao' \
  'Zhang Xiaoxin' 'Zhang Daibing' 'Li Minyong' 'Fang Daining' 'Yan Hong'; do
  grep -q "$name" "$TARGET"
done

echo 'twenty-scientist science depth coverage static check: ok'
