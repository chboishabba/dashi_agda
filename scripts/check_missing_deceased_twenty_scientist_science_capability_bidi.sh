#!/usr/bin/env bash
set -euo pipefail

TARGET='DASHI/Culture/MissingDeceasedTwentyScientistScienceCapabilityBidiExact.agda'
AGG='DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinEverything.agda'

# Core BIDI surface.
grep -q 'record ScientistTechnologyFibre' "$TARGET"
grep -q 'data ApplicationClaimStrength' "$TARGET"
grep -q 'sourceBackedIntended' "$TARGET"
grep -q 'crossDomainCandidate' "$TARGET"
grep -q 'record BidiReverseObligation' "$TARGET"
grep -q 'twentyScientistScienceFibres' "$TARGET"
grep -q 'twentyScientistScienceFibreCount = 20' "$TARGET"
grep -q 'integratedTwentyScientistCapability' "$TARGET"
grep -q 'allTwentyFibresAreRepresented = true' "$TARGET"

# Historical/application promotion firewalls.
grep -q 'possibleApplicationImpliesHistoricalDeployment = false' "$TARGET"
grep -q 'technicalCompatibilityImpliesSameProgramme = false' "$TARGET"
grep -q 'integratedCapabilityImpliesRosterCollaboration = false' "$TARGET"
grep -q 'scienceCarrierImpliesPersonPossession = false' "$TARGET"
grep -q 'institutionContinuityImpliesExactCapabilityTransfer = false' "$TARGET"
grep -q 'applicationCandidateImpliesEventCause = false' "$TARGET"
grep -q 'allTwentyFibresPresentImpliesOneHistoricalSystem = false' "$TARGET"

# Every retained scientist must be represented in the integrated science surface.
for name in \
  'Nuno F. G. Loureiro' 'Joshua Kyle LeBlanc' 'Frank W. Maiwald' \
  'Monica Jacinto / Monica Reza' 'Carl J. Grillmair' 'Michael David Hicks' \
  'William Neil McCasland' 'Anthony Chavez' 'Jason R. Thomas' 'Amy Eskridge' \
  'Ning Li' 'Chen Shuming' 'Feng Yanghe' 'Zhou Guangyuan' 'Liu Donghao' \
  'Zhang Xiaoxin' 'Zhang Daibing' 'Li Minyong' 'Fang Daining' 'Yan Hong'; do
  grep -q "$name" "$TARGET"
done

# Science-specific identifiers from the paid/bounded Round-6 surface.
for id in \
  'arXiv:1505.02649' '10.13182/NPICHMIT25-46370' '10.1021/acs.jpca.4c03552' \
  'US20190032604A1' '10.3847/1538-4357/aa8872' 'NASA A89-54007' \
  '10.1038/ncb3053' '10.1016/S0921-4534(97)01462-7' '10.1155/2018/6398616' \
  '978-7-5673-0533-5' '10.1016/j.cej.2023.147642' 'GB/T 37988-2019' \
  '10.1029/2023SW003522' '10.11887/j.cn.201801023' '10.1002/med.22120' \
  '10.1016/j.jmps.2025.106144' '10.7638/kqdlxxb-2013.0102'; do
  grep -q "$id" "$TARGET"
done

# Aggregate wiring.
grep -q 'MissingDeceasedTwentyScientistScienceCapabilityBidiExact' "$AGG"

echo 'twenty-scientist science capability BIDI static check: ok'
