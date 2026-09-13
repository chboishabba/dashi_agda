#!/usr/bin/env bash
set -euo pipefail
root="${1:-.}"

required=(
  "$root/DASHI/Core/ScientificOperatorFamilyExact.agda"
  "$root/DASHI/Culture/MissingDeceasedWeakSignalInverseInferenceOperatorExact.agda"
  "$root/DASHI/Culture/MissingDeceasedResilientControlOperatorExact.agda"
  "$root/DASHI/Culture/MissingDeceasedMaterialsProcessOperatorExact.agda"
  "$root/DASHI/Culture/MissingDeceasedMolecularMeasurementOperatorExact.agda"
  "$root/DASHI/Culture/MissingDeceasedFieldComparatorOperatorExact.agda"
  "$root/DASHI/Culture/MissingDeceasedClassificationEvidenceOperatorExact.agda"
  "$root/DASHI/Culture/MissingDeceasedTwentyScientistScientificOperatorFactorisationExact.agda"
  "$root/DASHI/Culture/MissingDeceasedTwentyScientistScientificOperatorBidiExact.agda"
  "$root/DASHI/Culture/MissingDeceasedTwentyScientistRound14OperatorFactorisationProgressExact.agda"
)
for f in "${required[@]}"; do test -f "$f"; done

core="$root/DASHI/Core/ScientificOperatorFamilyExact.agda"
grep -q 'weakSignalInverseInference' "$core"
grep -q 'resilientSensingControlVerification' "$core"
grep -q 'materialsProcessStructureProperty' "$core"
grep -q 'molecularSpectroscopyChemicalBiology' "$core"
grep -q 'fieldPlasmaPrecisionForceDiscrimination' "$core"
grep -q 'classificationEvidenceGovernance' "$core"
grep -q 'familySharingImpliesSameMechanism = false' "$core"
grep -q 'familySharingImpliesCollaboration = false' "$core"

ledger="$root/DASHI/Culture/MissingDeceasedTwentyScientistScientificOperatorFactorisationExact.agda"
grep -q 'scientificOperatorFactorisationCount = 20' "$ledger"
grep -q 'paidScienceFactorisationCount = 18' "$ledger"
grep -q 'gatedScienceFactorisationCount = 2' "$ledger"
grep -q 'everyScientistRepresented = true' "$ledger"
grep -q 'Anthony Chavez' "$ledger"
grep -q 'Amy Eskridge' "$ledger"

bidi="$root/DASHI/Culture/MissingDeceasedTwentyScientistScientificOperatorBidiExact.agda"
grep -q 'operatorBidiDoesNotPayHistoricalDeployment = false' "$bidi"
grep -q 'operatorBidiDoesNotPayPersonPossession = false' "$bidi"
grep -q 'operatorBidiDoesNotPayCustody = false' "$bidi"
grep -q 'operatorBidiDoesNotPayEventCause = false' "$bidi"

round="$root/DASHI/Culture/MissingDeceasedTwentyScientistRound14OperatorFactorisationProgressExact.agda"
grep -q 'round14ScientificCohortCount = 20' "$round"
grep -q 'round14PaidFactorisationCount = 18' "$round"
grep -q 'round14GatedFactorisationCount = 2' "$round"
grep -q 'round14EveryScientistTouched = true' "$round"

aggregate="$root/DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinEverything.agda"
grep -q 'ScientificOperatorFamilyExact' "$aggregate"
grep -q 'MissingDeceasedTwentyScientistScientificOperatorFactorisationExact' "$aggregate"
grep -q 'MissingDeceasedTwentyScientistScientificOperatorBidiExact' "$aggregate"
grep -q 'MissingDeceasedTwentyScientistRound14OperatorFactorisationProgressExact' "$aggregate"

echo 'Round-14 scientific operator factorisation static contract: OK'
