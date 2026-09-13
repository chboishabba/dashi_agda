#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OWNER="$ROOT/DASHI/Biology/BioacousticSongEnergyExpenditureBidiExact.agda"
VALIDATION="$ROOT/DASHI/Biology/BioacousticFlyStateSpaceValidation.agda"
EVERYTHING="$ROOT/DASHI/Biology/AnimalexicEverything.agda"

[[ -f "$OWNER" ]]
grep -q 'realExperimentCostAndOutcomeModelsStillExternal' "$OWNER"
grep -q 'SI.Measurement SI.Power SI.centiScale' "$OWNER"
grep -q 'SI.Energy' "$OWNER"
grep -q 'SI.joule' "$OWNER"
grep -q 'energeticCostDebt' "$OWNER"
grep -q 'wholeAnimalMetabolicPower' "$OWNER"
grep -q 'respiratorySyringealMechanicalProxy' "$OWNER"
grep -q 'acousticRadiatedEnergy' "$OWNER"
grep -q 'opportunityCost' "$OWNER"
grep -q 'dailyEnergyBudgetCost' "$OWNER"
grep -q '10.1242/jeb.204.19.3379' "$OWNER"
grep -q '10.1006/anbe.2003.2250' "$OWNER"
grep -q '10.1007/s00359-005-0022-4' "$OWNER"
grep -q '10.1371/journal.pone.0023198' "$OWNER"
grep -q 'BioacousticSongEnergyExpenditureBidiExact' "$VALIDATION"
grep -q 'BioacousticSongEnergyExpenditureBidiExact' "$EVERYTHING"

echo "bioacoustic song energy static contract: PASS"
