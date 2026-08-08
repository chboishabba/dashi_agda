#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_ns_luo_physical_carrier_support_round25.sh

files=(
  DASHI/Physics/Closure/NSTriadKNLuoRealityTransversePhaseSpaceRound26Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteGalerkinPolynomialRound26Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoTriadwiseEnergyCancellationRound26Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoSignedCriticalLedgerRound26Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteKernelCommutatorRound26Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoLowTransportCommutatorRound26Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoDivisionFreeHHDefectRound26Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoHystereticPositiveVariationRound26Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoCriticalRemainderClassificationRound26Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteTaxAdversarialRegressionRound26Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoHighestAlphaRound26Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoGalerkinCriticalLedgerRound26Validation.agda
  DASHI/Papers/NavierStokes/GalerkinCriticalLedgerRound26.agda
  DASHI/Papers/NavierStokes/CurrentTheoremInterfaceRound26.agda
)

docs=(
  docs/ns-clay-contract/README.md
  docs/ns-clay-contract/architecture.puml
  docs/ns-clay-contract/galerkin-critical-ledger-round26.md
  docs/ns-clay-contract/paper-corpus/highest-alpha-lemma-ladder.md
)

scripts=(
  scripts/ns_round26_finite_tax_adversarial.py
)

workflow=.github/workflows/ns-luo-galerkin-critical-ledger-round26.yml

for file in "${files[@]}" "${docs[@]}" "${scripts[@]}" "$workflow"; do
  test -f "$file"
done

audit_targets=("${files[@]}" "${docs[@]}" "${scripts[@]}")

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|TODO|FIXME' "${audit_targets[@]}"; then
  echo "round twenty-six contains a hole, unsafe escape, trust primitive, or placeholder" >&2
  exit 1
fi

phase=DASHI/Physics/Closure/NSTriadKNLuoRealityTransversePhaseSpaceRound26Exact.agda
grep -q '10.1007/BF02547354' "$phase"
grep -q '10.1090/chel/343' "$phase"
grep -q 'TransverseModeCoefficient' "$phase"
grep -q 'reconstructedNegativeValue' "$phase"
grep -q 'ConjugateTransversalityLaw' "$phase"
grep -q 'reconstructedNegativeIsTransverse' "$phase"

polynomial=DASHI/Physics/Closure/NSTriadKNLuoFiniteGalerkinPolynomialRound26Exact.agda
grep -q 'GalerkinCoordinateAtom' "$polynomial"
grep -q 'atomDegreeAtMostTwo' "$polynomial"
grep -q 'atomDifferenceFactorisation' "$polynomial"
grep -q 'finiteGalerkinDifferenceFactorisation' "$polynomial"
grep -q 'Physical.PhysicalTriadIncidence' "$polynomial"

energy=DASHI/Physics/Closure/NSTriadKNLuoTriadwiseEnergyCancellationRound26Exact.agda
grep -q 'resonantTriadEnergyExchangeCyclicZero' "$energy"
grep -q 'aPairCancels' "$energy"
grep -q 'bPairCancels' "$energy"
grep -q 'cPairCancels' "$energy"
grep -q 'shellInternalTransferCancels' "$energy"

ledger=DASHI/Physics/Closure/NSTriadKNLuoSignedCriticalLedgerRound26Exact.agda
grep -q 'criticalVelocityVorticityWeightIdentity' "$ledger"
grep -q 'weightedShellBalance' "$ledger"
grep -q 'finiteSignedCriticalLedgerExact' "$ledger"
grep -q 'lowerBoundarySource upperBoundarySource' "$ledger"
grep -q 'MeanZeroHomogeneousCriticalCarrier' "$ledger"

kernel=DASHI/Physics/Closure/NSTriadKNLuoFiniteKernelCommutatorRound26Exact.agda
grep -q 'finiteKernelCommutatorCellIdentity' "$kernel"
grep -q 'finiteKernelCommutatorIdentity' "$kernel"
grep -q 'firstMomentScaleLaw' "$kernel"
grep -q 'dyadicFirstMomentInherited' "$kernel"

low=DASHI/Physics/Closure/NSTriadKNLuoLowTransportCommutatorRound26Exact.agda
grep -q 'LowAdvectsHigh' "$low"
grep -q 'principalLowTransportCancels' "$low"
grep -q 'survivingFiniteTermIsIncrementCommutator' "$low"
grep -q 'Set (lsuc ℓ)' "$low"

hh=DASHI/Physics/Closure/NSTriadKNLuoDivisionFreeHHDefectRound26Exact.agda
grep -q '10.1512/iumj.1993.42.42034' "$hh"
grep -q '10.48550/arXiv.2606.27560' "$hh"
grep -q 'divisionFreeHHProductIdentity' "$hh"
grep -q 'zeroDenominatorForcesZeroDefect' "$hh"
grep -q 'hhSquaredProductExact' "$hh"
if grep -qE '/[[:space:]]*denominator|denominator[[:space:]]*⁻¹' "$hh"; then
  echo "round twenty-six reintroduced division by the HH denominator" >&2
  exit 1
fi

hysteresis=DASHI/Physics/Closure/NSTriadKNLuoHystereticPositiveVariationRound26Exact.agda
grep -q '10.48550/arXiv.2606.25341' "$hysteresis"
grep -q 'entryGapPaidByRise' "$hysteresis"
grep -q 'hystereticEntryChargeBelowPositiveVariation' "$hysteresis"
grep -q 'allEntryChargesBelowVariationBudget' "$hysteresis"

ownership=DASHI/Physics/Closure/NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact.agda
grep -q 'HH-good HH-bad LH HL CC Com kernel tail boundary' "$ownership"
grep -q 'ownerUnique' "$ownership"
grep -q 'duplicateFreeTaxOwnershipExact' "$ownership"
grep -q 'OwnedViscosityCoefficients' "$ownership"
grep -q 'totalEta' "$ownership"

remainder=DASHI/Physics/Closure/NSTriadKNLuoCriticalRemainderClassificationRound26Exact.agda
grep -q 'dataControlled timeIntegrable smallRemainder telescoping' "$remainder"
grep -q 'remainderClassificationExact' "$remainder"
grep -q 'GronwallAdmissibleRemainder' "$remainder"
grep -q 'gronwallRemainderHasDeclaredShape' "$remainder"

regression=DASHI/Physics/Closure/NSTriadKNLuoFiniteTaxAdversarialRegressionRound26Exact.agda
grep -q 'signedCancellationExample' "$regression"
grep -q 'magnitudeTaxAfterEarlyAbsoluteValue' "$regression"
grep -q 'duplicateOwnershipDoublesUnitAtom' "$regression"
grep -q 'zeroBudgetIsZero' "$regression"

integration=DASHI/Physics/Closure/NSTriadKNLuoHighestAlphaRound26Exact.agda
grep -q 'Round26ExactEvidence' "$integration"
grep -q 'hystereticEntriesPaidByPositiveVariation' "$integration"
grep -q 'namedRemaindersRecomposeExactly' "$integration"
grep -q 'localODEStillOpen' "$integration"
grep -q 'uniformTaxesStillOpen' "$integration"
grep -q 'strictMarginStillOpen' "$integration"
grep -q 'clayPromotionStillFalse' "$integration"

paper=DASHI/Papers/NavierStokes/GalerkinCriticalLedgerRound26.agda
grep -q 'canonicalGalerkinCriticalLedgerRound26Status' "$paper"
grep -q 'finiteAlgebraAdvanced' "$paper"
grep -q 'taxOwnershipAdvanced' "$paper"
grep -q 'localODEInstanceRemainsOpen' "$paper"
grep -q 'uniformTaxRemainsOpen' "$paper"
grep -q 'strictMarginRemainsOpen' "$paper"
grep -q 'clayPromotionRemainsFalse' "$paper"

current=DASHI/Papers/NavierStokes/CurrentTheoremInterfaceRound26.agda
grep -q 'canonicalCurrentNSPaperTheoremInterfaceRound26' "$current"
grep -q 'currentRound26TaxOwnershipChecked' "$current"
grep -q 'currentRound26ClayPromotionFalse' "$current"

grep -q '\[finite Galerkin and critical-tax tranche\](galerkin-critical-ledger-round26.md)' docs/ns-clay-contract/README.md
grep -q '\[Round 26 finite Galerkin and critical-tax ledger\](galerkin-critical-ledger-round26.md)' docs/ns-clay-contract/README.md
grep -q '\[Back to the Clay-contract overview\](README.md)' docs/ns-clay-contract/galerkin-critical-ledger-round26.md
grep -q 'Duplicate-free tax ownership' docs/ns-clay-contract/galerkin-critical-ledger-round26.md
grep -q 'L7 — Duplicate-free physical tax ledger' docs/ns-clay-contract/paper-corpus/highest-alpha-lemma-ladder.md
grep -q 'Strict unique-owner viscosity certificate' docs/ns-clay-contract/architecture.puml

grep -q 'agent/ns-luo-galerkin-critical-ledger-round26' "$workflow"
grep -q 'check_ns_luo_galerkin_critical_ledger_round26.sh' "$workflow"
grep -q 'ns-round26-finite-regression.json' "$workflow"
grep -q 'ns-round26-critical-ledger-agda' "$workflow"

python3 scripts/ns_round26_finite_tax_adversarial.py \
  --radius 2 \
  --out ns-round26-finite-regression.json

python3 - <<'PY'
import json
from pathlib import Path
payload = json.loads(Path('ns-round26-finite-regression.json').read_text())
assert payload['all_checks_passed'] is True
assert payload['signed_cancellation_examples'] > 0
assert payload['duplicate_ownership_examples'] > 0
assert payload['commutator_cells_checked'] > 0
assert payload['triad_energy_cells_checked'] > 0
PY

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoGalerkinCriticalLedgerRound26Validation.agda
