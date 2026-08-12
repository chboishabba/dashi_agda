#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

BASE_CHECKER="scripts/check_dynamic_mass_residual_round11.sh"
if [[ -x "$BASE_CHECKER" ]]; then
  "$BASE_CHECKER"
fi

FILES=(
  DASHI/Crypto/ChosenCiphertextObservationRefinementExact.agda
  DASHI/Crypto/CryptoUsageInvariantExact.agda
  DASHI/Crypto/XorReuseLeakExact.agda
  DASHI/Crypto/TopTenCryptoBlueTeamProfilesExact.agda
  DASHI/Crypto/TopTenCryptoObservationSurfacesExact.agda
  DASHI/Crypto/TopTenCryptoDependencyGraphExact.agda
  DASHI/Crypto/KEMStateContractExact.agda
  DASHI/Crypto/MLWEKeyStateResidualExact.agda
  DASHI/Crypto/PassiveEncapsulationFibreInvariantExact.agda
  DASHI/Crypto/PublicSecretFactorisationAttackExact.agda
  DASHI/Crypto/MLKEMSecurityDependencyGraphExact.agda
  DASHI/EverythingTerminalisationProvenanceSymmetryRound10.agda
)

for f in "${FILES[@]}"; do
  test -s "$f"
  if grep -nE '\b(postulate|{-# *OPTIONS +--allow-unsolved-metas|unsafe|primTrustMe)\b|\?|{!!}' "$f"; then
    echo "fail-closed scan rejected $f" >&2
    exit 1
  fi
done

grep -q 'refinementIsMonotone' DASHI/Crypto/ChosenCiphertextObservationRefinementExact.agda
grep -q 'samePublicFibreCannotBeSplitByPublicFactoredObservation' DASHI/Crypto/ChosenCiphertextObservationRefinementExact.agda
grep -q 'rightCandidateRejectedByLeftObservation' DASHI/Crypto/ChosenCiphertextObservationRefinementExact.agda
grep -q 'reuseContradictsUniqueness' DASHI/Crypto/CryptoUsageInvariantExact.agda
grep -q 'unauthenticatedChannelNotQKDReady' DASHI/Crypto/CryptoUsageInvariantExact.agda
grep -q 'sameKeystreamRevealsPlaintextRelation' DASHI/Crypto/XorReuseLeakExact.agda
grep -q 'allTenCount' DASHI/Crypto/TopTenCryptoBlueTeamProfilesExact.agda
grep -q 'allProfilesCount' DASHI/Crypto/TopTenCryptoBlueTeamProfilesExact.agda
grep -q 'mlKemIsKEMNotDirectEncryption' DASHI/Crypto/TopTenCryptoBlueTeamProfilesExact.agda
grep -q 'qkdIsDistributionNotDirectEncryption' DASHI/Crypto/TopTenCryptoBlueTeamProfilesExact.agda
grep -q 'coverageCount' DASHI/Crypto/TopTenCryptoObservationSurfacesExact.agda
grep -q 'rsaValidityOutcome' DASHI/Crypto/TopTenCryptoObservationSurfacesExact.agda
grep -q 'mlKemDownstream' DASHI/Crypto/TopTenCryptoObservationSurfacesExact.agda
grep -q 'qkdStatistics' DASHI/Crypto/TopTenCryptoObservationSurfacesExact.agda
grep -q 'kemBreakRefutesHPKE' DASHI/Crypto/TopTenCryptoDependencyGraphExact.agda
grep -q 'unauthenticatedBreakRefutesQKDComposite' DASHI/Crypto/TopTenCryptoDependencyGraphExact.agda
grep -q 'publicSecretFactorisationCutsAsymmetry' DASHI/Crypto/TopTenCryptoDependencyGraphExact.agda
grep -q 'GeneratedAgreementFailure' DASHI/Crypto/KEMStateContractExact.agda
grep -q 'trueSecretPassesResidualTest' DASHI/Crypto/MLWEKeyStateResidualExact.agda
grep -q 'samePublicKeySameHonestTranscript' DASHI/Crypto/PassiveEncapsulationFibreInvariantExact.agda
grep -q 'fibreSplitRefutesExactPublicRecovery' DASHI/Crypto/PublicSecretFactorisationAttackExact.agda
grep -q 'fibreSplitRefutesPublicSecretFactorisation' DASHI/Crypto/PublicSecretFactorisationAttackExact.agda
grep -q 'publicFactorisationBreaksNoRecovery' DASHI/Crypto/MLKEMSecurityDependencyGraphExact.agda

grep -q '10.6028/NIST.FIPS.197-upd1' DASHI/Crypto/TopTenCryptoBlueTeamProfilesExact.agda
grep -q '10.17487/RFC8439' DASHI/Crypto/TopTenCryptoBlueTeamProfilesExact.agda
grep -q '10.17487/RFC8017' DASHI/Crypto/TopTenCryptoBlueTeamProfilesExact.agda
grep -q '10.17487/RFC9180' DASHI/Crypto/TopTenCryptoBlueTeamProfilesExact.agda
grep -q '10.6028/NIST.FIPS.203' DASHI/Crypto/TopTenCryptoBlueTeamProfilesExact.agda

if command -v agda >/dev/null 2>&1; then
  agda -i . -i src DASHI/EverythingTerminalisationProvenanceSymmetryRound10.agda
else
  echo "agda unavailable: structural/fail-closed round-12 scan completed; no kernel-clean claim"
fi
