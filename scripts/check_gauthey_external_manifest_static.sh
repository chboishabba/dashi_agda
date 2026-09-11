#!/usr/bin/env bash
set -euo pipefail

FILE="DASHI/Biology/DrosophilaGautheyExternalManifestHashBidiExact.agda"
[[ -f "$FILE" ]] || { echo "missing $FILE" >&2; exit 1; }

grep -q '55570f4ad028bfd19ab63d5b9b13430803cb277c' "$FILE"
grep -q 'f34fe193f0507b5ad7f3c05d6b8973c04a34cf02' "$FILE"
grep -q '39a4ae6739b9e13040b971469616e908df41f502' "$FILE"
grep -q '436b785a2c33b12968c5645ff0118f4e5493cf10' "$FILE"
grep -q '57a3052ba0a9b3503a04a6c50de5255fadcd4d19' "$FILE"
grep -q '10.34770/s5hx-1x75' "$FILE"
grep -q 'codeManifestPaid = true' "$FILE"
grep -q 'trialBytesPaid = false' "$FILE"
grep -q 'compactCarrierBytesPaid = false' "$FILE"

echo "Gauthey external manifest static contract: PASS"
