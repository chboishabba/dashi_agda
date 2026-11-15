module DASHI.Reasoning.AlbertF4TauCetiFormalDonorValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.AlbertF4TauCetiFormalDonorReceiptExact as Receipt

albertStackLocated :
  Receipt.Boundary.tauCetiAlbertStackLocated Receipt.canonicalBoundary ≡ true
albertStackLocated = refl

f4StackLocated :
  Receipt.Boundary.tauCetiCanonicalF4StackLocated Receipt.canonicalBoundary ≡ true
f4StackLocated = refl

sameObjectBridgeNotLocated :
  Receipt.Boundary.sameObjectAlbertToCanonicalF4BridgeLocated Receipt.canonicalBoundary ≡ false
sameObjectBridgeNotLocated = refl

authorityNotImported :
  Receipt.Boundary.externalFormalAuthorityImportedIntoAgda Receipt.canonicalBoundary ≡ false
authorityNotImported = refl
