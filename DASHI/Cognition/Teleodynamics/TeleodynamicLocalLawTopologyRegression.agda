module DASHI.Cognition.Teleodynamics.TeleodynamicLocalLawTopologyRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.Teleodynamics.TeleodynamicLocalLawTopologyFactorisationExact as F

_ : F.sameTopologyDifferentLocalLawCanChangeFuture F.canonicalBoundary ≡ true
_ = refl

_ : F.topologyDeterminesLocalTransitionByDefinition F.canonicalBoundary ≡ false
_ = refl

_ : F.sameArchitectureSimilarityDeterminesLocalLaw F.canonicalBoundary ≡ false
_ = refl

_ : F.iitMatchedGateScanReportedInSibling F.canonicalBoundary ≡ true
_ = refl

_ : F.xorOrSameTopologyDifferentFuture
_ = F.xorOrCounterexample
