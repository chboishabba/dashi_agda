module DASHI.Law.SensibLawSharedWorldAdversarialConsumerRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)

import DASHI.Interop.SharedUserWorldConsumerRuntimeExact as Shared
import DASHI.Law.SensibLawSharedWorldAdversarialConsumerExact as Legal

maboAuthorityCoordinate : Shared.SharedWorldCoordinate
maboAuthorityCoordinate =
  Shared.shared-world-coordinate
    "world:authority:mabo-1992-hca-23"
    Shared.authorityCoordinate
    Shared.legalSource
    "source:primary:mabo-1992-hca-23"
    "revision:pinned:mabo"
    "prov:mabo-authority"
    Shared.explicitlyReviewed
    "context:AU-HCA-1992"
    "scope:legal-research"
    false refl
    false refl

pabaiConsumer : Shared.ConsumerDependencySlice
pabaiConsumer =
  Shared.consumer-dependency-slice
    "consumer:pabai:duty"
    Shared.legalProofConsumer
    ("world:authority:mabo-1992-hca-23" ∷ [])
    "scope:legal-research"
    "query:pabai-duty"
    "slice:pabai"

maboLookupForPabai : Shared.SharedWorldLookupReceipt
maboLookupForPabai =
  Shared.shared-world-lookup-receipt
    pabaiConsumer
    maboAuthorityCoordinate
    true
    true
    true
    Shared.reuseAlreadyPaid
    refl
    "lookup:pabai:mabo"

maboStructuralAnalogyStillNeedsPabaiAuthorityPayment :
  Legal.decideLegalReuse Shared.reuseAlreadyPaid true false
  ≡ Legal.authorityPaymentRequired
maboStructuralAnalogyStillNeedsPabaiAuthorityPayment = refl

wrongLegalTypeReopensExactResidual :
  Legal.decideLegalReuse Shared.reuseAlreadyPaid false true
  ≡ Legal.wrongTypeRequiresResidual
wrongLegalTypeReopensExactResidual = refl

scopedOutPrivateCoordinateCannotPayLegalConsumer :
  Legal.decideLegalReuse Shared.scopeBlocked true true
  ≡ Legal.legalScopeBlocked
scopedOutPrivateCoordinateCannotPayLegalConsumer = refl

reviewedExactLegalPrerequisiteMayBeReused :
  Legal.decideLegalReuse Shared.reuseAlreadyPaid true true
  ≡ Legal.reusableLegalPrerequisite
reviewedExactLegalPrerequisiteMayBeReused = refl

pabaiDefeaterRerunShape : Legal.AdversarialLegalRerunReceipt
pabaiDefeaterRerunShape =
  Legal.adversarial-legal-rerun-receipt
    "proposition:pabai:duty"
    Legal.routeReachable
    "delta:pabai:core-policy-defeater"
    Legal.routeDefeated
    Legal.counterAdversarialRepair
    true refl
    "rerun:pabai:defeater"
    false refl

counterDefeaterMayReopenWithoutBecomingCurrentLaw :
  Legal.LegalSearchDirection
counterDefeaterMayReopenWithoutBecomingCurrentLaw =
  Legal.counterAdversarialRepair
