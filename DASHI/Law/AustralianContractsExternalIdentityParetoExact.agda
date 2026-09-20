module DASHI.Law.AustralianContractsExternalIdentityParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Interop.SLRWikidataTypedTraversalParetoExact as Wikidata
import DASHI.Law.AustralianContractsLegalFollowExact as Contracts

------------------------------------------------------------------------
-- AUSTRALIAN CONTRACTS SUPPLEMENTAL EXTERNAL IDENTITY / PARETO WELD
--
-- QID/canonical-URL work is a supplemental attribution sidecar.  It is not a
-- fifth legal frontier and never outranks a live primary-law residual merely
-- because a stable external identifier would be convenient.
------------------------------------------------------------------------

data ExternalIdentityLookupPriority : Set where
  notApplicable opportunistic worthChecking highValue :
    ExternalIdentityLookupPriority

data ExternalIdentityLikelihood : Set where
  likelihoodNotApplicable likelihoodLow likelihoodModerate likelihoodHigh :
    ExternalIdentityLikelihood

record ContractExternalIdentityWorkItem : Set where
  constructor contractExternalIdentityWorkItem
  field
    semanticReference : String
    wikidataQidPriority : ExternalIdentityLookupPriority
    canonicalUrlPriority : ExternalIdentityLookupPriority
    wikidataQidLikelihood : ExternalIdentityLikelihood
    lookupIsExistenceClaim : Bool
    lookupIsExistenceClaimIsFalse : lookupIsExistenceClaim ≡ false
    lookupCreatesLegalAuthority : Bool
    lookupCreatesLegalAuthorityIsFalse :
      lookupCreatesLegalAuthority ≡ false
    lookupCreatesApplicability : Bool
    lookupCreatesApplicabilityIsFalse :
      lookupCreatesApplicability ≡ false
    primarySourcePrecedesIdentityByDefault : Bool
    primarySourcePrecedesIdentityByDefaultIsTrue :
      primarySourcePrecedesIdentityByDefault ≡ true

open ContractExternalIdentityWorkItem public

waltonsExternalIdentityWork : ContractExternalIdentityWorkItem
waltonsExternalIdentityWork =
  contractExternalIdentityWorkItem
    "case:au:hca:1988:7"
    worthChecking
    highValue
    likelihoodHigh
    false refl
    false refl
    false refl
    true refl

ExternalIdentityPolicy : Set
ExternalIdentityPolicy = Identity.SnowballExternalIdentityPolicy

externalIdentityPolicyPaid : ExternalIdentityPolicy
externalIdentityPolicyPaid = Identity.canonicalExternalIdentityPolicy

AttributionBoundary : Set
AttributionBoundary = Attribution.AttributionSnowballBoundary

attributionBoundaryPaid : AttributionBoundary
attributionBoundaryPaid = Attribution.canonicalAttributionSnowballBoundary

WikidataTraversalBoundary : Set
WikidataTraversalBoundary = Wikidata.TypedTraversalBoundary

wikidataTraversalBoundaryPaid : WikidataTraversalBoundary
wikidataTraversalBoundaryPaid = Wikidata.canonicalTypedTraversalBoundary

data QidLikelihoodAutomaticallyMeansEntityExists : Set where
data OptionalQidWorkMayDisplaceLivePrimarySourceResidual : Set where
data QidCreatesLegalApplicability : Set where
data QidCreatesLegalAuthority : Set where
data UnresolvedQidIsNegativeLegalEvidence : Set where
data SupplementalIdentityBecomesFifthLegalFrontier : Set where

qidLikelihoodIsNotExistenceClaim :
  QidLikelihoodAutomaticallyMeansEntityExists → ⊥
qidLikelihoodIsNotExistenceClaim ()

optionalIdentityCannotDisplaceLivePrimarySource :
  OptionalQidWorkMayDisplaceLivePrimarySourceResidual → ⊥
optionalIdentityCannotDisplaceLivePrimarySource ()

qidDoesNotCreateApplicability :
  QidCreatesLegalApplicability → ⊥
qidDoesNotCreateApplicability ()

qidDoesNotCreateLegalAuthority :
  QidCreatesLegalAuthority → ⊥
qidDoesNotCreateLegalAuthority ()

unresolvedQidIsNotNegativeLegalEvidence :
  UnresolvedQidIsNegativeLegalEvidence → ⊥
unresolvedQidIsNotNegativeLegalEvidence ()

supplementalIdentityIsNotFifthLegalFrontier :
  SupplementalIdentityBecomesFifthLegalFrontier → ⊥
supplementalIdentityIsNotFifthLegalFrontier ()

record AustralianContractsExternalIdentityBoundary : Set where
  constructor australianContractsExternalIdentityBoundary
  field
    reusesSnowballExternalIdentityPolicy : Bool
    reusesSnowballExternalIdentityPolicyIsTrue :
      reusesSnowballExternalIdentityPolicy ≡ true
    reusesAttributionSnowball : Bool
    reusesAttributionSnowballIsTrue :
      reusesAttributionSnowball ≡ true
    reusesTypedWikidataParetoBoundary : Bool
    reusesTypedWikidataParetoBoundaryIsTrue :
      reusesTypedWikidataParetoBoundary ≡ true
    supplementalIdentityIsLegalFrontier : Bool
    supplementalIdentityIsLegalFrontierIsFalse :
      supplementalIdentityIsLegalFrontier ≡ false
    unresolvedIdentityIsNegativeEvidence : Bool
    unresolvedIdentityIsNegativeEvidenceIsFalse :
      unresolvedIdentityIsNegativeEvidence ≡ false
    qidLikelihoodIsExistenceClaim : Bool
    qidLikelihoodIsExistenceClaimIsFalse :
      qidLikelihoodIsExistenceClaim ≡ false
    primarySourcePrecedesOptionalIdentityByDefault : Bool
    primarySourcePrecedesOptionalIdentityByDefaultIsTrue :
      primarySourcePrecedesOptionalIdentityByDefault ≡ true
    qidCreatesLegalAuthority : Bool
    qidCreatesLegalAuthorityIsFalse :
      qidCreatesLegalAuthority ≡ false
    qidCreatesApplicability : Bool
    qidCreatesApplicabilityIsFalse :
      qidCreatesApplicability ≡ false

canonicalAustralianContractsExternalIdentityBoundary :
  AustralianContractsExternalIdentityBoundary
canonicalAustralianContractsExternalIdentityBoundary =
  australianContractsExternalIdentityBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    true refl
    false refl
    false refl
