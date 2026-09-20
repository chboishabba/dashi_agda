module DASHI.Law.AustralianContractsExternalIdentityParetoRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Law.AustralianContractsExternalIdentityParetoExact as Identity

boundaryExists : Set
boundaryExists = Identity.AustralianContractsExternalIdentityBoundary

boundaryPaid : boundaryExists
boundaryPaid = Identity.canonicalAustralianContractsExternalIdentityBoundary

waltonsQidLikelihoodIsHigh :
  Identity.wikidataQidLikelihood Identity.waltonsExternalIdentityWork
    ≡ Identity.likelihoodHigh
waltonsQidLikelihoodIsHigh = refl

waltonsQidLikelihoodStillIsNotExistence :
  Identity.lookupIsExistenceClaim Identity.waltonsExternalIdentityWork
    ≡ false
waltonsQidLikelihoodStillIsNotExistence =
  Identity.lookupIsExistenceClaimIsFalse Identity.waltonsExternalIdentityWork

primarySourceStillPrecedesOptionalIdentity :
  Identity.primarySourcePrecedesOptionalIdentityByDefault
    Identity.canonicalAustralianContractsExternalIdentityBoundary
    ≡ true
primarySourceStillPrecedesOptionalIdentity =
  Identity.primarySourcePrecedesOptionalIdentityByDefaultIsTrue
    Identity.canonicalAustralianContractsExternalIdentityBoundary

supplementalIdentityStillIsNotLegalFrontier :
  Identity.supplementalIdentityIsLegalFrontier
    Identity.canonicalAustralianContractsExternalIdentityBoundary
    ≡ false
supplementalIdentityStillIsNotLegalFrontier =
  Identity.supplementalIdentityIsLegalFrontierIsFalse
    Identity.canonicalAustralianContractsExternalIdentityBoundary


verifiedWaltonsQidAttachmentRemainsSupplemental :
  Identity.supplementalOnly Identity.waltonsVerifiedQidAttachmentFixture
    ≡ true
verifiedWaltonsQidAttachmentRemainsSupplemental =
  Identity.supplementalOnlyIsTrue Identity.waltonsVerifiedQidAttachmentFixture

verifiedWaltonsQidAttachmentCreatesNoAuthority :
  Identity.createsLegalAuthority Identity.waltonsVerifiedQidAttachmentFixture
    ≡ false
verifiedWaltonsQidAttachmentCreatesNoAuthority =
  Identity.createsLegalAuthorityIsFalse Identity.waltonsVerifiedQidAttachmentFixture

externalIdentityStillRequiresExistingSemanticObject :
  Identity.externalIdentityAttachmentRequiresExistingSemanticObject
    Identity.canonicalAustralianContractsExternalIdentityBoundary
    ≡ true
externalIdentityStillRequiresExistingSemanticObject =
  Identity.externalIdentityAttachmentRequiresExistingSemanticObjectIsTrue
    Identity.canonicalAustralianContractsExternalIdentityBoundary

conflictingIdentityStillBecomesHardResidual :
  Identity.conflictingExternalIdentityIsHardResidual
    Identity.canonicalAustralianContractsExternalIdentityBoundary
    ≡ true
conflictingIdentityStillBecomesHardResidual =
  Identity.conflictingExternalIdentityIsHardResidualIsTrue
    Identity.canonicalAustralianContractsExternalIdentityBoundary
