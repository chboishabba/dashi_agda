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
