module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseStructuralIdentitySnowballValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseStructuralIdentitySnowballExact as P

identityRegression :
  P.AdKStructuralIdentitySnowballBoundary.openPdbDoiRetained
    P.canonicalAdKStructuralIdentitySnowballBoundary
  ≡ true
  × P.AdKStructuralIdentitySnowballBoundary.closedPdbDoiRetained
    P.canonicalAdKStructuralIdentitySnowballBoundary
  ≡ true
  × P.AdKStructuralIdentitySnowballBoundary.uniprotIdentityRetained
    P.canonicalAdKStructuralIdentitySnowballBoundary
  ≡ true
  × P.AdKStructuralIdentitySnowballBoundary.adkQidRetained
    P.canonicalAdKStructuralIdentitySnowballBoundary
  ≡ true
identityRegression = refl , refl , refl , refl

unresolvedIdentityRegression :
  P.AdKStructuralIdentitySnowballBoundary.openPdbObjectQidResolved
    P.canonicalAdKStructuralIdentitySnowballBoundary
  ≡ false
  × P.AdKStructuralIdentitySnowballBoundary.closedPdbObjectQidResolved
    P.canonicalAdKStructuralIdentitySnowballBoundary
  ≡ false
  × P.AdKStructuralIdentitySnowballBoundary.primaryArticleQidsResolved
    P.canonicalAdKStructuralIdentitySnowballBoundary
  ≡ false
unresolvedIdentityRegression = refl , refl , refl

firewallRegression :
  P.AdKStructuralIdentitySnowballBoundary.pdbDoiCreatesDynamicMechanism
    P.canonicalAdKStructuralIdentitySnowballBoundary
  ≡ false
  × P.AdKStructuralIdentitySnowballBoundary.sharedUniProtImpliesSameExperimentalCondition
    P.canonicalAdKStructuralIdentitySnowballBoundary
  ≡ false
  × P.AdKStructuralIdentitySnowballBoundary.adkQidCreatesPdbObjectIdentity
    P.canonicalAdKStructuralIdentitySnowballBoundary
  ≡ false
firewallRegression = refl , refl , refl
