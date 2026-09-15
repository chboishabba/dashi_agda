module DASHI.Wikimedia.IbrahimMonster369OEISLiteralCollisionPortfolioValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Wikimedia.IbrahimMonster369OEISLiteralCollisionPortfolioExact as P

boundary : P.Monster369LiteralCollisionPortfolioBoundary
boundary = P.canonicalMonster369LiteralCollisionPortfolioBoundary

literalWorldCountRegression : P.literalWorldCount boundary ≡ 11
literalWorldCountRegression = refl

literalCollisionEdgeCountRegression : P.literalCollisionEdgeCount boundary ≡ 11
literalCollisionEdgeCountRegression = refl

sameIntegerRolesRetainedRegression :
  P.sameIntegerDifferentRoleFixturesRetained boundary ≡ true
sameIntegerRolesRetainedRegression = refl

literalRuntimeMinimumRegression :
  P.equivalentFiniteSearchMinimumSize boundary ≡ 5
literalRuntimeMinimumRegression = refl

uniqueRuntimeMinimumRegression :
  P.equivalentFiniteSearchMinimumCount boundary ≡ 1
uniqueRuntimeMinimumRegression = refl

exactExecutionFirewallRegression :
  P.exactRepositoryPytestObserved boundary ≡ false
exactExecutionFirewallRegression = refl

kernelFirewallRegression :
  P.minimumHittingSetKernelProved boundary ≡ false
kernelFirewallRegression = refl

oeisAuthorityFirewallRegression :
  P.oeisCreatesLiteralMonsterIdentity boundary ≡ false
oeisAuthorityFirewallRegression = refl
