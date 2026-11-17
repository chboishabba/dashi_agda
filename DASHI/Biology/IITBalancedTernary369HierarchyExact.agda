module DASHI.Biology.IITBalancedTernary369HierarchyExact where

open import DASHI.Core.Prelude

import DASHI.Foundations.BalancedTernaryAntipodal369OrbitHierarchyExact as Hierarchy
import DASHI.Foundations.BalancedTernaryResidualTreeExact as Residual
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent

------------------------------------------------------------------------
-- BALANCED-TERNARY / 369 HIERARCHY AS A CONTROLLED OBSERVER FAMILY
--
-- The repo already owns exact 3, 9 and 27 carriers and their antipodal orbit
-- quotients.  Here they are registered as integration/coarse-graining test
-- surfaces.  The counts themselves are not IIT quantities.
------------------------------------------------------------------------

rank1OrbitObserver : SSP.SSPTrit → Hierarchy.AntipodalClass3
rank1OrbitObserver = Hierarchy.classifyAntipodal3

rank1IdentityConsumer : SSP.SSPTrit → SSP.SSPTrit
rank1IdentityConsumer x = x

negativeAndPositiveShareOrbit :
  rank1OrbitObserver SSP.sspNegOne ≡
  rank1OrbitObserver SSP.sspPosOne
negativeAndPositiveShareOrbit = refl

negativeTritNotPositive : SSP.sspNegOne ≡ SSP.sspPosOne → ⊥
negativeTritNotPositive ()

rank1OrbitLosesSignedIdentity :
  Descent.ConsumerNonDescentWitness
    rank1OrbitObserver
    rank1IdentityConsumer
rank1OrbitLosesSignedIdentity =
  Descent.consumerNonDescentWitness
    SSP.sspNegOne
    SSP.sspPosOne
    refl
    negativeTritNotPositive

rank1OrbitCannotRecoverSignedIdentity :
  Descent.FactorsThrough rank1OrbitObserver rank1IdentityConsumer → ⊥
rank1OrbitCannotRecoverSignedIdentity =
  Descent.nonDescentWitnessBlocksFactorization
    rank1OrbitLosesSignedIdentity

raw369Counts :
  Hierarchy.rawCarrierCount Hierarchy.rank1 ≡ 3
  × Hierarchy.rawCarrierCount Hierarchy.rank2 ≡ 9
  × Hierarchy.rawCarrierCount Hierarchy.rank3 ≡ 27
raw369Counts = refl , refl , refl

quotient369Counts :
  Hierarchy.quotientOrbitCount Hierarchy.rank1 ≡ 2
  × Hierarchy.quotientOrbitCount Hierarchy.rank2 ≡ 5
  × Hierarchy.quotientOrbitCount Hierarchy.rank3 ≡ 14
quotient369Counts = refl , refl , refl

stageFiveResidualSurvivesVisibleFallback :
  Residual.residualConstituent Residual.stageFiveRetainedTree ≡
  Residual.none → ⊥
stageFiveResidualSurvivesVisibleFallback =
  Residual.stageFiveProjectionDoesNotEraseTwo

record Ternary369IITBoundary : Set where
  constructor ternary369IITBoundary
  field
    threeNineTwentySevenGiveExactFiniteRefinementFixtures : Bool
    antipodalQuotientCanLoseSignedIdentity : Bool
    retainedResidualCanKeepFineInformationBehindCoarseView : Bool
    raw369CountsAreIITPhiValues : Bool
    antipodalOrbitCountProvesConsciousnessOrdering : Bool
    everyCoarseGrainingPreservesIntegration : Bool
    consumerRelativeDescentMustBeTested : Bool

open Ternary369IITBoundary public

canonicalTernary369IITBoundary : Ternary369IITBoundary
canonicalTernary369IITBoundary =
  ternary369IITBoundary
    true true true
    false false false true

countsAreNotPhi :
  raw369CountsAreIITPhiValues canonicalTernary369IITBoundary ≡ false
countsAreNotPhi = refl

coarseGrainingNeedsProof :
  everyCoarseGrainingPreservesIntegration canonicalTernary369IITBoundary ≡ false
coarseGrainingNeedsProof = refl
