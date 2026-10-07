module DASHI.Governance.BoloBoloFederationCostComparisonRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.BoloBoloFederationCostComparisonExact as Comparison

sourceArchitectureRemainsSourceBounded :
  Comparison.sourceArchitectureUsedAsDesignInput Comparison.canonicalBoloComparisonBoundary ≡ true
sourceArchitectureRemainsSourceBounded = refl

costModelIsDerivedNotQuoted :
  Comparison.costModelQuotedFromBoloBolo Comparison.canonicalBoloComparisonBoundary ≡ false
costModelIsDerivedNotQuoted = refl

occupyEvidenceCalibratesRatherThanProves :
  Comparison.occupyEvidenceAutomaticallyProvesBoloSuperiority Comparison.canonicalBoloComparisonBoundary ≡ false
occupyEvidenceCalibratesRatherThanProves = refl

removedCouplingMustPayOverhead :
  Comparison.removedGlobalCouplingMustExceedFederationOverhead Comparison.canonicalBoloComparisonBoundary ≡ true
removedCouplingMustPayOverhead = refl

syntheticRetainedCostPinned : Comparison.retainedCost Comparison.syntheticCostModel ≡ 40
syntheticRetainedCostPinned = refl

syntheticRemovedCostPinned : Comparison.removedGlobalCouplingCost Comparison.syntheticCostModel ≡ 60
syntheticRemovedCostPinned = refl

syntheticOverheadPinned : Comparison.federationOverhead Comparison.syntheticCostModel ≡ 25
syntheticOverheadPinned = refl

syntheticGlobalCostPinned : Comparison.globalCoordinationCost Comparison.syntheticCostModel ≡ 100
syntheticGlobalCostPinned = refl

syntheticFederatedCostPinned : Comparison.federatedCoordinationCost Comparison.syntheticCostModel ≡ 65
syntheticFederatedCostPinned = refl

syntheticImprovementMarginPinned :
  Comparison.improvementMargin Comparison.syntheticRemovalPaysOverhead ≡ 34
syntheticImprovementMarginPinned = refl

syntheticStrictImprovement :
  Comparison.StrictCostImprovement Comparison.syntheticCostModel
syntheticStrictImprovement = Comparison.removalPaysOverheadImpliesStrictImprovement Comparison.syntheticRemovalPaysOverhead

noEmpiricalSuperiorityPromotion :
  Comparison.empiricalBoloSuperiorityEstablished Comparison.canonicalBoloComparisonBoundary ≡ false
noEmpiricalSuperiorityPromotion = refl
