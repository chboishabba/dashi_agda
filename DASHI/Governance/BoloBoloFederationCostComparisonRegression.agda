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

syntheticStrictImprovement : Comparison.StrictCostImprovement Comparison.syntheticCostModel
syntheticStrictImprovement =
  Comparison.removalPaysOverheadImpliesStrictImprovement Comparison.syntheticRemovalPaysOverhead

linearRemovedCouplingPinned :
  Comparison.removedGlobalCouplingCost
    (Comparison.linearCostModel Comparison.syntheticUnitWeights Comparison.syntheticAccounting) ≡ 60
linearRemovedCouplingPinned = refl

linearFederationOverheadPinned :
  Comparison.weightedFederationOverhead Comparison.syntheticUnitWeights Comparison.syntheticAccounting ≡ 25
linearFederationOverheadPinned = refl

linearWinMarginPinned :
  Comparison.linearImprovementMargin Comparison.syntheticLinearWinCondition ≡ 34
linearWinMarginPinned = refl

linearWinImpliesStrictImprovement :
  Comparison.StrictCostImprovement
    (Comparison.linearCostModel Comparison.syntheticUnitWeights Comparison.syntheticAccounting)
linearWinImpliesStrictImprovement =
  Comparison.linearWinConditionImpliesStrictImprovement Comparison.syntheticLinearWinCondition

nestedOverheadPinned :
  Comparison.nestedFederationOverhead Comparison.syntheticNestedComponents ≡ 25
nestedOverheadPinned = refl

nestedBoloInterfacePinned :
  Comparison.boloInterfaceCost Comparison.syntheticNestedComponents ≡ 5
nestedBoloInterfacePinned = refl

nestedTegaInterfacePinned :
  Comparison.tegaInterfaceCost Comparison.syntheticNestedComponents ≡ 5
nestedTegaInterfacePinned = refl

nestedWinMarginPinned :
  Comparison.nestedImprovementMargin Comparison.syntheticNestedWinCondition ≡ 34
nestedWinMarginPinned = refl

nestedWinImpliesStrictImprovement :
  Comparison.StrictCostImprovement
    (Comparison.nestedBoloCostModel Comparison.syntheticNestedComponents)
nestedWinImpliesStrictImprovement =
  Comparison.nestedBoloWinConditionImpliesStrictImprovement Comparison.syntheticNestedWinCondition

sourcePopulationDoesNotBecomeWeight :
  Comparison.sourcePopulationNumbersBecomeCostCoefficients Comparison.canonicalBoloComparisonBoundary ≡ false
sourcePopulationDoesNotBecomeWeight = refl

noEmpiricalSuperiorityPromotion :
  Comparison.empiricalBoloSuperiorityEstablished Comparison.canonicalBoloComparisonBoundary ≡ false
noEmpiricalSuperiorityPromotion = refl
