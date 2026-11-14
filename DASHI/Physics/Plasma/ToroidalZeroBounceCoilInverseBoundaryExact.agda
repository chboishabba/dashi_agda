module DASHI.Physics.Plasma.ToroidalZeroBounceCoilInverseBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.ToroidalZeroBounceArchitectureForkExact as Fork
import DASHI.Physics.Plasma.ZeroBouncePopulationExact as ZeroBounce

record CoilInverseTarget
    (population : ZeroBounce.DeclaredParticlePopulation) : Set₁ where
  constructor coil-inverse-target
  field
    branch : Fork.ZeroBounceArchitectureBranch
    plasmaBoundaryReceipt : Set
    totalTargetFieldReceipt : Set
    plasmaCurrentFieldReceipt : Set
    externalFieldTargetReceipt : Set
    targetNormalFieldReceipt : Set
    sameEquilibriumReceipt : Set
    sameZeroBounceConsumerReceipt : Set
    targetReference : String

open CoilInverseTarget public

record WindingSurfaceCurrentPotentialReceipt
    (population : ZeroBounce.DeclaredParticlePopulation)
    (target : CoilInverseTarget population) : Set₁ where
  constructor winding-surface-current-potential-receipt
  field
    windingSurfaceReceipt : Set
    currentPotentialReceipt : Set
    surfaceCurrentIsNormalCrossGradientReceipt : Set
    biotSavartMapReceipt : Set
    normalFieldResidualReceipt : Set
    regularizationReceipt : Set
    toroidalFluxOrCurrentNormalizationReceipt : Set
    filamentContourExtractionReceipt : Set
    coilClearanceReceipt : Set
    curvatureAndStrainReceipt : Set
    manufacturabilityReceipt : Set
    receiptReference : String

open WindingSurfaceCurrentPotentialReceipt public

record CoilInverseBoundary : Set where
  constructor coil-inverse-boundary
  field
    externalCoilsMustReproduceFullFiniteBetaInteriorFieldPointwise : Bool
    externalCoilsMustReproduceFullFiniteBetaInteriorFieldPointwiseIsFalse :
      externalCoilsMustReproduceFullFiniteBetaInteriorFieldPointwise ≡ false
    coilInverseTargetsBoundaryNormalCondition : Bool
    coilInverseTargetsBoundaryNormalConditionIsTrue :
      coilInverseTargetsBoundaryNormalCondition ≡ true
    plasmaAndExternalFieldContributionsMustRemainSeparated : Bool
    plasmaAndExternalFieldContributionsMustRemainSeparatedIsTrue :
      plasmaAndExternalFieldContributionsMustRemainSeparated ≡ true
    zeroNormalFieldAloneAllowsTrivialZeroCurrentSolution : Bool
    zeroNormalFieldAloneAllowsTrivialZeroCurrentSolutionIsTrue :
      zeroNormalFieldAloneAllowsTrivialZeroCurrentSolution ≡ true
    fluxOrCurrentNormalizationStillRequired : Bool
    fluxOrCurrentNormalizationStillRequiredIsTrue :
      fluxOrCurrentNormalizationStillRequired ≡ true

canonicalCoilInverseBoundary : CoilInverseBoundary
canonicalCoilInverseBoundary =
  coil-inverse-boundary false refl true refl true refl true refl true refl

methodReference : String
methodReference =
  "NESCOIL/REGCOIL-style stage-two inverse: optimize a winding-surface current potential against the target normal magnetic field with regularization, then contour the potential into filamentary coils. Finite-beta plasma-current contribution remains separate."
