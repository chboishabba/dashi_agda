module DASHI.Physics.Plasma.ToroidalZeroBounceArchitectureForkExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.ToroidalConstantMagnitudeHybridABCExact as ABC
import DASHI.Physics.Plasma.ToroidalZeroBounceSparseSupportMaxCutExact as Sparse
import DASHI.Physics.Plasma.ZeroBouncePopulationExact as ZeroBounce

data ZeroBounceArchitectureBranch : Set where
  axisymmetricCurrentCarrying : ZeroBounceArchitectureBranch
  externalTransformC3 : ZeroBounceArchitectureBranch

record ArchitectureForkReceipt
    (population : ZeroBounce.DeclaredParticlePopulation) : Set₁ where
  constructor architecture-fork-receipt
  field
    sparseCut : Sparse.SparseSupportMaxCut population
    axisymmetricBranchReceipt : Set
    plasmaCurrentOrDrivenTransformReceipt : Set
    externalTransformBranchReceipt : Set
    nonAxisymmetricC3Receipt : Set
    sameZeroBounceConsumerReceipt : Set
    sameBestKnownReferenceReceipt : Set
    branchReference : String

record ArchitectureForkBoundary : Set where
  constructor architecture-fork-boundary
  field
    axisymmetricSparseWinnerProvesExternalTransform : Bool
    axisymmetricSparseWinnerProvesExternalTransformIsFalse :
      axisymmetricSparseWinnerProvesExternalTransform ≡ false
    nonAxisymmetricConstraintMayBeRequiredForExternalTransform : Bool
    nonAxisymmetricConstraintMayBeRequiredForExternalTransformIsTrue :
      nonAxisymmetricConstraintMayBeRequiredForExternalTransform ≡ true
    optimizerMaySilentlyCollapseArchitectureWithoutBranchConstraint : Bool
    optimizerMaySilentlyCollapseArchitectureWithoutBranchConstraintIsTrue :
      optimizerMaySilentlyCollapseArchitectureWithoutBranchConstraint ≡ true

canonicalArchitectureForkBoundary : ArchitectureForkBoundary
canonicalArchitectureForkBoundary =
  architecture-fork-boundary false refl true refl true refl

localAblationReference : String
localAblationReference =
  "2026-10-07 local ablation: unconstrained sparse basin is axisymmetric; imposing C3 non-axisymmetric coefficient norm floors through 0.12 raises the toy geometry objective only modestly, so a distinct external-transform branch remains numerically plausible."
