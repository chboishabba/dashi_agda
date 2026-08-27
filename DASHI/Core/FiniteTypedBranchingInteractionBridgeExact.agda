module DASHI.Core.FiniteTypedBranchingInteractionBridgeExact where

------------------------------------------------------------------------
-- TYPED BRANCHING KERNEL -> GENERIC BINARY INTERACTION ADMISSION
--
-- PRIMARY MATHEMATICAL SOURCES
--
-- Theodore E. Harris,
-- "The Theory of Branching Processes", Springer, 1963.
-- DOI: 10.1007/978-3-642-51866-9.
--
-- E. Seneta,
-- "Non-negative Matrices and Markov Chains", 2nd ed., Springer, 1981.
-- DOI: 10.1007/0-387-32792-4.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", 2nd ed., Cambridge University Press, 2013.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- `FiniteTypedBranchingReachabilityBridgeExact` already proves that equal row
-- mass/regime does not determine target reachability.  This file asks the
-- complementary structural question: does the local source x target kernel
-- itself reduce to endpoint-only potentials?  On the canonical trap/escape
-- rectangle, the answer is exactly no.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.BinaryInteractionNonseparabilityExact as Interaction
import DASHI.Core.FiniteTypedBranchingKernelExact as Kernel
import DASHI.Core.FiniteTypedBranchingReachabilityBridgeExact as Branch
import DASHI.Core.AdmissibleReachability as Reach

------------------------------------------------------------------------
-- Reuse the existing route kernel as a generic binary response surface.
------------------------------------------------------------------------

routeInteractionSurface : Interaction.BinaryNatSurface
routeInteractionSurface =
  Interaction.binary-nat-surface
    Branch.RouteType
    Branch.RouteType
    Branch.routeOffspring
    "Existing typed branching support matrix viewed only through the generic binary interaction interface."

-- Rectangle on rows trapStart/escapeStart and columns trapped/escapeGoal:
--
--   1 0
--   0 1
--
-- so diagonal sum 2 differs from cross sum 0.
routeRectangleObstruction :
  Interaction.RectangleObstruction routeInteractionSurface
routeRectangleObstruction =
  Interaction.rectangle-obstruction
    Branch.trapStart
    Branch.escapeStart
    Branch.trapped
    Branch.escapeGoal
    (λ ())

routeRankOneObstruction :
  Interaction.RankOneMinorObstruction routeInteractionSurface
routeRankOneObstruction =
  Interaction.rank-one-minor-obstruction
    Branch.trapStart
    Branch.escapeStart
    Branch.trapped
    Branch.escapeGoal
    (λ ())

routeStrongInteractionAdmission :
  Interaction.StrongBinaryInteractionAdmission routeInteractionSurface
routeStrongInteractionAdmission =
  Interaction.strong-binary-interaction-admission
    routeRectangleObstruction
    routeRankOneObstruction

routeKernelIsNotEndpointAdditive :
  Interaction.NonseparableAdditiveInteraction routeInteractionSurface
routeKernelIsNotEndpointAdditive =
  Interaction.strongAdmissionImpliesAdditiveNonseparability
    routeStrongInteractionAdmission

------------------------------------------------------------------------
-- Joint capstone with the previous reachability result.
------------------------------------------------------------------------

record BranchCountInteractionReachabilitySeparation : Set₁ where
  constructor branch-count-interaction-reachability-separation
  field
    sameLocalRowMass :
      Kernel.rowScaledMass Branch.routeKernel Branch.trapStart
      ≡ Kernel.rowScaledMass Branch.routeKernel Branch.escapeStart
    sameLocalRegime :
      Kernel.rowRegime Branch.routeKernel Branch.trapStart
      ≡ Kernel.rowRegime Branch.routeKernel Branch.escapeStart
    kernelNotEndpointAdditive :
      Interaction.NonseparableAdditiveInteraction routeInteractionSurface
    trapCannotReachGoal :
      Reach.Reachable Branch.routeSystem Branch.trapStart Branch.escapeGoal → ⊥
    escapeCanReachGoal :
      Reach.Reachable Branch.routeSystem Branch.escapeStart Branch.escapeGoal

canonicalBranchCountInteractionReachabilitySeparation :
  BranchCountInteractionReachabilitySeparation
canonicalBranchCountInteractionReachabilitySeparation =
  branch-count-interaction-reachability-separation
    Branch.sameStartRowMass
    Branch.sameStartRowRegime
    routeKernelIsNotEndpointAdditive
    Branch.trapStartCannotReachGoal
    Branch.escapeStartReachesGoal

record FiniteTypedBranchingInteractionBoundary : Set where
  constructor finite-typed-branching-interaction-boundary
  field
    equalRowMassImpliesEndpointSeparableKernel : Bool
    equalRowMassImpliesEndpointSeparableKernelIsFalse :
      equalRowMassImpliesEndpointSeparableKernel ≡ false
    nonseparableKernelImpliesSameReachability : Bool
    nonseparableKernelImpliesSameReachabilityIsFalse :
      nonseparableKernelImpliesSameReachability ≡ false
    matrixInteractionAloneCreatesProbabilitySemantics : Bool
    matrixInteractionAloneCreatesProbabilitySemanticsIsFalse :
      matrixInteractionAloneCreatesProbabilitySemantics ≡ false

canonicalFiniteTypedBranchingInteractionBoundary :
  FiniteTypedBranchingInteractionBoundary
canonicalFiniteTypedBranchingInteractionBoundary =
  finite-typed-branching-interaction-boundary
    false refl
    false refl
    false refl
