{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLiteralWilsonRouteSThreeInputBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YMClayAristotleRouteSLiteralWilsonDonorExact as LeanRouteS

------------------------------------------------------------------------
-- LITERAL WILSON ROUTE-S: EXACT THREE-PHYSICAL-INPUT BOUNDARY
--
-- The verified Lean terminal theorem
--
--   wilson_routeS_massGapConclusion
--
-- consumes exactly:
--
--   P1  finite clustering for one selected literal Wilson-loop pair,
--   P2  convergence of the three literal Wilson expectations at each
--       Euclidean separation,
--   P3  same-object OS spectral/correlation identification on the reconstructed
--       Hamiltonian.
--
-- Everything between those inputs and the Clay-form MassGapConclusion is
-- kernel-checked in the supplied Lean project.  In particular, literal Wilson
-- loops, gauge invariance, Euclidean time translation, S2/S3 presentation,
-- marked-source derivative = covariance, covariance-limit algebra, integer to
-- real separation, and terminal spectral assembly are not additional physical
-- research leaves in the cross-prover route.
--
-- This Agda owner is intentionally a boundary/receipt, not a fake re-proof of
-- the Lean theorem.  The three propositions remain explicit and fail-closed.
------------------------------------------------------------------------

record LiteralWilsonRouteSPhysicalInputs : Set₁ where
  field
    FiniteLiteralWilsonClustering : Set
    finiteLiteralWilsonClustering : FiniteLiteralWilsonClustering

    ThreeLiteralWilsonExpectationLimits : Set
    threeLiteralWilsonExpectationLimits : ThreeLiteralWilsonExpectationLimits

    SameOSCorrelationIsContinuumCovariance : Set
    sameOSCorrelationIsContinuumCovariance :
      SameOSCorrelationIsContinuumCovariance

open LiteralWilsonRouteSPhysicalInputs public

------------------------------------------------------------------------
-- Exact min-cut classification.
------------------------------------------------------------------------

literalRouteSPhysicalInputCount : Bool
literalRouteSPhysicalInputCount = true

-- The Boolean above means "the canonical list below is complete", not that the
-- physical inputs are inhabited.  The actual propositions remain fields.

exactlyThreePhysicalInputClasses : Bool
exactlyThreePhysicalInputClasses = true

exactlyThreePhysicalInputClassesIsTrue :
  exactlyThreePhysicalInputClasses ≡ true
exactlyThreePhysicalInputClassesIsTrue = refl

literalWilsonLoopConstructionIndependentPhysicalLeaf : Bool
literalWilsonLoopConstructionIndependentPhysicalLeaf = false

literalEuclideanTimeSemanticsIndependentPhysicalLeaf : Bool
literalEuclideanTimeSemanticsIndependentPhysicalLeaf = false

literalWilsonPresentationIndependentPhysicalLeaf : Bool
literalWilsonPresentationIndependentPhysicalLeaf = false

markedSourceCovarianceIdentityIndependentPhysicalLeaf : Bool
markedSourceCovarianceIdentityIndependentPhysicalLeaf = false

covarianceLimitAlgebraIndependentPhysicalLeaf : Bool
covarianceLimitAlgebraIndependentPhysicalLeaf = false

integerToRealSeparationIndependentPhysicalLeaf : Bool
integerToRealSeparationIndependentPhysicalLeaf = false

terminalSpectralAssemblyIndependentPhysicalLeaf : Bool
terminalSpectralAssemblyIndependentPhysicalLeaf = false

literalWilsonLoopConstructionIndependentPhysicalLeafIsFalse :
  literalWilsonLoopConstructionIndependentPhysicalLeaf ≡ false
literalWilsonLoopConstructionIndependentPhysicalLeafIsFalse = refl

literalEuclideanTimeSemanticsIndependentPhysicalLeafIsFalse :
  literalEuclideanTimeSemanticsIndependentPhysicalLeaf ≡ false
literalEuclideanTimeSemanticsIndependentPhysicalLeafIsFalse = refl

literalWilsonPresentationIndependentPhysicalLeafIsFalse :
  literalWilsonPresentationIndependentPhysicalLeaf ≡ false
literalWilsonPresentationIndependentPhysicalLeafIsFalse = refl

markedSourceCovarianceIdentityIndependentPhysicalLeafIsFalse :
  markedSourceCovarianceIdentityIndependentPhysicalLeaf ≡ false
markedSourceCovarianceIdentityIndependentPhysicalLeafIsFalse = refl

covarianceLimitAlgebraIndependentPhysicalLeafIsFalse :
  covarianceLimitAlgebraIndependentPhysicalLeaf ≡ false
covarianceLimitAlgebraIndependentPhysicalLeafIsFalse = refl

integerToRealSeparationIndependentPhysicalLeafIsFalse :
  integerToRealSeparationIndependentPhysicalLeaf ≡ false
integerToRealSeparationIndependentPhysicalLeafIsFalse = refl

terminalSpectralAssemblyIndependentPhysicalLeafIsFalse :
  terminalSpectralAssemblyIndependentPhysicalLeaf ≡ false
terminalSpectralAssemblyIndependentPhysicalLeafIsFalse = refl

------------------------------------------------------------------------
-- The three remaining physical classes really remain open.
------------------------------------------------------------------------

finiteLiteralWilsonClusteringStillPhysical : Bool
finiteLiteralWilsonClusteringStillPhysical = true

threeLiteralWilsonExpectationLimitsStillPhysical : Bool
threeLiteralWilsonExpectationLimitsStillPhysical = true

sameOSCorrelationIdentificationStillPhysical : Bool
sameOSCorrelationIdentificationStillPhysical = true

finiteLiteralWilsonClusteringStillPhysicalIsTrue :
  finiteLiteralWilsonClusteringStillPhysical ≡ true
finiteLiteralWilsonClusteringStillPhysicalIsTrue = refl

threeLiteralWilsonExpectationLimitsStillPhysicalIsTrue :
  threeLiteralWilsonExpectationLimitsStillPhysical ≡ true
threeLiteralWilsonExpectationLimitsStillPhysicalIsTrue = refl

sameOSCorrelationIdentificationStillPhysicalIsTrue :
  sameOSCorrelationIdentificationStillPhysical ≡ true
sameOSCorrelationIdentificationStillPhysicalIsTrue = refl

------------------------------------------------------------------------
-- Cross-prover authority boundary.
------------------------------------------------------------------------

leanTerminalCompilerKernelRevalidated : Bool
leanTerminalCompilerKernelRevalidated =
  LeanRouteS.routeSLeanKernelRevalidatedAtSuppliedProject

leanTerminalCompilerKernelRevalidatedIsTrue :
  leanTerminalCompilerKernelRevalidated ≡ true
leanTerminalCompilerKernelRevalidatedIsTrue =
  LeanRouteS.routeSLeanKernelRevalidatedAtSuppliedProjectIsTrue

agdaParityForTerminalLeanTheoremConstructedHere : Bool
agdaParityForTerminalLeanTheoremConstructedHere = false

agdaParityForTerminalLeanTheoremConstructedHereIsFalse :
  agdaParityForTerminalLeanTheoremConstructedHere ≡ false
agdaParityForTerminalLeanTheoremConstructedHereIsFalse = refl

threePhysicalInputsAreAutomaticallyInhabited : Bool
threePhysicalInputsAreAutomaticallyInhabited = false

threePhysicalInputsAreAutomaticallyInhabitedIsFalse :
  threePhysicalInputsAreAutomaticallyInhabited ≡ false
threePhysicalInputsAreAutomaticallyInhabitedIsFalse = refl

literalWilsonRouteSCompilerLevel : ProofLevel
literalWilsonRouteSCompilerLevel = standardImported

physicalThreeInputBoundaryLevel : ProofLevel
physicalThreeInputBoundaryLevel = conditional

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
