{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLiteralWilsonRouteSThreeInputBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YMClayAristotleRouteSLiteralWilsonDonorExact as LeanRouteS
import DASHI.Physics.YangMills.YMClayLiteralWilsonP1FiniteClusteringExact as P1
import DASHI.Physics.YangMills.YMClayLiteralWilsonP2ExpectationConvergenceExact as P2
import DASHI.Physics.YangMills.YMClayLiteralWilsonP3SameOSCorrelationExact as P3

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
-- 2026-09-19 theorem-proof reduction of the three Lean hypotheses.
--
-- Important distinction:
--
--   * the Lean terminal theorem still has three displayed hypothesis classes;
--   * those classes are no longer three independent Agda physical theorems.
--
-- P1 is compiler output from R320 plus the same-carrier Wilson/T5 presentation.
-- P2's three expectation limits are compiler output from that same Wilson
-- presentation and PhysicalMeasureConvergenceData.
-- P3's continuum covariance = spectrum-correlation equality is definitional in
-- R281; the physical residue is only that this R281 spectrum is the spectrum of
-- the actual OS-reconstructed Hamiltonian.
------------------------------------------------------------------------

p1NeedsNewClusteringAnalysisAfterR320 : Bool
p1NeedsNewClusteringAnalysisAfterR320 =
  P1.newFiniteClusteringInequalityRequiredAfterR320

p1NeedsNewClusteringAnalysisAfterR320IsFalse :
  p1NeedsNewClusteringAnalysisAfterR320 ≡ false
p1NeedsNewClusteringAnalysisAfterR320IsFalse =
  P1.newFiniteClusteringInequalityRequiredAfterR320IsFalse

p2ThreeLimitsIndependentPhysicalTheorems : Bool
p2ThreeLimitsIndependentPhysicalTheorems =
  P2.threeExpectationLimitsIndependentPhysicalLeaves

p2ThreeLimitsIndependentPhysicalTheoremsIsFalse :
  p2ThreeLimitsIndependentPhysicalTheorems ≡ false
p2ThreeLimitsIndependentPhysicalTheoremsIsFalse =
  P2.threeExpectationLimitsIndependentPhysicalLeavesIsFalse

p3PostHocCovarianceCorrelationIdentityStillPhysical : Bool
p3PostHocCovarianceCorrelationIdentityStillPhysical =
  P3.postHocCorrelationIdentityStillPhysical

p3PostHocCovarianceCorrelationIdentityStillPhysicalIsFalse :
  p3PostHocCovarianceCorrelationIdentityStillPhysical ≡ false
p3PostHocCovarianceCorrelationIdentityStillPhysicalIsFalse =
  P3.postHocCorrelationIdentityStillPhysicalIsFalse

p3SameReconstructedHamiltonianSpectrumStillPhysical : Bool
p3SameReconstructedHamiltonianSpectrumStillPhysical =
  P3.sameReconstructedHamiltonianSpectrumStillPhysical

p3SameReconstructedHamiltonianSpectrumStillPhysicalIsTrue :
  p3SameReconstructedHamiltonianSpectrumStillPhysical ≡ true
p3SameReconstructedHamiltonianSpectrumStillPhysicalIsTrue =
  P3.sameReconstructedHamiltonianSpectrumStillPhysicalIsTrue

threeLeanHypothesisClassesAreThreeIndependentPhysicalTheorems : Bool
threeLeanHypothesisClassesAreThreeIndependentPhysicalTheorems = false

threeLeanHypothesisClassesAreThreeIndependentPhysicalTheoremsIsFalse :
  threeLeanHypothesisClassesAreThreeIndependentPhysicalTheorems ≡ false
threeLeanHypothesisClassesAreThreeIndependentPhysicalTheoremsIsFalse = refl

routeSIndependentPhysicalPaymentsAfterAgdaReduction : Bool
routeSIndependentPhysicalPaymentsAfterAgdaReduction = true

routeSIndependentPhysicalPaymentsAfterAgdaReductionIsTrue :
  routeSIndependentPhysicalPaymentsAfterAgdaReduction ≡ true
routeSIndependentPhysicalPaymentsAfterAgdaReductionIsTrue = refl

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
