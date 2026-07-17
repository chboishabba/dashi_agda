module DASHI.Physics.YangMills.BalabanCumulativeDeterminantToCMP122 where

-- Canonical end-to-end finite-cutoff route based on the simultaneous block
-- determinant identity, with no adjacent determinant telescope assumption.

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base using (ℕ; zero; suc; _≤_)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; _+ℝ_
  ; _≤ℝ_
  )
open import DASHI.Geometry.Gauge.SUNPrimitives using
  ( clayYangMillsPromoted )
open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  ( SourceAuthorityId
  ; VerificationStatus
  )
open import DASHI.Physics.YangMills.BalabanSection2InductivePackage using
  ( UniformBalabanRGClosure
  ; BalabanSection2InductivePackage
  )
open import DASHI.Physics.YangMills.BalabanEffectiveCouplingTrajectory using
  ( BalabanInverseSquareCouplingStep
  ; inverseSquaredCoupling
  ; betaCorrection
  )
open import DASHI.Physics.YangMills.BalabanInverseSquareCouplingBudget using
  ( InverseSquareBudgetArithmetic
  ; InverseSquareBudgetOrderBridge
  ; InverseSquareThresholdControlsCoupling
  ; gammaInverseSquare
  )
open import DASHI.Physics.YangMills.BalabanIntervalDeterminantAlgebra using
  ( intervalSum )
open import DASHI.Physics.YangMills.BalabanCumulativeDeterminantToPrefix using
  ( cumulativeDeterminantBoundsToBetaPrefix )
open import DASHI.Physics.YangMills.BalabanCMP122ConditionalRGClosure using
  ( BalabanCMP122ConditionalTheorem
  ; γ
  ; section2Package
  ; finiteCutoffUniformBalabanRG
  )

cumulativeDeterminantBoundsToFiniteCutoffRG :
  (theorem : BalabanCMP122ConditionalTheorem) →
  (arith : InverseSquareBudgetArithmetic) →
  (order : InverseSquareBudgetOrderBridge) →
  (K : ℕ) →
  (step : BalabanInverseSquareCouplingStep) →
  (threshold :
    InverseSquareThresholdControlsCoupling K (γ theorem) step) →
  (gaussian interaction : ℕ → ℝ) →
  (endpointDifference cumulativeCorrection : ℕ → ℕ → ℝ) →
  (totalBeta :
    ∀ j →
    betaCorrection step (suc j)
      ≡ gaussian (suc j) +ℝ interaction (suc j)) →
  (cumulativeGaussianIdentity :
    ∀ k n →
    intervalSum gaussian k n
      ≡ endpointDifference k n +ℝ cumulativeCorrection k n) →
  (endpointUpper correctionUpper interactionUpper : ℕ → ℕ → ℝ) →
  (endpointUpperBound :
    ∀ k n →
    endpointDifference k n ≤ℝ endpointUpper k n) →
  (correctionUpperBound :
    ∀ k n →
    cumulativeCorrection k n ≤ℝ correctionUpper k n) →
  (interactionUpperBound :
    ∀ k n →
    intervalSum interaction k n ≤ℝ interactionUpper k n) →
  (bareCouplingBudget :
    ∀ k → k ≤ K →
    gammaInverseSquare threshold
      +ℝ ((endpointUpper zero k +ℝ correctionUpper zero k)
          +ℝ interactionUpper zero k)
      ≤ℝ inverseSquaredCoupling step zero) →
  (sourceAuthorityId : SourceAuthorityId) →
  (theoremLocator : String) →
  (status : VerificationStatus) →
  (noClayPromotion : clayYangMillsPromoted ≡ false) →
  BalabanSection2InductivePackage.terminalScale (section2Package theorem)
    ≤ K →
  UniformBalabanRGClosure
cumulativeDeterminantBoundsToFiniteCutoffRG
  theorem arith order K step threshold
  gaussian interaction
  endpointDifference cumulativeCorrection
  totalBeta cumulativeGaussianIdentity
  endpointUpper correctionUpper interactionUpper
  endpointUpperBound correctionUpperBound interactionUpperBound
  bareCouplingBudget
  sourceAuthorityId theoremLocator status noClayPromotion
  sourceTerminal≤K =
  let
    budget = cumulativeDeterminantBoundsToBetaPrefix
      K step threshold
      gaussian interaction
      endpointDifference cumulativeCorrection
      totalBeta cumulativeGaussianIdentity
      endpointUpper correctionUpper interactionUpper
      endpointUpperBound correctionUpperBound interactionUpperBound
      bareCouplingBudget
      sourceAuthorityId theoremLocator status noClayPromotion
  in
    finiteCutoffUniformBalabanRG
      theorem arith order threshold budget
      (record
        { coversSourceTerminal = sourceTerminal≤K
        })
