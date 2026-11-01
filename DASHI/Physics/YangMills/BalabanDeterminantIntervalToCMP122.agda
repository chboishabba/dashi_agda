module DASHI.Physics.YangMills.BalabanDeterminantIntervalToCMP122 where

-- End-to-end finite-cutoff composition:
--
--   cumulative determinant shell identity
--   + endpoint/correction/interaction upper bounds
--   + bare inverse-square budget
--   -> small coupling through cutoff K
--   -> published CMP 122 uniform RG closure.
--
-- All analytic and source-specific statements remain explicit arguments.  The
-- theorem owns only their mechanical composition.

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base using (ℕ; zero; suc; _≤_; _+_)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; _+ℝ_
  ; _-ℝ_
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
  ; UniformBalabanRGClosureAt
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
open import DASHI.Physics.YangMills.BalabanDeterminantIntervalToPrefix using
  ( determinantIntervalBoundsToBetaPrefix )
open import DASHI.Physics.YangMills.BalabanCMP122ConditionalRGClosure using
  ( BalabanCMP122ConditionalTheorem
  ; γ
  ; section2Package
  ; finiteCutoffUniformBalabanRG
  ; CouplingBoundCoversSection2
  )

replaceLeftNat≤ :
  ∀ {m n p : ℕ} →
  m ≡ n →
  n ≤ p →
  m ≤ p
replaceLeftNat≤ refl n≤p = n≤p

-- Repackage a source closure at a larger ultraviolet cutoff.  The equality in
-- `UniformBalabanRGClosure` ties its terminal scale to the source Sect. 2
-- package, so a bound on that package is sufficient.
uniformClosureAtFromSourceTerminal :
  {K : ℕ} →
  (closure : UniformBalabanRGClosure) →
  BalabanSection2InductivePackage.terminalScale
    (UniformBalabanRGClosure.section2 closure)
    ≤ K →
  UniformBalabanRGClosureAt K
uniformClosureAtFromSourceTerminal closure sourceTerminal≤K =
  record
    { closure = closure
    ; sourceTerminalWithinCutoff =
        replaceLeftNat≤
          (UniformBalabanRGClosure.terminalScaleAgrees closure)
          sourceTerminal≤K
    }

determinantIntervalBoundsToFiniteCutoffRG :
  (theorem : BalabanCMP122ConditionalTheorem) →
  (arith : InverseSquareBudgetArithmetic) →
  (order : InverseSquareBudgetOrderBridge) →
  (K : ℕ) →
  (step : BalabanInverseSquareCouplingStep) →
  (threshold :
    InverseSquareThresholdControlsCoupling K (γ theorem) step) →
  (gaussian correction interaction endpoint : ℕ → ℝ) →
  (totalBeta :
    ∀ j →
    betaCorrection step (suc j)
      ≡ gaussian (suc j) +ℝ interaction (suc j)) →
  (shellDecomposition :
    ∀ j →
    gaussian (suc j)
      ≡ (endpoint (suc j) -ℝ endpoint j)
          +ℝ correction (suc j)) →
  (endpointUpper correctionUpper interactionUpper : ℕ → ℕ → ℝ) →
  (endpointBound :
    ∀ k n →
    endpoint (n + k) -ℝ endpoint k
      ≤ℝ endpointUpper k n) →
  (correctionBound :
    ∀ k n →
    intervalSum correction k n
      ≤ℝ correctionUpper k n) →
  (interactionBound :
    ∀ k n →
    intervalSum interaction k n
      ≤ℝ interactionUpper k n) →
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
determinantIntervalBoundsToFiniteCutoffRG
  theorem arith order K step threshold
  gaussian correction interaction endpoint
  totalBeta shellDecomposition
  endpointUpper correctionUpper interactionUpper
  endpointBound correctionBound interactionBound
  bareCouplingBudget
  sourceAuthorityId theoremLocator status noClayPromotion
  sourceTerminal≤K =
  let
    budget = determinantIntervalBoundsToBetaPrefix
      K step threshold
      gaussian correction interaction endpoint
      totalBeta shellDecomposition
      endpointUpper correctionUpper interactionUpper
      endpointBound correctionBound interactionBound
      bareCouplingBudget
      sourceAuthorityId theoremLocator status noClayPromotion
  in
    finiteCutoffUniformBalabanRG
      theorem arith order threshold budget
      (record
        { coversSourceTerminal = sourceTerminal≤K
        })
