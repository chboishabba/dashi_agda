module DASHI.Physics.YangMills.BalabanEffectiveCouplingTrajectory where

-- Source ledger for the *actual* effective-coupling coordinate used by
-- Balaban.  CMP 109 I, (0.18) and (0.20), updates inverse squared coupling:
--
--   1 / g_{k+1}² = 1 / g_k² - β_{k+1}(g_k).
--
-- The paper explicitly separates this recursive definition from the hard
-- theorem that the resulting sequence remains in a small interval.  In
-- particular it says that the perturbative proof of its Theorem 2 was not
-- published in the RG series.  This module preserves that boundary.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base using (ℕ; suc; _≤_)
open import Data.Product using (_×_)
open import Data.Empty using (⊥)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ ; 0ℝ ; _-ℝ_ ; _≤ℝ_ ; _<ℝ_ )
open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  ( SourceAuthorityId
  ; VerificationStatus
  ; balaban-cmp-109
  ; paperImport
  ; openTarget
  )

-- We keep the inverse-square coordinate explicit.  This avoids introducing a
-- division/inversion development merely to transcribe the source recurrence.
record BalabanInverseSquareCouplingStep : Set₁ where
  field
    coupling : ℕ → ℝ
    inverseSquaredCoupling : ℕ → ℝ
    betaCorrection : ℕ → ℝ

    -- Source equations (0.18), (0.20).  `betaCorrection (suc k)` denotes
    -- Balaban's β_{k+1}(g_k), including its scale dependence.
    exactInverseSquareUpdate :
      ∀ k →
      inverseSquaredCoupling (suc k)
        ≡ inverseSquaredCoupling k -ℝ betaCorrection (suc k)

    inverseSquareCoordinateMeaning : Set
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    noClayPromotion : clayYangMillsPromoted ≡ false

open BalabanInverseSquareCouplingStep public

record CouplingTrajectoryInsideSmallInterval
    (step : BalabanInverseSquareCouplingStep) : Set where
  field
    terminalScale : ℕ
    γ : ℝ
    γ-positive : 0ℝ <ℝ γ
    staysPositiveAndSmall :
      ∀ k → k ≤ terminalScale →
      (0ℝ <ℝ coupling step k) × (coupling step k ≤ℝ γ)

open CouplingTrajectoryInsideSmallInterval public

-- The CMP 122 theorem fixes γ externally.  This parameterised form is the
-- exact premise shape needed to apply it to a particular source theorem.
record CouplingTrajectoryBoundedBy
    (γ : ℝ)
    (step : BalabanInverseSquareCouplingStep) : Set where
  field
    terminalScale : ℕ
    γ-positive : 0ℝ <ℝ γ
    staysPositiveAndSmall :
      ∀ k → k ≤ terminalScale →
      (0ℝ <ℝ coupling step k) × (coupling step k ≤ℝ γ)

open CouplingTrajectoryBoundedBy public

-- The only missing mathematical input for this interface is deliberately
-- narrow: it must establish the small interval for the recurrence above.  A
-- fifth-order remainder statement is not assumed here because CMP 109 uses
-- its own β-functions and coupling coordinate.
record BalabanCouplingTrajectoryProofTarget : Set₁ where
  field
    step : BalabanInverseSquareCouplingStep
    initialSmallnessHypothesis : Set
    trajectory : CouplingTrajectoryInsideSmallInterval step
    sourceOrOwnedProof : Set
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    noClayPromotion : clayYangMillsPromoted ≡ false

-- Audit findings, not proof witnesses.
inverseSquareRecurrenceExtracted : Bool
inverseSquareRecurrenceExtracted = true

betaCorrectionEstimateExtracted : Bool
betaCorrectionEstimateExtracted = false

publishedSmallIntervalProofLocated : Bool
publishedSmallIntervalProofLocated = false

effectiveCouplingInvariantIntervalAvailable : Set
effectiveCouplingInvariantIntervalAvailable = ⊥

currentEffectiveCouplingTrajectoryStatus : VerificationStatus
currentEffectiveCouplingTrajectoryStatus = openTarget
