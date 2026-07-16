module DASHI.Physics.YangMills.BalabanInverseSquareCouplingBudget where

-- Finite-cutoff coupling control for the inverse-square coordinate in
-- Balaban CMP 109 I, (0.18), (0.20).  This file deliberately proves only the
-- bookkeeping implication needed by CMP 122: a cumulative β-budget implies
-- its finite-scale small-coupling premise.  It neither assumes nor invents a
-- pointwise perturbative expansion for Balaban's β-correction.

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base using (ℕ; zero; suc; _≤_)
open import Data.Product using (_×_)
open import Data.Empty using (⊥)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ ; 0ℝ ; _+ℝ_ ; _-ℝ_ ; _≤ℝ_ ; _<ℝ_ ; ≤ℝ-trans ; cong ; trans )
open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  ( SourceAuthorityId ; VerificationStatus ; balaban-cmp-109 ; openTarget )
open import DASHI.Physics.YangMills.BalabanEffectiveCouplingTrajectory using
  ( BalabanInverseSquareCouplingStep
  ; coupling
  ; inverseSquaredCoupling
  ; betaCorrection
  ; exactInverseSquareUpdate
  ; CouplingTrajectoryBoundedBy
  )

sym :
  {A : Set} →
  {x y : A} →
  x ≡ y →
  y ≡ x
sym refl = refl

-- These are elementary ordered-additive laws, isolated because the common
-- real-analysis surface intentionally exposes only a minimal API.
record InverseSquareBudgetArithmetic : Set₁ where
  field
    sub-zero :
      ∀ a → a -ℝ 0ℝ ≡ a

    sub-assoc-right :
      ∀ a b c →
      (a -ℝ b) -ℝ c ≡ a -ℝ (b +ℝ c)

    subtract-right-antitone :
      ∀ {a b c} →
      b ≤ℝ c →
      (a -ℝ c) ≤ℝ (a -ℝ b)

    ≤-replace-right :
      ∀ {a b c} →
      a ≤ℝ b → b ≡ c → a ≤ℝ c

open InverseSquareBudgetArithmetic public

-- β₁ + ··· + βₖ.  The source recurrence writes β_{k+1} at the update from
-- k to k+1, hence the shifted index in the successor clause.
betaPrefixSum :
  BalabanInverseSquareCouplingStep →
  ℕ →
  ℝ
betaPrefixSum step zero = 0ℝ
betaPrefixSum step (suc k) =
  betaPrefixSum step k +ℝ betaCorrection step (suc k)

inverseSquareTelescoping :
  (arith : InverseSquareBudgetArithmetic) →
  (step : BalabanInverseSquareCouplingStep) →
  ∀ k →
  inverseSquaredCoupling step k
    ≡
  inverseSquaredCoupling step zero -ℝ betaPrefixSum step k
inverseSquareTelescoping arith step zero =
  sym (sub-zero arith (inverseSquaredCoupling step zero))
inverseSquareTelescoping arith step (suc k) =
  trans
    (exactInverseSquareUpdate step k)
    (trans
      (cong
        (λ u → u -ℝ betaCorrection step (suc k))
        (inverseSquareTelescoping arith step k))
      (sub-assoc-right arith
        (inverseSquaredCoupling step zero)
        (betaPrefixSum step k)
        (betaCorrection step (suc k))))

-- This is the semantic bridge that the inverse-square coordinate by itself
-- cannot supply: the source must identify a lower inverse-square threshold
-- with positivity and the desired bound on g.
record InverseSquareThresholdControlsCoupling
    (K : ℕ)
    (γ : ℝ)
    (step : BalabanInverseSquareCouplingStep) : Set₁ where
  field
    γ-positive : 0ℝ <ℝ γ
    gammaInverseSquare : ℝ
    thresholdControlsCoupling :
      ∀ k → k ≤ K →
      gammaInverseSquare ≤ℝ inverseSquaredCoupling step k →
      (0ℝ <ℝ coupling step k) × (coupling step k ≤ℝ γ)

open InverseSquareThresholdControlsCoupling public

-- The only analytic input is a prefix majorant plus a bare inverse-square
-- budget.  A pointwise β estimate is one possible way to construct this
-- record, but is intentionally not required by the consumer theorem.
record BalabanBetaPrefixBound
    (K : ℕ)
    (step : BalabanInverseSquareCouplingStep)
    {γ : ℝ}
    (threshold : InverseSquareThresholdControlsCoupling K γ step) : Set₁ where
  field
    prefixMajorant : ℕ → ℝ

    betaPrefixControlled :
      ∀ k → k ≤ K →
      betaPrefixSum step k ≤ℝ prefixMajorant k

    bareCouplingBudget :
      ∀ k → k ≤ K →
      gammaInverseSquare threshold +ℝ prefixMajorant k
        ≤ℝ inverseSquaredCoupling step zero

    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    noClayPromotion : clayYangMillsPromoted ≡ false

open BalabanBetaPrefixBound public

-- The equality in the final step is not derivable from the minimal real
-- surface: gamma + B ≤ u₀ is the natural budget form, whereas the preceding
-- line needs gamma ≤ u₀ - B.  Keep this ordered-field rearrangement named and
-- explicit rather than treating it as definitional arithmetic.
record InverseSquareBudgetOrderBridge : Set₁ where
  field
    addBudgetImpliesSubBudget :
      ∀ {γ B u₀ : ℝ} →
      γ +ℝ B ≤ℝ u₀ →
      γ ≤ℝ u₀ -ℝ B

open InverseSquareBudgetOrderBridge public

inverseSquareAboveGammaThreshold′ :
  (arith : InverseSquareBudgetArithmetic) →
  (order : InverseSquareBudgetOrderBridge) →
  {K : ℕ} →
  {γ : ℝ} →
  {step : BalabanInverseSquareCouplingStep} →
  {threshold : InverseSquareThresholdControlsCoupling K γ step} →
  (budget : BalabanBetaPrefixBound K step threshold) →
  ∀ k → k ≤ K →
  gammaInverseSquare threshold ≤ℝ inverseSquaredCoupling step k
inverseSquareAboveGammaThreshold′ arith order {step = step}
  {threshold = threshold} budget k k≤K =
  ≤-replace-right arith
    (≤ℝ-trans
      (addBudgetImpliesSubBudget order
        (BalabanBetaPrefixBound.bareCouplingBudget budget k k≤K))
      (subtract-right-antitone arith
        (BalabanBetaPrefixBound.betaPrefixControlled budget k k≤K)))
    (sym (inverseSquareTelescoping arith step k))

couplingTrajectoryBoundedByGamma :
  (arith : InverseSquareBudgetArithmetic) →
  (order : InverseSquareBudgetOrderBridge) →
  {K : ℕ} →
  {γ : ℝ} →
  {step : BalabanInverseSquareCouplingStep} →
  (threshold : InverseSquareThresholdControlsCoupling K γ step) →
  (budget : BalabanBetaPrefixBound K step threshold) →
  CouplingTrajectoryBoundedBy γ step
couplingTrajectoryBoundedByGamma arith order {K} threshold budget =
  record
    { terminalScale = K
    ; γ-positive = γ-positive threshold
    ; staysPositiveAndSmall = λ k k≤K →
        thresholdControlsCoupling threshold k k≤K
          (inverseSquareAboveGammaThreshold′ arith order budget k k≤K)
    }

-- A continuum construction tunes the bare coordinate with the ultraviolet
-- cutoff.  This record deliberately records that family without choosing a
-- counterterm, a β-expansion, or a limiting topology.  Its `betaBudget` field
-- is the single finite-cutoff theorem that must eventually be inhabited.
record BalabanBareCouplingSchedule : Set₁ where
  field
    γ : ℝ
    γ-positive : 0ℝ <ℝ γ
    bareCoupling : ℕ → ℝ
    trajectory : (K : ℕ) → BalabanInverseSquareCouplingStep

    startsAtBareCoupling :
      ∀ K →
      coupling (trajectory K) zero ≡ bareCoupling K

    threshold :
      ∀ K →
      InverseSquareThresholdControlsCoupling K γ (trajectory K)

    betaBudget :
      ∀ K →
      BalabanBetaPrefixBound K (trajectory K) (threshold K)

    -- These are deliberately named future obligations.  They are not used by
    -- the finite-cutoff CMP 122 implication below.
    terminalRenormalisationCondition : Set
    ultravioletBareCouplingSmallness : Set

    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    noClayPromotion : clayYangMillsPromoted ≡ false

open BalabanBareCouplingSchedule public

-- A small bare coupling alone can make the finite-cutoff premise vacuous.
-- This wrapper records the minimum renormalisation guard needed by the RG
-- lane: a positive, cutoff-uniform physical coupling window at the source's
-- chosen observation scale.  It deliberately does not claim nontriviality.
record RenormalisedBalabanBareCouplingSchedule : Set₁ where
  field
    schedule : BalabanBareCouplingSchedule

    renormalisedCouplingLower : ℝ
    renormalisedCouplingUpper : ℝ
    lowerPositive : 0ℝ <ℝ renormalisedCouplingLower

    -- A source construction may renormalise at a fixed physical scale rather
    -- than literally at the ultraviolet cutoff.  The observation scale is
    -- therefore explicit and must lie within the finite trajectory.
    observationScale : ℕ → ℕ
    observationWithinCutoff :
      ∀ K → observationScale K ≤ K

    terminalCouplingWindow :
      ∀ K →
      renormalisedCouplingLower ≤ℝ
        coupling (trajectory schedule K) (observationScale K)
      ×
      coupling (trajectory schedule K) (observationScale K)
        ≤ℝ renormalisedCouplingUpper

    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    noClayPromotion : clayYangMillsPromoted ≡ false

open RenormalisedBalabanBareCouplingSchedule public

scheduleTrajectoryBoundedByGamma :
  (arith : InverseSquareBudgetArithmetic) →
  (order : InverseSquareBudgetOrderBridge) →
  (schedule : BalabanBareCouplingSchedule) →
  ∀ K →
  CouplingTrajectoryBoundedBy (γ schedule) (trajectory schedule K)
scheduleTrajectoryBoundedByGamma arith order schedule K =
  couplingTrajectoryBoundedByGamma arith order
    (threshold schedule K)
    (betaBudget schedule K)

-- This remains unavailable until a source-backed or owned prefix estimate,
-- bare schedule, coordinate bridge, and elementary ordered-field witness are
-- supplied.  It is intentionally not a paper import.
finiteCutoffBetaBudgetAvailable : Set
finiteCutoffBetaBudgetAvailable = ⊥

currentFiniteCutoffBetaBudgetStatus : VerificationStatus
currentFiniteCutoffBetaBudgetStatus = openTarget
