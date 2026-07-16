module DASHI.Physics.YangMills.BalabanRenormalisedCouplingExistence where

-- Assembly surface for the one substantive finite-cutoff RG theorem.  A
-- successful inhabitant must supply the generated history-dependent beta
-- dynamics, its one-sided prefix budget, and a nonvanishing observation-scale
-- window together.
-- It cannot close the CMP 122 premise merely by choosing a rapidly vanishing
-- bare coupling independently of the beta calculation.

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base using (ℕ; zero; _≤_)
open import Data.Product using (_×_)
open import Data.Empty using (⊥)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _≤ℝ_; _<ℝ_)
open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  ( SourceAuthorityId ; VerificationStatus ; openTarget )
open import DASHI.Physics.YangMills.BalabanCutoffBetaLaw using
  ( BalabanCutoffCouplingDynamics ; step )
open import DASHI.Physics.YangMills.BalabanBetaPrefixEstimate using
  ( BalabanActualBetaPrefixEstimate ; prefixBudget )
open import DASHI.Physics.YangMills.BalabanEffectiveCouplingTrajectory using
  ( coupling )
open import DASHI.Physics.YangMills.BalabanInverseSquareCouplingBudget using
  ( InverseSquareThresholdControlsCoupling
  ; BalabanBareCouplingSchedule
  ; RenormalisedBalabanBareCouplingSchedule
  )

record BalabanRenormalisedCouplingConstruction : Set₁ where
  field
    γ : ℝ
    γ-positive : 0ℝ <ℝ γ

    bareCoupling : ℕ → ℝ
    dynamics : (K : ℕ) → BalabanCutoffCouplingDynamics K

    startsAtBareCoupling :
      ∀ K → coupling (step (dynamics K)) zero ≡ bareCoupling K

    threshold :
      ∀ K → InverseSquareThresholdControlsCoupling K γ (step (dynamics K))

    actualPrefixEstimate :
      ∀ K → BalabanActualBetaPrefixEstimate K (dynamics K) (threshold K)

    -- The following observation-scale fields are the output of the tuning
    -- argument (continuity plus endpoint bracketing in the intended proof).
    -- They prevent a schedule from becoming physically vacuous.  CMP 109
    -- Theorem 2 is the specialised case observationScale K = K with terminal
    -- coupling equality; this generic surface deliberately also admits a
    -- direct shooting or monotonicity construction at another physical scale.
    renormalisedCouplingLower : ℝ
    renormalisedCouplingUpper : ℝ
    lowerPositive : 0ℝ <ℝ renormalisedCouplingLower
    observationScale : ℕ → ℕ
    observationWithinCutoff : ∀ K → observationScale K ≤ K
    terminalCouplingWindow :
      ∀ K →
      renormalisedCouplingLower ≤ℝ
        coupling (step (dynamics K)) (observationScale K)
      ×
      coupling (step (dynamics K)) (observationScale K)
        ≤ℝ renormalisedCouplingUpper

    -- Retained for the subsequent continuum family.  Neither condition is
    -- consumed by the finite-cutoff arithmetic theorem itself.
    terminalRenormalisationCondition : Set
    ultravioletBareCouplingSmallness : Set

    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    noClayPromotion : clayYangMillsPromoted ≡ false

open BalabanRenormalisedCouplingConstruction public

constructionToBareSchedule :
  BalabanRenormalisedCouplingConstruction →
  BalabanBareCouplingSchedule
constructionToBareSchedule construction = record
  { γ = γ construction
  ; γ-positive = γ-positive construction
  ; bareCoupling = bareCoupling construction
  ; trajectory = λ K → step (dynamics construction K)
  ; startsAtBareCoupling = startsAtBareCoupling construction
  ; threshold = threshold construction
  ; betaBudget = λ K → prefixBudget (actualPrefixEstimate construction K)
  ; terminalRenormalisationCondition =
      terminalRenormalisationCondition construction
  ; ultravioletBareCouplingSmallness =
      ultravioletBareCouplingSmallness construction
  ; sourceAuthorityId = sourceAuthorityId construction
  ; theoremLocator = theoremLocator construction
  ; status = status construction
  ; noClayPromotion = noClayPromotion construction
  }

balabanRenormalisedCouplingConstruction :
  BalabanRenormalisedCouplingConstruction →
  RenormalisedBalabanBareCouplingSchedule
balabanRenormalisedCouplingConstruction construction = record
  { schedule = constructionToBareSchedule construction
  ; renormalisedCouplingLower = renormalisedCouplingLower construction
  ; renormalisedCouplingUpper = renormalisedCouplingUpper construction
  ; lowerPositive = lowerPositive construction
  ; observationScale = observationScale construction
  ; observationWithinCutoff = observationWithinCutoff construction
  ; terminalCouplingWindow = terminalCouplingWindow construction
  ; sourceAuthorityId = sourceAuthorityId construction
  ; theoremLocator = theoremLocator construction
  ; status = status construction
  ; noClayPromotion = noClayPromotion construction
  }

-- The real theorem is an existence proof for this construction from the
-- finite-lattice Balaban transformation.  No published source located so far
-- supplies the exact bound in this coordinate, so the target remains open.
actualBalabanRenormalisedCouplingConstructionAvailable : Set
actualBalabanRenormalisedCouplingConstructionAvailable = ⊥

currentBalabanRenormalisedCouplingConstructionStatus : VerificationStatus
currentBalabanRenormalisedCouplingConstructionStatus = openTarget
