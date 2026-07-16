module DASHI.Physics.YangMills.BalabanBetaTubeAndRenormalisation where

-- One optional sufficient producer for the remaining finite-cutoff RG
-- theorem.  CMP 109 Theorem 2 itself only requires the tuned trajectory;
-- contraction is one possible way to construct it, not the canonical
-- theorem boundary.
-- A tube is a family of trajectories generated from varying initial
-- inverse-square coordinates.  The fixed-point fields encode the actual
-- shooting argument; they do not permit an unrelated beta sequence to be
-- paired with a separately chosen bare coupling.

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ; zero; _≤_)
open import Data.Product using (Σ; _,_; _×_)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ ; 0ℝ ; 1ℝ ; _+ℝ_ ; _-ℝ_ ; _*ℝ_ ; _≤ℝ_ ; _<ℝ_ ; absℝ )
open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  ( SourceAuthorityId ; VerificationStatus ; balaban-cmp-109 ; openTarget )
open import DASHI.Physics.YangMills.BalabanCutoffBetaLaw using
  ( BalabanCutoffCouplingDynamics ; step )
open import DASHI.Physics.YangMills.BalabanEffectiveCouplingTrajectory using
  ( coupling ; inverseSquaredCoupling )
open import DASHI.Physics.YangMills.BalabanInverseSquareCouplingBudget using
  ( InverseSquareThresholdControlsCoupling
  ; BalabanBetaPrefixBound
  ; betaPrefixSum
  )
open import DASHI.Physics.YangMills.BalabanBetaPrefixEstimate using
  ( BalabanActualBetaPrefixEstimate )
open import DASHI.Physics.YangMills.BalabanRenormalisedCouplingExistence using
  ( BalabanRenormalisedCouplingConstruction )

record BalabanBetaTubeEstimate (K : ℕ) (γ : ℝ) : Set₁ where
  field
    -- Points are initial inverse-square coordinates in the analytic tube.
    TubePoint : Set
    initialInverseSquare : TubePoint → ℝ
    dynamicsAt : TubePoint → BalabanCutoffCouplingDynamics K
    initialCoordinate :
      ∀ u →
      inverseSquaredCoupling (step (dynamicsAt u)) zero
        ≡ initialInverseSquare u

    thresholdAt :
      ∀ u →
      InverseSquareThresholdControlsCoupling K γ (step (dynamicsAt u))

    observationScale : ℕ
    observationWithinCutoff : observationScale ≤ K
    renormalisedInverseSquare : ℝ

    -- T_K(u) = u_R + sum of the path-dependent source beta corrections
    -- along the generated trajectory from u.
    renormalisationMap : TubePoint → TubePoint
    mapHasSourceFormula :
      ∀ u →
      initialInverseSquare (renormalisationMap u)
        ≡
      renormalisedInverseSquare +ℝ
        betaPrefixSum (step (dynamicsAt u)) observationScale

    contractionFactor : ℝ
    contractionFactorNonnegative : 0ℝ ≤ℝ contractionFactor
    contractionFactorStrict : contractionFactor <ℝ 1ℝ
    observationMapContraction :
      ∀ u v →
      absℝ
        (initialInverseSquare (renormalisationMap u)
          -ℝ initialInverseSquare (renormalisationMap v))
        ≤ℝ
      contractionFactor *ℝ
        absℝ (initialInverseSquare u -ℝ initialInverseSquare v)

    -- This is the Banach fixed-point conclusion in the exact source tube.
    -- It remains a named analytic obligation until the finite-lattice
    -- fluctuation calculation and a complete-metric theorem inhabit it.
    fixedPoint : Σ TubePoint λ u → renormalisationMap u ≡ u
    fixedPointObservationCondition :
      inverseSquaredCoupling
        (step (dynamicsAt (Σ.proj₁ fixedPoint)))
        observationScale
        ≡ renormalisedInverseSquare

    prefixMajorant : ℕ → ℝ
    prefixControlled :
      ∀ u k → k ≤ K →
      betaPrefixSum (step (dynamicsAt u)) k ≤ℝ prefixMajorant k

    -- This is deliberately a budget on the selected fixed trajectory, not
    -- on an arbitrary auxiliary one.
    fixedPointBareBudget :
      ∀ k → k ≤ K →
      InverseSquareThresholdControlsCoupling.gammaInverseSquare
        (thresholdAt (Σ.proj₁ fixedPoint))
        +ℝ prefixMajorant k
        ≤ℝ inverseSquaredCoupling
          (step (dynamicsAt (Σ.proj₁ fixedPoint)))
          zero

    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    noClayPromotion : clayYangMillsPromoted ≡ false

open BalabanBetaTubeEstimate public

betaTubePrefixEstimate :
  ∀ {K γ} →
  (tube : BalabanBetaTubeEstimate K γ) →
  BalabanActualBetaPrefixEstimate K
    (dynamicsAt tube (Σ.proj₁ (fixedPoint tube)))
    (thresholdAt tube (Σ.proj₁ (fixedPoint tube)))
betaTubePrefixEstimate tube = record
  { prefixBudget = record
      { prefixMajorant = prefixMajorant tube
      ; betaPrefixControlled =
          λ k k≤K → prefixControlled tube (Σ.proj₁ (fixedPoint tube)) k k≤K
      ; bareCouplingBudget = fixedPointBareBudget tube
      ; sourceAuthorityId = sourceAuthorityId tube
      ; theoremLocator = theoremLocator tube
      ; status = status tube
      ; noClayPromotion = noClayPromotion tube
      }
  ; sourceAuthorityId = sourceAuthorityId tube
  ; theoremLocator = theoremLocator tube
  ; status = status tube
  ; noClayPromotion = noClayPromotion tube
  }

-- A family of exact tube estimates supplies the pre-existing renormalised
-- schedule target.  The physical coupling window is stated separately from
-- the inverse-square observation condition: both are needed to exclude a
-- vacuous g -> 0 construction.
record BalabanBetaTubeAndRenormalisation : Set₁ where
  field
    γ : ℝ
    γ-positive : 0ℝ <ℝ γ
    tubeAt : (K : ℕ) → BalabanBetaTubeEstimate K γ

    renormalisedCouplingLower : ℝ
    renormalisedCouplingUpper : ℝ
    lowerPositive : 0ℝ <ℝ renormalisedCouplingLower
    fixedPointCouplingWindow :
      ∀ K →
      renormalisedCouplingLower ≤ℝ
        coupling
          (step (dynamicsAt (tubeAt K) (Σ.proj₁ (fixedPoint (tubeAt K)))))
          (observationScale (tubeAt K))
      ×
      coupling
        (step (dynamicsAt (tubeAt K) (Σ.proj₁ (fixedPoint (tubeAt K)))))
        (observationScale (tubeAt K))
        ≤ℝ renormalisedCouplingUpper

    terminalRenormalisationCondition : Set
    ultravioletBareCouplingSmallness : Set
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    noClayPromotion : clayYangMillsPromoted ≡ false

open BalabanBetaTubeAndRenormalisation public

betaTubeToRenormalisedConstruction :
  BalabanBetaTubeAndRenormalisation →
  BalabanRenormalisedCouplingConstruction
betaTubeToRenormalisedConstruction tube = record
  { γ = γ tube
  ; γ-positive = γ-positive tube
  ; bareCoupling = λ K →
      coupling
        (step (dynamicsAt (tubeAt tube K)
          (Σ.proj₁ (fixedPoint (tubeAt tube K)))))
        zero
  ; dynamics = λ K →
      dynamicsAt (tubeAt tube K) (Σ.proj₁ (fixedPoint (tubeAt tube K)))
  ; startsAtBareCoupling = λ K → refl
  ; threshold = λ K →
      thresholdAt (tubeAt tube K) (Σ.proj₁ (fixedPoint (tubeAt tube K)))
  ; actualPrefixEstimate = λ K → betaTubePrefixEstimate (tubeAt tube K)
  ; renormalisedCouplingLower = renormalisedCouplingLower tube
  ; renormalisedCouplingUpper = renormalisedCouplingUpper tube
  ; lowerPositive = lowerPositive tube
  ; observationScale = λ K → observationScale (tubeAt tube K)
  ; observationWithinCutoff = λ K → observationWithinCutoff (tubeAt tube K)
  ; terminalCouplingWindow = fixedPointCouplingWindow tube
  ; terminalRenormalisationCondition = terminalRenormalisationCondition tube
  ; ultravioletBareCouplingSmallness = ultravioletBareCouplingSmallness tube
  ; sourceAuthorityId = sourceAuthorityId tube
  ; theoremLocator = theoremLocator tube
  ; status = status tube
  ; noClayPromotion = noClayPromotion tube
  }

actualBalabanBetaTubeAndRenormalisationAvailable : Set
actualBalabanBetaTubeAndRenormalisationAvailable = ⊥

currentBalabanBetaTubeAndRenormalisationStatus : VerificationStatus
currentBalabanBetaTubeAndRenormalisationStatus = openTarget
