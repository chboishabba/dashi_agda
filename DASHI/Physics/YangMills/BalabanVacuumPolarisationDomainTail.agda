module DASHI.Physics.YangMills.BalabanVacuumPolarisationDomainTail where

-- CMP 99's generalized random-walk/domain-difference estimate has to be
-- propagated through the CMP 109 polarization diagrams and their weighted
-- coordinate moment.  This is the precise owned bridge; it is deliberately
-- separate from both the coefficient definition and an infinite-volume limit.

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base using (ℕ)
open import Data.Empty using (⊥)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ ; 0ℝ ; _-ℝ_ ; _*ℝ_ ; -ℝ_ ; absℝ ; _≤ℝ_ )
open import DASHI.Physics.YangMills.BalabanLargeFieldSuppression using
  ( expℝ ; fromNat )
open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  ( SourceAuthorityId ; VerificationStatus ; balaban-cmp-099 ; openTarget )

record BalabanVacuumPolarisationDomainTail : Set₁ where
  field
    Domain Background History : Set
    agreementRadius : Domain → Domain → ℕ
    betaAt : ℕ → Domain → Background → History → ℝ

    tailConstant tailRate : ℝ
    tailConstantNonnegative : 0ℝ ≤ℝ tailConstant
    tailRateNonnegative : 0ℝ ≤ℝ tailRate

    -- The hypothesis says that the two admissible domain sequences agree on
    -- the source-valid localization neighbourhood encoded by the radius.
    domainsAgreeNearCoefficient : Domain → Domain → Set

    weightedMomentDomainDifference :
      ∀ scale Ω Ω′ U history →
      domainsAgreeNearCoefficient Ω Ω′ →
      absℝ (betaAt scale Ω U history -ℝ betaAt scale Ω′ U history)
        ≤ℝ
      tailConstant *ℝ expℝ
        (-ℝ (tailRate *ℝ fromNat (agreementRadius Ω Ω′)))

    -- This must eventually state the uniform source scope: scale, ultraviolet
    -- cutoff, finite volume, and every regular background/history tube.
    uniformScope : Set

    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    noClayPromotion : clayYangMillsPromoted ≡ false

open BalabanVacuumPolarisationDomainTail public

actualBalabanVacuumPolarisationDomainTailAvailable : Set
actualBalabanVacuumPolarisationDomainTailAvailable = ⊥

currentBalabanVacuumPolarisationDomainTailStatus : VerificationStatus
currentBalabanVacuumPolarisationDomainTailStatus = openTarget
