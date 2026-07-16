module DASHI.Physics.YangMills.BalabanVacuumPolarisationDomainTail where

-- CMP 99's generalized random-walk/domain-difference estimate has to be
-- propagated through the CMP 109 polarization diagrams and their weighted
-- coordinate moment.  This is the precise owned bridge; it is deliberately
-- separate from both the coefficient definition and an infinite-volume limit.

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base using (ℕ)
open import Data.List.Base using (List)
open import Data.Empty using (⊥)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ ; 0ℝ ; _-ℝ_ ; _*ℝ_ ; -ℝ_ ; absℝ ; _≤ℝ_ )
open import DASHI.Physics.YangMills.BalabanLargeFieldSuppression using
  ( expℝ ; fromNat )
open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  ( SourceAuthorityId ; VerificationStatus
  ; balaban-cmp-099 ; balaban-cmp-109 ; balaban-cmp-116 ; openTarget )

-- CMP 109 I, (4.37), is the non-negotiable intermediate object:
--
--   Pi_{mu nu}(x,y) = sum_{X in D_j} E^{(2)}_{mu nu}(X;x,y).
--
-- Thus a domain-difference proof cannot compare only a finite collection of
-- algebraic diagram shapes.  It must first mark the CMP 99 (3.154) random-walk
-- difference in every localised contribution and then resum the localisation
-- domains.  This record exposes precisely that missing bridge; its last field
-- is deliberately still an owned analytic theorem, not a paper import.
record BalabanLocalisedPolarisationDomainComparison
    (Domain Background History : Set) : Set₁ where
  field
    Position LocalisationDomain : Set
    anchorPosition : Position
    collarRadius : Domain → Domain → ℕ
    discrepancyDistance : Domain → Domain → Position → Position → ℕ
    localisationDomains : ℕ → Domain → List LocalisationDomain
    localisationTreeLength : LocalisationDomain → ℕ
    positionDistance : Position → Position → ℕ

    localisedPolarisation :
      ℕ → Domain → Background → History → LocalisationDomain →
      Position → Position → ℝ

    spatialConstant spatialRate localisationRate boundaryRate : ℝ
    spatialConstantNonnegative : 0ℝ ≤ℝ spatialConstant
    spatialRateNonnegative : 0ℝ ≤ℝ spatialRate
    localisationRateNonnegative : 0ℝ ≤ℝ localisationRate
    boundaryRateNonnegative : 0ℝ ≤ℝ boundaryRate

    domainsAgreeNearCoefficient : Domain → Domain → Set

    -- This is the termwise output of replacing one CMP 99 propagator or
    -- background derivative at a time in CMP 109's (4.3) expansion.  There,
    -- derivatives of H_j are sums of exponentially decaying tree expressions;
    -- CMP 109 (4.5) is the prototype for the extra factor when a localization
    -- lies outside X.  Its boundary factor is the marked random-walk factor of
    -- CMP 99 (3.154), measured from the two operator localisations to the
    -- domain discrepancy.  It is deliberately *not* replaced here by a
    -- uniform collar factor: that replacement is valid only in the near part
    -- of the later coordinate-moment split.
    markedLocalisedDifference :
      ∀ scale Ω Ω′ U history X x y →
      domainsAgreeNearCoefficient Ω Ω′ →
      absℝ (localisedPolarisation scale Ω U history X x y
          -ℝ localisedPolarisation scale Ω′ U history X x y)
        ≤ℝ
      spatialConstant *ℝ
      expℝ (-ℝ (spatialRate *ℝ fromNat (positionDistance x y))) *ℝ
      expℝ (-ℝ (localisationRate *ℝ fromNat (localisationTreeLength X))) *ℝ
      expℝ (-ℝ (boundaryRate *ℝ fromNat
        (discrepancyDistance Ω Ω′ x y)))

    -- Do not identify these two X-index lists by equality.  A localisation
    -- domain which reaches the discrepancy region can occur on only one side;
    -- its contribution must instead be paid for by the CMP 116 tree-length
    -- weight.  The owned resummation proof uses the dichotomy
    --
    --   marked walk remains in the collar  -> pays discrepancy distance,
    --   localisation reaches the discrepancy -> pays tree length.
    --
    -- In particular, it must retain both exponential costs while summing X.

open BalabanLocalisedPolarisationDomainComparison public

record BalabanVacuumPolarisationDomainTail : Set₁ where
  field
    Domain Background History : Set
    betaAt : ℕ → Domain → Background → History → ℝ

    tailConstant tailRate : ℝ
    tailConstantNonnegative : 0ℝ ≤ℝ tailConstant
    tailRateNonnegative : 0ℝ ≤ℝ tailRate

    -- A source-facing decomposition witness for the route from CMP 99 (3.154)
    -- to the beta moment.  It is optional only because a direct finite-volume
    -- proof may package the same estimates differently; it is never evidence
    -- that the weighted-moment conclusion has already been proved.
    localisedComparison :
      BalabanLocalisedPolarisationDomainComparison Domain Background History

    -- Owned output: CMP 99 (3.154) gives the marked local difference; CMP 116
    -- (1.26), (1.29), and Lemma 3/(2.38) provide the localization summability.
    -- The critical intermediate estimate retains the two costs jointly:
    --
    --   sum_X exp (-delta * markedDistance X) exp (-kappa * treeLength X).
    --
    -- For near positions, a geometric charging lemma makes this at most a
    -- collar-decay factor times a still-summable tree-length weight.  For far
    -- positions, compare the two ordinary spatially decaying kernels instead.
    -- The resulting far coordinate tail is polynomial times exponential and
    -- is bounded by every strictly smaller positive exponential rate.
    weightedMomentDomainDifference :
      ∀ scale Ω Ω′ U history →
      BalabanLocalisedPolarisationDomainComparison.domainsAgreeNearCoefficient
        localisedComparison Ω Ω′ →
      absℝ (betaAt scale Ω U history -ℝ betaAt scale Ω′ U history)
        ≤ℝ
      tailConstant *ℝ expℝ
        (-ℝ (tailRate *ℝ fromNat
          (BalabanLocalisedPolarisationDomainComparison.collarRadius
            localisedComparison Ω Ω′)))

    -- This must eventually state the uniform source scope: scale, ultraviolet
    -- cutoff, finite volume, and every regular background/history tube.
    uniformScope : Set

    operatorDifferenceSourceAuthorityId : SourceAuthorityId
    operatorDifferenceAuthorityIsCMP99 :
      operatorDifferenceSourceAuthorityId ≡ balaban-cmp-099
    polarisationFactorisationSourceAuthorityId : SourceAuthorityId
    polarisationFactorisationAuthorityIsCMP109 :
      polarisationFactorisationSourceAuthorityId ≡ balaban-cmp-109
    localisationResummationSourceAuthorityId : SourceAuthorityId
    localisationResummationAuthorityIsCMP116 :
      localisationResummationSourceAuthorityId ≡ balaban-cmp-116
    theoremLocator : String
    status : VerificationStatus
    noClayPromotion : clayYangMillsPromoted ≡ false

open BalabanVacuumPolarisationDomainTail public

actualBalabanVacuumPolarisationDomainTailAvailable : Set
actualBalabanVacuumPolarisationDomainTailAvailable = ⊥

currentBalabanVacuumPolarisationDomainTailStatus : VerificationStatus
currentBalabanVacuumPolarisationDomainTailStatus = openTarget
