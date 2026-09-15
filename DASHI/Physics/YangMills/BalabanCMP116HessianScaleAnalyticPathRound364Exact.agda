module DASHI.Physics.YangMills.BalabanCMP116HessianScaleAnalyticPathRound364Exact where

------------------------------------------------------------------------
-- ROUND364 / H_scale ALTERNATE PRODUCER: ANALYTIC PATH, NOT MARKED SUM SCALE
--
-- R353 reaches the source Hessian stability theorem through the marked-walk
-- route
--
--   Hdiff <= M_Hessian <= L_src * d_sub_src.
--
-- After R360--R363 most of the construction of M_Hessian has become source
-- replay / same-object attachment.  The surviving R353 field H_scale is the
-- scalar comparison
--
--   M_Hessian <= L_src * d_sub_src.
--
-- CMP116, however, also gives a logically different route.  The substituted
-- background is analytic on the declared common domain, and finite further
-- derivatives retain Cauchy bounds.  Standard mean-value/FTC reasoning then
-- gives a local Hessian Lipschitz estimate provided the SAME substituted-
-- background segment stays in that domain and a uniform bound on the next
-- derivative is available on that segment.
--
-- This owner does NOT claim those physical/source inputs.  It only separates
-- them from the generic calculus transport and compiles them directly into
-- the R352 source ABI.  Hence R353 H_scale is no longer architecturally
-- mandatory: it is one producer, while the analytic-path route below is an
-- alternate producer whose source cost must be compared honestly.
--
-- Primary source context:
--   T. Balaban, "Renormalization Group Approach to Lattice Gauge Field
--   Theories II. Cluster Expansions", CMP 116 (1988), 1--22.
--   DOI: 10.1007/BF01239022.
-- Sect. 1 constructs the substituted background analytically on the common
-- domain; (1.18)--(1.21) give uniform bounds and the later differentiated
-- localization uses Cauchy estimates.  Source analyticity is not itself an
-- inhabitant of the concrete segment/derivative fields below.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; absℝ; _-ℝ_; _*ℝ_; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as CMP116
import DASHI.Physics.YangMills.BalabanSelectedHessianStabilitySourceRound352Exact as R352
import DASHI.Physics.YangMills.BalabanSelectedHessianWalkResummationCutRound353Exact as R353

------------------------------------------------------------------------
-- Generic calculus authority.
--
-- `DerivativeBound` deliberately stays abstract: an application may realize it
-- by a third field derivative, a Fréchet derivative of the Hessian map, or an
-- equivalent same-carrier source theorem.  The only generic conclusion consumed
-- downstream is endpoint Lipschitz control.
------------------------------------------------------------------------

record ScalarMeanValueLipschitzAuthority : Set₂ where
  field
    State : Set
    distance : State → State → ℝ
    AdmissibleSegment : State → State → Set
    DerivativeBound : (State → ℝ) → ℝ → State → State → Set

    endpointDifferenceBound :
      ∀ (f : State → ℝ) L left right →
      AdmissibleSegment left right →
      DerivativeBound f L left right →
      absℝ (f left -ℝ f right) ≤ℝ L *ℝ distance left right

open ScalarMeanValueLipschitzAuthority public

------------------------------------------------------------------------
-- Literal CMP116 application data for the alternate producer.
------------------------------------------------------------------------

record CMP116SubstitutedHessianAnalyticPathData
    (calculus : ScalarMeanValueLipschitzAuthority) : Set₁ where
  field
    leftSubstituted rightSubstituted : State calculus
    sourceHessian : State calculus → ℝ
    sourceLipschitz : ℝ

    -- Same-carrier source/application payments.
    substitutedSegmentAdmissible :
      AdmissibleSegment calculus leftSubstituted rightSubstituted

    sourceHessianDerivativeBound :
      DerivativeBound calculus sourceHessian sourceLipschitz
        leftSubstituted rightSubstituted

open CMP116SubstitutedHessianAnalyticPathData public

sourceSubstitutionDistanceFromPath :
  (calculus : ScalarMeanValueLipschitzAuthority) →
  CMP116SubstitutedHessianAnalyticPathData calculus →
  ℝ
sourceSubstitutionDistanceFromPath calculus dataSet =
  distance calculus
    (leftSubstituted dataSet) (rightSubstituted dataSet)

sourceHessianDifferenceFromPath :
  (calculus : ScalarMeanValueLipschitzAuthority) →
  CMP116SubstitutedHessianAnalyticPathData calculus →
  ℝ
sourceHessianDifferenceFromPath calculus dataSet =
  absℝ
    (sourceHessian dataSet (leftSubstituted dataSet)
      -ℝ sourceHessian dataSet (rightSubstituted dataSet))

analyticPathPaysSourceHessianStability :
  (calculus : ScalarMeanValueLipschitzAuthority) →
  (dataSet : CMP116SubstitutedHessianAnalyticPathData calculus) →
  sourceHessianDifferenceFromPath calculus dataSet
    ≤ℝ sourceLipschitz dataSet
      *ℝ sourceSubstitutionDistanceFromPath calculus dataSet
analyticPathPaysSourceHessianStability calculus dataSet =
  endpointDifferenceBound calculus
    (sourceHessian dataSet)
    (sourceLipschitz dataSet)
    (leftSubstituted dataSet)
    (rightSubstituted dataSet)
    (substitutedSegmentAdmissible dataSet)
    (sourceHessianDerivativeBound dataSet)

------------------------------------------------------------------------
-- Compile directly into the existing R352 source theorem ABI.
------------------------------------------------------------------------

analyticPathToR352Source :
  (calculus : ScalarMeanValueLipschitzAuthority) →
  (dataSet : CMP116SubstitutedHessianAnalyticPathData calculus) →
  R352.CMP116LocalHessianStabilitySource ⊤
analyticPathToR352Source calculus dataSet = record
  { R352.CMP116LocalHessianStabilitySource.sourceHessianDifference =
      λ _ → sourceHessianDifferenceFromPath calculus dataSet
  ; R352.CMP116LocalHessianStabilitySource.sourceLipschitz =
      sourceLipschitz dataSet
  ; R352.CMP116LocalHessianStabilitySource.sourceSubstitutionDistance =
      λ _ → sourceSubstitutionDistanceFromPath calculus dataSet
  ; R352.CMP116LocalHessianStabilitySource.sourceHessianStable =
      λ _ → analyticPathPaysSourceHessianStability calculus dataSet
  }

------------------------------------------------------------------------
-- Pareto / authority accounting.
------------------------------------------------------------------------

-- Standard real/Banach mean-value or FTC-to-Lipschitz mathematics.  The record
-- above remains proof-bearing; this status does not manufacture an inhabitant.
meanValueLipschitzAuthorityLevel : ProofLevel
meanValueLipschitzAuthorityLevel = standardImported

-- CMP116 source authority for analyticity and preservation of finite declared
-- derivatives under Cauchy estimates.  This still does not instantiate the
-- exact physical path or its quantitative derivative constant.
cmp116FiniteDerivativeCauchyAuthorityLevel : ProofLevel
cmp116FiniteDerivativeCauchyAuthorityLevel =
  CMP116.finitePolydiscCauchyDerivativePreservesExternalMajorantLevel

-- Physical/source payments for the alternate route.
literalCMP116SubstitutedBackgroundSegmentLevel : ProofLevel
literalCMP116SubstitutedBackgroundSegmentLevel = conditional

literalCMP116UniformHessianDerivativeBoundLevel : ProofLevel
literalCMP116UniformHessianDerivativeBoundLevel = conditional

analyticPathToR352CompilerLevel : ProofLevel
analyticPathToR352CompilerLevel = machineChecked

-- R353 remains a valid marked-walk producer.  It is simply not mandatory if
-- this analytic-path producer is cheaper on the exact source carrier.
round353MarkedMajorantScaleComparisonArchitecturallyMandatory : Bool
round353MarkedMajorantScaleComparisonArchitecturallyMandatory = false

round353MarkedMajorantScaleComparisonArchitecturallyMandatoryIsFalse :
  round353MarkedMajorantScaleComparisonArchitecturallyMandatory ≡ false
round353MarkedMajorantScaleComparisonArchitecturallyMandatoryIsFalse = refl

analyticPathAutomaticallyCheaperThanMarkedWalkRoute : Bool
analyticPathAutomaticallyCheaperThanMarkedWalkRoute = false

analyticPathAutomaticallyCheaperThanMarkedWalkRouteIsFalse :
  analyticPathAutomaticallyCheaperThanMarkedWalkRoute ≡ false
analyticPathAutomaticallyCheaperThanMarkedWalkRouteIsFalse = refl

record Round364Boundary : Set where
  constructor round364-boundary
  field
    genericMeanValueMathIsNotNewYM : Bool
    genericMeanValueMathIsNotNewYMIsTrue :
      genericMeanValueMathIsNotNewYM ≡ true

    exactSubstitutedSegmentStillSourceSpecific : Bool
    exactSubstitutedSegmentStillSourceSpecificIsTrue :
      exactSubstitutedSegmentStillSourceSpecific ≡ true

    uniformHessianDerivativeBoundStillSourceSpecific : Bool
    uniformHessianDerivativeBoundStillSourceSpecificIsTrue :
      uniformHessianDerivativeBoundStillSourceSpecific ≡ true

    markedWalkRouteRemainsAvailable : Bool
    markedWalkRouteRemainsAvailableIsTrue :
      markedWalkRouteRemainsAvailable ≡ true

canonicalRound364Boundary : Round364Boundary
canonicalRound364Boundary =
  round364-boundary true refl true refl true refl true refl

round364FrontierRefinementLevel : ProofLevel
round364FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
