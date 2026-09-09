{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116SharedFirstVariationCoordinateRound256Exact where

------------------------------------------------------------------------
-- ROUND256 / ONE PHYSICAL FIRST-SUBSTITUTION DIRECTION FEEDS D1 AND ROW C
--
-- Both the first physical variation and the first-gradient Heat/Doob covariance
-- response differentiate the SAME substituted CMP116 activity E(A(B)).  At first
-- order the only substitution direction is
--
--     A'(B) u = firstSubstitutionVariation B u.
--
-- The second-order chain rule reuses that same direction twice and separately
-- adds A''(B)[u,v].  Therefore the first-substitution tangent must be realized
-- once, not independently in D1 and Row C.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityFirstVariationRound105Exact as First
import DASHI.Physics.YangMills.BalabanPreferredD1SemanticsFrontierRound228Exact as D1
import DASHI.Physics.YangMills.BalabanCMP116FirstGradientLocalizationRound255Exact as Grad

record SharedPhysicalFirstSubstitutionCoordinate
    (activity : Chain.SubstitutedActivitySecondVariation) : Set₁ where
  field
    PhysicalTangent : Set

    toBackgroundTangent :
      Chain.Background activity →
      PhysicalTangent →
      Chain.BackgroundTangent activity

    -- This field is the literal source/repository coordinate weld.  Consumers
    -- use the RHS directly; no second first-order substitution map is allowed.
    physicalTangentIsFirstSubstitutionDirection : Set

open SharedPhysicalFirstSubstitutionCoordinate public

-- The first-order chain-rule value itself is already compiler-owned once the
-- shared background tangent is selected.
sharedSubstitutedFirstVariation :
  ∀ {activity} →
  SharedPhysicalFirstSubstitutionCoordinate activity →
  Chain.Background activity →
  PhysicalTangent _ →
  DASHI.Foundations.RealAnalysisAxioms.ℝ
sharedSubstitutedFirstVariation {activity} coordinate background tangent =
  First.substitutedFirstVariation activity background
    (toBackgroundTangent coordinate background tangent)

sharedFirstVariationCompilerLevel : ProofLevel
sharedFirstVariationCompilerLevel = First.cmp116SubstitutedFirstVariationCompilerLevel

-- Existing D1 source seam: identify the consumer tangent with the literal
-- first substitution derivative.  This is the same coordinate realization used
-- by the first-gradient Cauchy/localization route below.
literalSharedFirstSubstitutionCoordinateLevel : ProofLevel
literalSharedFirstSubstitutionCoordinateLevel =
  D1.literalCMP116SubstitutionTangentIdentificationLevel

-- First-gradient localization is standard CMP116 finite-derivative reuse once
-- that coordinate and the common analytic radius are fixed.
sharedFirstGradientLocalizationSourceLevel : ProofLevel
sharedFirstGradientLocalizationSourceLevel =
  Grad.cmp116FirstGradientLocalizationSourceLevel
