module DASHI.Core.FeministRechartingSourceBridgeExact where

------------------------------------------------------------------------
-- SOURCE-ATTRIBUTED FEMINIST RECHARTING BRIDGE
--
-- This file does not collapse distinct feminist projects into one doctrine.
-- It records bounded source roles for the representation move discussed in the
-- supplied DASHI reconstruction, then points that discussion at the generic
-- theorem already owned by IntersectionalNonFactorability:
--
--   if a coarse chart has erased a distinction, arbitrary post-composition /
--   relabelling of that chart cannot reconstruct the erased phenomenon.
--
-- SOURCES
--
-- Luce Irigaray, "This Sex Which Is Not One", Cornell University Press, 1985
-- English edition. ISBN 9780801493317.  Used here as source context for the
-- critique of a representational economy whose privileged coordinates already
-- render the feminine through a masculine/phallocentric measure.
--
-- Helene Cixous, "The Laugh of the Medusa", Signs 1(4) (1976), 875--893.
-- DOI: 10.1086/493306.  Used here as source context for generative expressive
-- practice rather than mere occupancy of an inherited discursive slot.
--
-- Audre Lorde, "Uses of the Erotic: The Erotic as Power", Out & Out Books,
-- 1978. ISBN 9780918314093.  A later anthology chapter is available as DOI
-- 10.1093/oso/9780198782506.003.0032.  Used here as source context for a
-- positive endogenous capacity/power reading rather than deficiency alone.
--
-- Monique Wittig, "One Is Not Born a Woman", Feminist Issues 1(2) (1981),
-- 47--54.  Stable original bibliographic record retained; a later Oxford
-- anthology chapter has DOI 10.1093/oso/9780192892706.003.0036.  Used here as
-- source context for challenging the category-producing social relation.
--
-- These source roles motivate, but do not themselves prove, the DASHI theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF

------------------------------------------------------------------------
-- Typed source roles keep the theories distinct.
------------------------------------------------------------------------

data RechartingSourceRole : Set where
  phallocentricChartCritique
  generativeExpression
  positiveEndogenousPower
  categoryRelationCritique
  : RechartingSourceRole

record RechartingSource : Set where
  constructor recharting-source
  field
    author : String
    title : String
    stableIdentifier : String
    sourceRole : RechartingSourceRole

open RechartingSource public

irigaraySource : RechartingSource
irigaraySource =
  recharting-source
    "Luce Irigaray"
    "This Sex Which Is Not One"
    "ISBN 9780801493317"
    phallocentricChartCritique

cixousSource : RechartingSource
cixousSource =
  recharting-source
    "Helene Cixous"
    "The Laugh of the Medusa"
    "DOI 10.1086/493306"
    generativeExpression

lordeSource : RechartingSource
lordeSource =
  recharting-source
    "Audre Lorde"
    "Uses of the Erotic: The Erotic as Power"
    "ISBN 9780918314093; later anthology DOI 10.1093/oso/9780198782506.003.0032"
    positiveEndogenousPower

wittigSource : RechartingSource
wittigSource =
  recharting-source
    "Monique Wittig"
    "One Is Not Born a Woman"
    "Feminist Issues 1(2), 47-54; later anthology DOI 10.1093/oso/9780192892706.003.0036"
    categoryRelationCritique

------------------------------------------------------------------------
-- Mathematical bridge.
------------------------------------------------------------------------

mereRechartingCannotRecover :
  ∀ {Situated Flat Recharted Outcome : Set}
    {flatten : Situated → Flat}
    {phenomenon : Situated → Outcome} →
  (rechart : Flat → Recharted) →
  INF.NonFactorabilityWitness flatten phenomenon →
  INF.FactorsThrough (λ state → rechart (flatten state)) phenomenon →
  ⊥
mereRechartingCannotRecover =
  INF.rechartingCannotRecoverErasedPhenomenon

------------------------------------------------------------------------
-- A positive repair is therefore typed as *adding a residual observer*, not as
-- a claim that any specific feminist theory uniquely determines that residual.
------------------------------------------------------------------------

record PositiveRecharting
    {Situated Flat Residual : Set}
    (flatten : Situated → Flat) : Set₁ where
  constructor positive-recharting
  field
    residual : Situated → Residual

open PositiveRecharting public

record FeministRechartingBoundary : Set where
  constructor feminist-recharting-boundary
  field
    allFourSourcesAssertSameTheory : Bool
    allFourSourcesAssertSameTheoryIsFalse :
      allFourSourcesAssertSameTheory ≡ false
    feministTheoryProvedByNonFactorabilityTheorem : Bool
    feministTheoryProvedByNonFactorabilityTheoremIsFalse :
      feministTheoryProvedByNonFactorabilityTheorem ≡ false
    signFlipInsideCollapsedChartRecoversErasedStructure : Bool
    signFlipInsideCollapsedChartRecoversErasedStructureIsFalse :
      signFlipInsideCollapsedChartRecoversErasedStructure ≡ false
    positiveResidualUniquelySpecifiedBySources : Bool
    positiveResidualUniquelySpecifiedBySourcesIsFalse :
      positiveResidualUniquelySpecifiedBySources ≡ false

canonicalFeministRechartingBoundary : FeministRechartingBoundary
canonicalFeministRechartingBoundary =
  feminist-recharting-boundary
    false refl
    false refl
    false refl
    false refl
