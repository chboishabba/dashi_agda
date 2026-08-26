module DASHI.Core.IntersectionalNonFactorability where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym; trans)

------------------------------------------------------------------------
-- INTERSECTIONAL NON-FACTORABILITY
--
-- Reference / conceptual motivation:
--   Kimberle Crenshaw,
--   "Mapping the Margins: Intersectionality, Identity Politics, and Violence
--   against Women of Color", Stanford Law Review 43(6), 1241-1299 (1991).
--   DOI: 10.2307/1229039.
--
-- Crenshaw's structural/political intersectionality motivates the warning that
-- single-axis frames can fail to represent situated phenomena.  The
-- factorisation criterion below is a DASHI mathematical translation, not a
-- theorem attributed to Crenshaw.
--
-- The recharting theorem added below is also generic DASHI mathematics.  It
-- formalises a representation-theoretic point used in the supplied 2026-08-27
-- discussion: once two situated states have already collided under a coarse
-- observer, post-composing that observer with a relabelling/reweighting/chart
-- map cannot recover a phenomenon that distinguishes those states.  A richer
-- observer must add information rather than merely rename the old quotient.
------------------------------------------------------------------------

record FactorsThrough
    {Situated Flat Outcome : Set}
    (flatten : Situated → Flat)
    (phenomenon : Situated → Outcome) : Set₁ where
  constructor factorsThrough
  field
    interpretFlat : Flat → Outcome
    factorisation :
      (state : Situated) →
      phenomenon state ≡ interpretFlat (flatten state)

open FactorsThrough public

record NonFactorabilityWitness
    {Situated Flat Outcome : Set}
    (flatten : Situated → Flat)
    (phenomenon : Situated → Outcome) : Set₁ where
  constructor nonFactorabilityWitness
  field
    left right : Situated
    sameFlatProjection : flatten left ≡ flatten right
    situatedOutcomesDiffer : phenomenon left ≡ phenomenon right → ⊥

open NonFactorabilityWitness public

witnessRulesOutEveryFlatFactorisation :
  ∀ {Situated Flat Outcome}
    {flatten : Situated → Flat}
    {phenomenon : Situated → Outcome} →
  NonFactorabilityWitness flatten phenomenon →
  FactorsThrough flatten phenomenon →
  ⊥
witnessRulesOutEveryFlatFactorisation witness factor =
  situatedOutcomesDiffer witness
    (trans
      (factorisation factor (left witness))
      (trans
        (cong (interpretFlat factor) (sameFlatProjection witness))
        (sym (factorisation factor (right witness)))))

------------------------------------------------------------------------
-- Recharting/post-composition cannot recover information erased by `flatten`.
-- This is stronger than a statement about permutations: the post-map may be
-- any function whatsoever.  If the original observer identifies the witness
-- pair, every observer factoring through it identifies that pair as well.
------------------------------------------------------------------------

postcomposeNonFactorability :
  ∀ {Situated Flat Recharted Outcome}
    {flatten : Situated → Flat}
    {phenomenon : Situated → Outcome} →
  (rechart : Flat → Recharted) →
  NonFactorabilityWitness flatten phenomenon →
  NonFactorabilityWitness (λ state → rechart (flatten state)) phenomenon
postcomposeNonFactorability rechart witness =
  nonFactorabilityWitness
    (left witness)
    (right witness)
    (cong rechart (sameFlatProjection witness))
    (situatedOutcomesDiffer witness)

rechartingCannotRecoverErasedPhenomenon :
  ∀ {Situated Flat Recharted Outcome}
    {flatten : Situated → Flat}
    {phenomenon : Situated → Outcome} →
  (rechart : Flat → Recharted) →
  NonFactorabilityWitness flatten phenomenon →
  FactorsThrough (λ state → rechart (flatten state)) phenomenon →
  ⊥
rechartingCannotRecoverErasedPhenomenon rechart witness =
  witnessRulesOutEveryFlatFactorisation
    (postcomposeNonFactorability rechart witness)

------------------------------------------------------------------------
-- Concrete carrier-repair witness.
--
-- Two situated states share exactly the same flat single-axis label but differ
-- on the relevant relational/institutional phenomenon.  Therefore no change of
-- weights or interpretation *inside that flat carrier* can recover the outcome.
------------------------------------------------------------------------

data SituatedState : Set where
  sameLabelLowPower sameLabelHighPower : SituatedState

data FlatSingleAxis : Set where
  sameDemographicLabel : FlatSingleAxis

flatProjection : SituatedState → FlatSingleAxis
flatProjection sameLabelLowPower = sameDemographicLabel
flatProjection sameLabelHighPower = sameDemographicLabel

relationalOutcome : SituatedState → Bool
relationalOutcome sameLabelLowPower = false
relationalOutcome sameLabelHighPower = true

relationalOutcomeDiffers :
  relationalOutcome sameLabelLowPower ≡
  relationalOutcome sameLabelHighPower → ⊥
relationalOutcomeDiffers ()

canonicalIntersectionalNonFactorability :
  NonFactorabilityWitness flatProjection relationalOutcome
canonicalIntersectionalNonFactorability =
  nonFactorabilityWitness
    sameLabelLowPower
    sameLabelHighPower
    refl
    relationalOutcomeDiffers

flatReweightingCannotRepairMissingRelation :
  FactorsThrough flatProjection relationalOutcome → ⊥
flatReweightingCannotRepairMissingRelation =
  witnessRulesOutEveryFlatFactorisation canonicalIntersectionalNonFactorability

canonicalRechartingCannotRepairMissingRelation :
  ∀ {Recharted : Set} →
  (rechart : FlatSingleAxis → Recharted) →
  FactorsThrough (λ state → rechart (flatProjection state)) relationalOutcome →
  ⊥
canonicalRechartingCannotRepairMissingRelation rechart =
  rechartingCannotRecoverErasedPhenomenon
    rechart canonicalIntersectionalNonFactorability

------------------------------------------------------------------------
-- Product-of-single-axis readings are not automatically intersectional.
-- This no-promotion boundary prevents two separately useful consumer surfaces
-- from being promoted to a sufficient situated-intersectional carrier without
-- an application-supplied factorisation witness.
------------------------------------------------------------------------

data SeparateAxisSufficiencyImpliesIntersectionalSufficiencyPermission : Set where

separateAxisSufficiencyCannotAutoPromote :
  SeparateAxisSufficiencyImpliesIntersectionalSufficiencyPermission → ⊥
separateAxisSufficiencyCannotAutoPromote ()
