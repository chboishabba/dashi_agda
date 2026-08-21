module DASHI.Core.IntersectionalNonFactorability where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

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
-- Concrete carrier-repair witness.
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

data SeparateAxisSufficiencyImpliesIntersectionalSufficiencyPermission : Set where

separateAxisSufficiencyCannotAutoPromote :
  SeparateAxisSufficiencyImpliesIntersectionalSufficiencyPermission → ⊥
separateAxisSufficiencyCannotAutoPromote ()
