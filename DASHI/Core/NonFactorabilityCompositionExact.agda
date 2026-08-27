module DASHI.Core.NonFactorabilityCompositionExact where

------------------------------------------------------------------------
-- NON-FACTORABILITY SURVIVES FURTHER COARSENING
--
-- If a consumer-relevant phenomenon already fails to factor through one
-- projection, post-composing that projection with another observer cannot
-- repair the erased distinction.  This is the exact algebra needed when a
-- private/fine state is first projected to an expressed surface and then to an
-- institutional/public surface.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; cong)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF

postcomposeNonFactorability :
  ∀ {Situated Flat Surface Outcome : Set}
    {flatten : Situated → Flat}
    {phenomenon : Situated → Outcome} →
  (post : Flat → Surface) →
  NF.NonFactorabilityWitness flatten phenomenon →
  NF.NonFactorabilityWitness (λ state → post (flatten state)) phenomenon
postcomposeNonFactorability post witness =
  NF.nonFactorabilityWitness
    (NF.left witness)
    (NF.right witness)
    (cong post (NF.sameFlatProjection witness))
    (NF.situatedOutcomesDiffer witness)

postcompositionCannotRepairErasedDistinction :
  ∀ {Situated Flat Surface Outcome : Set}
    {flatten : Situated → Flat}
    {phenomenon : Situated → Outcome} →
  (post : Flat → Surface) →
  NF.NonFactorabilityWitness flatten phenomenon →
  NF.FactorsThrough (λ state → post (flatten state)) phenomenon →
  ⊥
postcompositionCannotRepairErasedDistinction post witness =
  NF.witnessRulesOutEveryFlatFactorisation
    (postcomposeNonFactorability post witness)

------------------------------------------------------------------------
-- A two-stage observer is therefore no stronger than its first stage for a
-- distinction already lost at that first stage.  The theorem is deliberately
-- one-way: a later observer may erase additional distinctions too.
------------------------------------------------------------------------

TwoStageProjection :
  ∀ {Fine Middle Surface : Set} →
  (Fine → Middle) → (Middle → Surface) → Fine → Surface
TwoStageProjection first second state = second (first state)

twoStageNonFactorability :
  ∀ {Fine Middle Surface Outcome : Set}
    {first : Fine → Middle}
    {phenomenon : Fine → Outcome} →
  (second : Middle → Surface) →
  NF.NonFactorabilityWitness first phenomenon →
  NF.NonFactorabilityWitness (TwoStageProjection first second) phenomenon
twoStageNonFactorability = postcomposeNonFactorability
