module DASHI.Physics.Closure.NearExtremizerDefectEstimateBase where

open import Level using (zero)
open import DASHI.Physics.Closure.DefectBudgetBase
  using (DefectBudget)

----------------------------------------------------------------------
-- Abstract near-extremizer defect estimate model.
--
-- This packages the three cone-uniform quantities that appear in the
-- quotient-aware lift expansion:
--
--   • cross-term    = | 2⟨ΔJ x, L_neg J_abs x⟩ |
--   • pure-term     = | ⟨ΔJ x, L_neg ΔJ x⟩ |
--   • combined-term = | 2⟨ΔJ x, L_neg J_abs x⟩ + ⟨ΔJ x, L_neg ΔJ x⟩ |
--
-- together with the additive defect budget
--
--   η-cross + η-pure ≤ η-defect.
--
-- The core abstract proof is the cone-uniform combined estimate
--
--   combined-term ≤ η-defect
--
-- derived from:
--
--   combined-term ≤ cross-term + pure-term
--   cross-term    ≤ η-cross
--   pure-term     ≤ η-pure.

record NearExtremizerDefectEstimateModel : Set₁ where
  constructor mkNearExtremizerDefectEstimateModel
  field
    defectBudget : DefectBudget

  open DefectBudget defectBudget public

  field
    cross-term pure-term combined-term : N

    combined≤split :
      combined-term ≤ (cross-term + pure-term)

    cross≤η-cross :
      cross-term ≤ η-cross

    pure≤η-pure :
      pure-term ≤ η-pure

  split≤η-sum : (cross-term + pure-term) ≤ (η-cross + η-pure)
  split≤η-sum =
    mono+ cross-term η-cross pure-term η-pure
      cross≤η-cross
      pure≤η-pure

  combined≤η-defect : combined-term ≤ η-defect
  combined≤η-defect =
    trans≤ combined-term (cross-term + pure-term) η-defect
      combined≤split
      (trans≤
        (cross-term + pure-term)
        (η-cross + η-pure)
        η-defect
        split≤η-sum
        (DefectBudget.lemma-a defectBudget))

open NearExtremizerDefectEstimateModel public
