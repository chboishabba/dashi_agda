module DASHI.Governance.QuotientDefectResidualRouting where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Quotient defect / residual routing.
--
-- Classification is allowed to compress.  Safety requires a receipt for the
-- distinctions collapsed by that quotient and a typed route for any later use.
-- The Calabi-Yau quotient/resolution analogy here is motivation only: no
-- theorem about Calabi-Yau geometry is imported into this social/governance
-- carrier.
------------------------------------------------------------------------

record QuotientReceiptSystem : Set₁ where
  field
    Fine : Set
    Coarse : Set
    Defect : Set
    Provenance : Set
    Proposition : Set

    project : Fine → Coarse
    defect : Fine → Defect
    provenance : Fine → Provenance
    resolveFor : Proposition → Coarse → Defect → Provenance → Fine

open QuotientReceiptSystem public

record PropositionRelevantReopening (Q : QuotientReceiptSystem) : Set₁ where
  field
    RelevantEquivalent : Proposition Q → Fine Q → Fine Q → Set
    reopenRelevant :
      (p : Proposition Q) →
      (x : Fine Q) →
      RelevantEquivalent p x
        (resolveFor Q p (project Q x) (defect Q x) (provenance Q x))

open PropositionRelevantReopening public

------------------------------------------------------------------------
-- Several residual coordinates may coexist.  A system may preserve one and
-- erase/amplify another, so a single undifferentiated Q is too weak.
------------------------------------------------------------------------

data ResidualKind : Set where
  historical causal identity authority counterevidence trauma : ResidualKind

record ResidualFamily (Q : QuotientReceiptSystem) : Set₁ where
  field
    Residual : ResidualKind → Set
    observeResidual : (k : ResidualKind) → Fine Q → Residual k

open ResidualFamily public

record ResidualPolicyRouter (Q : QuotientReceiptSystem) (R : ResidualFamily Q) : Set₁ where
  field
    Action : Set
    routeResidual : (k : ResidualKind) → Residual R k → Action

open ResidualPolicyRouter public

------------------------------------------------------------------------
-- Non-promotion boundary: coarse equality alone cannot prove equality of a
-- residual coordinate.  A witness of residual difference therefore refutes
-- any proposed promotion that tries to manufacture such equality.
------------------------------------------------------------------------

record ResidualDifference
    {Q : QuotientReceiptSystem}
    (R : ResidualFamily Q)
    (k : ResidualKind)
    (x y : Fine Q) : Set₁ where
  field
    sameCoarse : project Q x ≡ project Q y
    residualDifferent : observeResidual R k x ≡ observeResidual R k y → ⊥

open ResidualDifference public

coarseEqualityCannotEraseResidualDifference :
  ∀ {Q R k x y} →
  ResidualDifference {Q} R k x y →
  observeResidual R k x ≡ observeResidual R k y →
  ⊥
coarseEqualityCannotEraseResidualDifference d = residualDifferent d

------------------------------------------------------------------------
-- A defect is a receipt that quotienting was nontrivial at the disputed
-- proposition.  It is not itself guilt, truth, or action authority.
------------------------------------------------------------------------

data DefectAutomaticallyAuthorisesAction : Set where

defectDoesNotAutomaticallyAuthoriseAction :
  DefectAutomaticallyAuthorisesAction → ⊥
defectDoesNotAutomaticallyAuthoriseAction ()
