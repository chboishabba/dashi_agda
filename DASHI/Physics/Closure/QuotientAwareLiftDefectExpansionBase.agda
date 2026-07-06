module DASHI.Physics.Closure.QuotientAwareLiftDefectExpansionBase where

open import Level using (zero)
open import DASHI.Physics.Closure.QuarterMarginBase
  using (QuarterMarginModel)

----------------------------------------------------------------------
-- Abstract quotient-aware lift-defect expansion model.
--
-- This packages the algebraic inequality behind the Gate 2-A transport
-- route:
--
--   transported-ratio ≤ principal-ratio + defect-ratio
--
-- together with comparison bounds
--
--   principal-ratio ≤ θ-principal
--   defect-ratio    ≤ η-defect
--
-- and the quarter-margin closure
--
--   θ-principal + η-defect ≤ 1/4.
--
-- The derived theorem is the abstract transport closure
--
--   transported-ratio ≤ 1/4.

record QuotientAwareLiftDefectExpansionModel : Set₁ where
  constructor mkQuotientAwareLiftDefectExpansionModel
  field
    quarterMarginModel : QuarterMarginModel

  open QuarterMarginModel quarterMarginModel public

  field
    principal-ratio defect-ratio transported-ratio : N

    transported≤principal+defect :
      transported-ratio ≤ (principal-ratio + defect-ratio)

    principal≤θ-principal :
      principal-ratio ≤ θ-principal

    defect≤η-defect :
      defect-ratio ≤ η-defect

  principalPlusDefect≤budget :
    (principal-ratio + defect-ratio) ≤ (θ-principal + η-defect)
  principalPlusDefect≤budget =
    mono+ principal-ratio θ-principal defect-ratio η-defect
      principal≤θ-principal
      defect≤η-defect

  transported≤quarter : transported-ratio ≤ one-quarter
  transported≤quarter =
    trans≤ transported-ratio (principal-ratio + defect-ratio) one-quarter
      transported≤principal+defect
      (trans≤
        (principal-ratio + defect-ratio)
        (θ-principal + η-defect)
        one-quarter
        principalPlusDefect≤budget
        lemma-c)

open QuotientAwareLiftDefectExpansionModel public
