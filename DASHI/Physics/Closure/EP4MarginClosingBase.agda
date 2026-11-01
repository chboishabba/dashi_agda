module DASHI.Physics.Closure.EP4MarginClosingBase where

open import Level using (zero)
open import DASHI.Physics.Closure.QuotientAwareLiftDefectExpansionBase
  using (QuotientAwareLiftDefectExpansionModel)

----------------------------------------------------------------------
-- Abstract EP4 margin-closing model.
--
-- EP4 consumes the quotient-aware transport closure from Gate 2-A and
-- adds the final outside-seam pollution budget:
--
--   total-leakage ≤ transported-ratio + outside-seam-pollution
--   transported-ratio ≤ 1/4
--   outside-seam-pollution ≤ residual-slack
--   1/4 + residual-slack ≤ unit-threshold
--
-- The derived theorem is the exact closing statement needed for the
-- seam-to-leakage transfer:
--
--   total-leakage ≤ unit-threshold.

record EP4MarginClosingModel : Set₁ where
  constructor mkEP4MarginClosingModel
  field
    quotientAwareModel : QuotientAwareLiftDefectExpansionModel

  open QuotientAwareLiftDefectExpansionModel quotientAwareModel public

  field
    outside-seam-pollution total-leakage residual-slack unit-threshold : N

    total≤transported+outside :
      total-leakage ≤ (transported-ratio + outside-seam-pollution)

    outside≤slack :
      outside-seam-pollution ≤ residual-slack

    quarterPlusSlack≤unit :
      (one-quarter + residual-slack) ≤ unit-threshold

  transportedPlusOutside≤unit :
    (transported-ratio + outside-seam-pollution) ≤ unit-threshold
  transportedPlusOutside≤unit =
    trans≤
      (transported-ratio + outside-seam-pollution)
      (one-quarter + residual-slack)
      unit-threshold
      (mono+ transported-ratio one-quarter outside-seam-pollution residual-slack
        transported≤quarter
        outside≤slack)
      quarterPlusSlack≤unit

  total≤unit : total-leakage ≤ unit-threshold
  total≤unit =
    trans≤ total-leakage (transported-ratio + outside-seam-pollution) unit-threshold
      total≤transported+outside
      transportedPlusOutside≤unit

open EP4MarginClosingModel public
