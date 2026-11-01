module DASHI.Law.SensibLawInstitutionalResponsibilityRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Law.SensibLawInstitutionalResponsibilityExact as Resp

authorisation-does-not-pay-justification :
  Resp.authorisedAutomaticallyJustified
    Resp.canonicalInstitutionalResponsibilityBoundary ≡ false
authorisation-does-not-pay-justification = refl

small-contribution-does-not-become-zero :
  Resp.smallContributionAutomaticallyNoContribution
    Resp.canonicalInstitutionalResponsibilityBoundary ≡ false
small-contribution-does-not-become-zero = refl

role-obligation-does-not-settle-responsibility :
  Resp.roleObligationAutomaticallyCompleteResponsibilityAnswer
    Resp.canonicalInstitutionalResponsibilityBoundary ≡ false
role-obligation-does-not-settle-responsibility = refl
