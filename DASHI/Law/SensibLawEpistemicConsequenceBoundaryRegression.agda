module DASHI.Law.SensibLawEpistemicConsequenceBoundaryRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Law.SensibLawEpistemicConsequenceBoundaryExact as EC

high-consequence-does-not-prove-falsity :
  EC.highConsequenceAutomaticallyUnderlyingInferenceFalse
    EC.canonicalEpistemicConsequenceBoundary ≡ false
high-consequence-does-not-prove-falsity = refl

high-uncertainty-does-not-create-automatic-prohibition :
  EC.highUncertaintyAutomaticallyProhibitsAction
    EC.canonicalEpistemicConsequenceBoundary ≡ false
high-uncertainty-does-not-create-automatic-prohibition = refl

legal-availability-does-not-pay-all-consumer-adequacy :
  EC.legalAvailabilityAutomaticallyAdequateForEveryConsumer
    EC.canonicalEpistemicConsequenceBoundary ≡ false
legal-availability-does-not-pay-all-consumer-adequacy = refl

severity-reversibility-remain-independent :
  EC.severityAndReversibilityAreSeparateCoordinates
    EC.canonicalEpistemicConsequenceBoundary ≡ true
severity-reversibility-remain-independent = refl
