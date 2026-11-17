module DASHI.Analysis.CollatzSyracuseAffinePrefixTransitionValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.CollatzSyracuseAffinePrefixTransitionExact as Step

appendZeroPaid :
  Step.AffinePrefixTransitionBoundary.trailingEvenTransitionPaid
    Step.canonicalAffinePrefixTransitionBoundary
  ≡ 1
appendZeroPaid = refl

appendOnePaid :
  Step.AffinePrefixTransitionBoundary.trailingOddTransitionPaid
    Step.canonicalAffinePrefixTransitionBoundary
  ≡ 1
appendOnePaid = refl

oddRegimePaid :
  Step.AffinePrefixTransitionBoundary.exactOddGapRegimeClassifierPaid
    Step.canonicalAffinePrefixTransitionBoundary
  ≡ 1
oddRegimePaid = refl

logsNotRequired :
  Step.AffinePrefixTransitionBoundary.floatingLogRequiredForRegimeClassification
    Step.canonicalAffinePrefixTransitionBoundary
  ≡ 0
logsNotRequired = refl
