module DASHI.Reasoning.ExceptionalE8AlbertCurrentMaxCutValidation where

------------------------------------------------------------------------
-- RED-FIRST validation for the recut Albert/F4 frontier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true; false)

import DASHI.Reasoning.ExceptionalE8AlbertCurrentMaxCutExact as Cut

selectedMoufangTrialityNowPaid :
  Cut.selectedMoufangTrialityAutomorphismPaid Cut.canonicalExceptionalCurrentMaxCut ≡ true
selectedMoufangTrialityNowPaid = refl

signedBasisG2SubgroupNowPaid :
  Cut.signedBasisG2SubgroupPaid Cut.canonicalExceptionalCurrentMaxCut ≡ true
signedBasisG2SubgroupNowPaid = refl

innerDerivation52DiagnosticNowPaid :
  Cut.innerDerivationDimension52DiagnosticPaid Cut.canonicalExceptionalCurrentMaxCut ≡ true
innerDerivation52DiagnosticNowPaid = refl

fullF4StillOpen :
  Cut.fullF4AutomorphismRecognitionPaid Cut.canonicalExceptionalCurrentMaxCut ≡ false
fullF4StillOpen = refl
