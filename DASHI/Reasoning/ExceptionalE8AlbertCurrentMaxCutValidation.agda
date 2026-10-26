module DASHI.Reasoning.ExceptionalE8AlbertCurrentMaxCutValidation where

------------------------------------------------------------------------
-- Validation surface for the exact exceptional max-cut.
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

knownGeneratorFamilyPaid :
  Cut.knownAlbertGeneratorFamilyPaid Cut.canonicalExceptionalCurrentMaxCut ≡ true
knownGeneratorFamilyPaid = refl

typedLinearJordanAutomorphismCarrierPaid :
  Cut.typedLinearJordanAutomorphismCarrierPaid Cut.canonicalExceptionalCurrentMaxCut ≡ true
typedLinearJordanAutomorphismCarrierPaid = refl

allInnerDerivationLawsSourceWritten :
  Cut.allInnerDerivationLawsSourceWritten Cut.canonicalExceptionalCurrentMaxCut ≡ true
allInnerDerivationLawsSourceWritten = refl

innerDerivation52NowPaid :
  Cut.exactInnerDerivationDimension52Paid Cut.canonicalExceptionalCurrentMaxCut ≡ true
innerDerivation52NowPaid = refl

trialitySplitNowPaid :
  Cut.exactTrialityTwentyEightEightEightEightPaid Cut.canonicalExceptionalCurrentMaxCut ≡ true
trialitySplitNowPaid = refl

exactQIRootSpacesNowPaid :
  Cut.exactQIRootSpacesFourPlusFortyEightPaid Cut.canonicalExceptionalCurrentMaxCut ≡ true
exactQIRootSpacesNowPaid = refl

allConcreteClassificationHypothesesOwned :
  Cut.allConcreteClassificationHypothesesOwned Cut.canonicalExceptionalCurrentMaxCut ≡ true
allConcreteClassificationHypothesesOwned = refl

generalClassificationStillExternal :
  Cut.generalExceptionalClassificationFormalizedInRepo Cut.canonicalExceptionalCurrentMaxCut ≡ false
generalClassificationStillExternal = refl

fullF4StillClassificationOpen :
  Cut.fullF4AutomorphismRecognitionPaid Cut.canonicalExceptionalCurrentMaxCut ≡ false
fullF4StillClassificationOpen = refl
