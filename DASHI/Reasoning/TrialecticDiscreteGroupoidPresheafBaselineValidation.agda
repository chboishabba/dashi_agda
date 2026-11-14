module DASHI.Reasoning.TrialecticDiscreteGroupoidPresheafBaselineValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.TrialecticDiscreteGroupoidPresheafBaselineExact as Baseline

boundary : Baseline.TrialecticDiscreteGroupoidPresheafBaselineBoundary
boundary = Baseline.canonicalTrialecticDiscreteGroupoidPresheafBaselineBoundary

fullSiteDiscreteGroupoidBaselinePaid :
  Baseline.fullSiteDiscreteGroupoidBaselinePaid boundary ≡ true
fullSiteDiscreteGroupoidBaselinePaid = refl

restrictionFunctorOnEqualityMorphismsPaid :
  Baseline.restrictionFunctorOnEqualityMorphismsPaid boundary ≡ true
restrictionFunctorOnEqualityMorphismsPaid = refl

edgeCycleIsNotSiteRestriction :
  Baseline.edgeCycleIsSiteRestriction boundary ≡ false
edgeCycleIsNotSiteRestriction = refl

transportEnrichedPresheafStillOpen :
  Baseline.transportEnrichedGroupoidPresheafPaid boundary ≡ false
transportEnrichedPresheafStillOpen = refl
