module DASHI.Analysis.RiemannG2ProjectiveJointComplementQuadraticLeanDonorValidationExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true; false)

import DASHI.Analysis.RiemannG2ProjectiveJointComplementQuadraticLeanDonorExact as O

jointTheoremSourceWritten :
  O.ProjectiveJointQuadraticBoundary.jointProjectiveQuadraticCompositionSourceWritten
    O.canonicalProjectiveJointQuadraticBoundary ≡ true
jointTheoremSourceWritten = refl

finalCarrierIdentityStillAbsent :
  O.ProjectiveJointQuadraticBoundary.projectiveTaperDefinitionallyFinalUniversalPoleQuotientTaper
    O.canonicalProjectiveJointQuadraticBoundary ≡ false
finalCarrierIdentityStillAbsent = refl

finalR2NotClaimed :
  O.ProjectiveJointQuadraticBoundary.jointDonorAlreadyPaysFinalR2
    O.canonicalProjectiveJointQuadraticBoundary ≡ false
finalR2NotClaimed = refl
