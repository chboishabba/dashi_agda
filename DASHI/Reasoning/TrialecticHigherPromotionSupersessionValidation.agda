module DASHI.Reasoning.TrialecticHigherPromotionSupersessionValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.TrialecticHigherPromotionSupersessionExact as Sup

boundary : Sup.TrialecticHigherPromotionSupersessionBoundary
boundary = Sup.canonicalTrialecticHigherPromotionSupersessionBoundary

oldLocalTokenStillUninhabited :
  Sup.oldLocalThreeCellPromotionTokenInhabited boundary ≡ false
oldLocalTokenStillUninhabited = refl

laterHigherStackExists :
  Sup.laterIndependentHigherStackCertificatePaid boundary ≡ true
laterHigherStackExists = refl

laterFiniteHypersheafExists :
  Sup.laterIndependentFiniteHypersheafCertificatePaid boundary ≡ true
laterFiniteHypersheafExists = refl

noContradiction :
  Sup.laterCertificateClaimsOldTokenInhabited boundary ≡ false
noContradiction = refl
