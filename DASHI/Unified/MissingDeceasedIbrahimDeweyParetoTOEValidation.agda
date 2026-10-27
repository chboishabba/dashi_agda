{-# OPTIONS --safe #-}
module DASHI.Unified.MissingDeceasedIbrahimDeweyParetoTOEValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (false; true)

import DASHI.Unified.MissingDeceasedIbrahimDeweyParetoTOEExact as Boundary
import DASHI.EverythingTOESymmetryResolved369 as TOE
import DASHI.Unifier as Unifier
import DASHI.Culture.MissingDeceasedIbrahimDeweyConvergenceExact as Crosswalk

toeBoundaryExact :
  TOE.missingDeceasedIbrahimDeweyBoundary
  ≡ Crosswalk.canonicalIbrahimDeweyConvergenceBoundary
toeBoundaryExact = refl

unifierBoundaryExact :
  Unifier.missingDeceasedIbrahimDeweyBoundary
  ≡ Crosswalk.canonicalIbrahimDeweyConvergenceBoundary
unifierBoundaryExact = refl

toeAmyReceiptExact :
  TOE.missingDeceasedAmyIbrahimDeweyConvergence
  ≡ Crosswalk.amyIbrahimDeweyConvergence
toeAmyReceiptExact = refl

unifierMaiwaldReceiptExact :
  Unifier.missingDeceasedMaiwaldIbrahimDeweyConvergence
  ≡ Crosswalk.maiwaldIbrahimDeweyConvergence
unifierMaiwaldReceiptExact = refl

dualRouteStillDoesNotCreateAuthority :
  Boundary.dualRouteAgreementCreatesAuthority ≡ false
dualRouteStillDoesNotCreateAuthority =
  Boundary.dualRouteAgreementCreatesAuthorityIsFalse

dualRouteStillMayRaisePriority :
  Boundary.dualRouteAgreementMayRaiseAcquisitionPriority ≡ true
dualRouteStillMayRaisePriority =
  Boundary.dualRouteAgreementMayRaiseAcquisitionPriorityIsTrue
