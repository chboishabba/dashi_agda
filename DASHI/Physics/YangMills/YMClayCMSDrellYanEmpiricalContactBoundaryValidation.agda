module DASHI.Physics.YangMills.YMClayCMSDrellYanEmpiricalContactBoundaryValidation where

open import Agda.Builtin.Equality using (_≡_)

-- RED-first validation: the empirical-contact boundary must exist separately
-- from the Clay F1/F3/F4 proof frontier.
import DASHI.Physics.YangMills.YMClayCMSDrellYanEmpiricalContactBoundaryExact as CMSBoundary

open CMSBoundary

cmsEmpiricalContactAvailable : Set
cmsEmpiricalContactAvailable = CMSDrellYanEmpiricalContactPresent

cmsContactIsExperimentalQCDContact :
  cmsContactIsBoundedExperimentalQCDContact ≡ true
cmsContactIsExperimentalQCDContact =
  cmsContactIsBoundedExperimentalQCDContactIsTrue

cmsContactDoesNotPayF1 : cmsContactPaysF1 ≡ false
cmsContactDoesNotPayF1 = cmsContactPaysF1IsFalse

cmsContactDoesNotPayF3 : cmsContactPaysF3 ≡ false
cmsContactDoesNotPayF3 = cmsContactPaysF3IsFalse

cmsContactDoesNotPayF4 : cmsContactPaysF4 ≡ false
cmsContactDoesNotPayF4 = cmsContactPaysF4IsFalse

cmsContactDoesNotProveWholeSpine :
  cmsContactProvesCanonicalSpine ≡ false
cmsContactDoesNotProveWholeSpine =
  cmsContactProvesCanonicalSpineIsFalse
