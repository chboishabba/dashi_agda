{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayCMSDrellYanEmpiricalContactBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.HEPDataCMSBelowZDrellYanClaimExact as CMS

------------------------------------------------------------------------
-- CMS empirical-contact axis for the Yang--Mills manuscript / proof ledger.
--
-- Existing canonical receipt:
--   CMS-SMP-20-003 / CERN-EP-2022-053
--   DOI 10.1140/epjc/s10052-023-11631-7
--   HEPData ins2079374/t43 with covariance t44
--   50--76 GeV / 76--106 GeV Drell--Yan ratio
--   chi2/dof = 2.1565191176
--   mean prediction/data = 0.9941233097
--   effective dof = 18
--   freeze commit 3205d746639568762c9e97adf4a3672c356bd491
--
-- This owner does not reinterpret that bounded collider contact as a proof of
-- the Clay mass gap.  It exists so Paper 3 and the current YM ledger can expose
-- experimental contact and proof debt on orthogonal axes.
------------------------------------------------------------------------

cmsEmpiricalContact : CMS.CMSBelowZDrellYanEmpiricalContact
cmsEmpiricalContact = CMS.canonicalCMSBelowZDrellYanEmpiricalContact

cmsAnalysisCode : String
cmsAnalysisCode = "CMS-SMP-20-003"

cmsPublicationDOI : String
cmsPublicationDOI = "10.1140/epjc/s10052-023-11631-7"

cmsDistributionAndCovariance : String
cmsDistributionAndCovariance = "HEPData ins2079374/t43 + t44"

data CMSDrellYanEmpiricalContactPresent : Set where
  cmsDrellYanEmpiricalContactPresent : CMSDrellYanEmpiricalContactPresent

cmsContactIsBoundedExperimentalQCDContact : Bool
cmsContactIsBoundedExperimentalQCDContact = true

cmsContactIsBoundedExperimentalQCDContactIsTrue :
  cmsContactIsBoundedExperimentalQCDContact ≡ true
cmsContactIsBoundedExperimentalQCDContactIsTrue = refl

-- The contact constrains a measured collider observable under the exact frozen
-- comparison law.  It does not supply any of the three live Clay inputs.
cmsContactPaysF1 : Bool
cmsContactPaysF1 = false

cmsContactPaysF1IsFalse : cmsContactPaysF1 ≡ false
cmsContactPaysF1IsFalse = refl

cmsContactPaysF3 : Bool
cmsContactPaysF3 = false

cmsContactPaysF3IsFalse : cmsContactPaysF3 ≡ false
cmsContactPaysF3IsFalse = refl

cmsContactPaysF4 : Bool
cmsContactPaysF4 = false

cmsContactPaysF4IsFalse : cmsContactPaysF4 ≡ false
cmsContactPaysF4IsFalse = refl

-- Preserve the stronger-claim guards already present in the canonical receipt.
cmsContactProvesZeroFittedParameters : Bool
cmsContactProvesZeroFittedParameters = false

cmsContactProvesZeroFittedParametersIsFalse :
  cmsContactProvesZeroFittedParameters ≡ false
cmsContactProvesZeroFittedParametersIsFalse = refl

cmsContactProvesCanonicalSpine : Bool
cmsContactProvesCanonicalSpine = false

cmsContactProvesCanonicalSpineIsFalse :
  cmsContactProvesCanonicalSpine ≡ false
cmsContactProvesCanonicalSpineIsFalse = refl

-- Agda checks the typed receipt/source/digest boundary.  The covariance-aware
-- floating-point calculation is an external replay result in the Closure lane.
agdaKernelRecomputesCMSCovarianceFitHere : Bool
agdaKernelRecomputesCMSCovarianceFitHere = false

agdaKernelRecomputesCMSCovarianceFitHereIsFalse :
  agdaKernelRecomputesCMSCovarianceFitHere ≡ false
agdaKernelRecomputesCMSCovarianceFitHereIsFalse = refl

cmsContactOrthogonalToClayProofFrontier : Bool
cmsContactOrthogonalToClayProofFrontier = true

cmsContactOrthogonalToClayProofFrontierIsTrue :
  cmsContactOrthogonalToClayProofFrontier ≡ true
cmsContactOrthogonalToClayProofFrontierIsTrue = refl
