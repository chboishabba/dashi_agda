module DASHI.Crypto.RSA15SSPFibreAdmissibilityRegression where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Crypto.RSA15SSPFibreAdmissibilityBoundary

regressionVerdictIsStructuredOnly :
  verdict canonicalRSA15SSPFibreAdmissibilityBoundary
  ≡
  structuredSourceDetectorOnly
regressionVerdictIsStructuredOnly =
  canonicalVerdictIsStructuredSourceDetectorOnly

regressionUnbiasedFactorSeparationRemainsFalse :
  unbiasedFactorFibreSeparationObserved
    canonicalRSA15SSPFibreAdmissibilityBoundary
  ≡
  false
regressionUnbiasedFactorSeparationRemainsFalse =
  canonicalUnbiasedFactorSeparationIsBlocked

regressionGeneralRSABreakRemainsFalse :
  generalRSABreakPromoted canonicalRSA15SSPFibreAdmissibilityBoundary
  ≡
  false
regressionGeneralRSABreakRemainsFalse =
  canonicalGeneralRSABreakIsNotPromoted
