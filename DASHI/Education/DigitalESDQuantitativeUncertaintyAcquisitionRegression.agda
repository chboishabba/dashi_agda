module DASHI.Education.DigitalESDQuantitativeUncertaintyAcquisitionRegression where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Education.DigitalESDQuantitativeUncertaintyAcquisitionExact as IAQ
import DASHI.Education.DigitalESDStudyClaimCeilingExact as Ceiling
import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone

iaqAuthorRegression :
  Attr.AttributedSource.sourceAuthor IAQ.iaqSustainabilityEducationSource
  ≡ "Wen-Jing Deng; Jiayue Sun; Wingkei Ho; John Chi-Kin Lee"
iaqAuthorRegression = refl

iaqDOIRegression :
  Attr.AttributedSource.doiState IAQ.iaqSustainabilityEducationSource
  ≡ Attr.doiRecorded "10.3390/su18147165"
iaqDOIRegression = refl

iaqNRegression :
  Ceiling.StudyClaimProfile.enrolledOrReportedN IAQ.iaqPilotProfile
  ≡ Ceiling.explicitlyReportedNat 1408 "Grades 5-10 students across five Asian regions"
iaqNRegression = refl

iaqClaimRegression :
  Ceiling.StudyClaimProfile.strongestSupportedClaim IAQ.iaqPilotProfile
  ≡ Ceiling.implicationConeClaim Cone.derivesBoundedContrast
iaqClaimRegression = refl
