module DASHI.Physics.Closure.HEPDataCMSBelowZDrellYanClaimExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: CMS Collaboration.
-- Title: "Measurement of the Mass Dependence of the Transverse Momentum of
-- Lepton Pairs in Drell--Yan Production in Proton--Proton Collisions at
-- sqrt(s) = 13 TeV".
-- European Physical Journal C 83 (2023), article 628.
-- DOI: 10.1140/epjc/s10052-023-11631-7.
-- CMS analysis: CMS-SMP-20-003; CERN-EP-2022-053.
-- HEPData record: ins2079374, distribution t43 with covariance table t44.
--
-- PURPOSE
-- State the strongest claim currently supported by the frozen repository
-- evidence.  Agda checks the source binding, numbers, digests and scope of the
-- receipt.  The floating-point covariance calculation was performed by the
-- external replay program; it is not re-derived by the Agda kernel.  The t43
-- contact does not by itself prove unique unification or a zero-fitted-parameter
-- derivation from the whole canonical spine.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.HEPDataW3ComparisonLawReceipt as W3

record CMSBelowZDrellYanEmpiricalContact : Set where
  field
    sourceReceipt : W3.W3ComparisonLawReceipt

    publicationTitle : String
    publicationDOI : String
    analysisCode : String

    numeratorMassWindow : String
    denominatorMassWindow : String
    distributionTable : String
    covarianceTable : String

    chi2PerDof : Float
    meanPredictionOverData : Float
    effectiveDegreesOfFreedom : Float

    freezeCommit : String
    artifactSha256 : String
    projectionDigest : String

    chi2PerDofMatchesSource :
      chi2PerDof
      ≡ W3.W3ComparisonLawAcceptanceCriterion.chi2PerDof
          (W3.W3ComparisonLawReceipt.criterion sourceReceipt)

    meanPredictionOverDataMatchesSource :
      meanPredictionOverData
      ≡ W3.W3ComparisonLawAcceptanceCriterion.meanPredData
          (W3.W3ComparisonLawReceipt.criterion sourceReceipt)

    effectiveDegreesOfFreedomMatchesSource :
      effectiveDegreesOfFreedom
      ≡ W3.W3ComparisonLawAcceptanceCriterion.effectiveDof
          (W3.W3ComparisonLawReceipt.criterion sourceReceipt)

    freezeCommitMatchesSource :
      freezeCommit
      ≡ W3.W3ComparisonLawAcceptanceCriterion.freezeCommit
          (W3.W3ComparisonLawReceipt.criterion sourceReceipt)

    artifactSha256MatchesSource :
      artifactSha256
      ≡ W3.W3ComparisonLawAcceptanceCriterion.fileSha256
          (W3.W3ComparisonLawReceipt.criterion sourceReceipt)

    projectionDigestMatchesSource :
      projectionDigest
      ≡ W3.W3ComparisonLawAcceptanceCriterion.projectionDigest
          (W3.W3ComparisonLawReceipt.criterion sourceReceipt)

open CMSBelowZDrellYanEmpiricalContact public

canonicalCMSBelowZDrellYanEmpiricalContact :
  CMSBelowZDrellYanEmpiricalContact
canonicalCMSBelowZDrellYanEmpiricalContact = record
  { sourceReceipt = W3.canonicalHEPDataW3ComparisonLawReceipt
  ; publicationTitle =
      "Measurement of the mass dependence of the transverse momentum of lepton pairs in Drell-Yan production in proton-proton collisions at sqrt(s)=13 TeV"
  ; publicationDOI = "10.1140/epjc/s10052-023-11631-7"
  ; analysisCode = "CMS-SMP-20-003"
  ; numeratorMassWindow = "50--76 GeV"
  ; denominatorMassWindow = "76--106 GeV"
  ; distributionTable = "ins2079374/t43"
  ; covarianceTable = "ins2079374/t44"
  ; chi2PerDof = 2.1565191176
  ; meanPredictionOverData = 0.9941233097
  ; effectiveDegreesOfFreedom = 18.0
  ; freezeCommit = "3205d746639568762c9e97adf4a3672c356bd491"
  ; artifactSha256 =
      "ffd659e6e2f271d75ec6bf90c5be34cbb9959a8f9d32762c1a2231835fb61eac"
  ; projectionDigest =
      "00f6c23f97f9c0275d90e6ffbf6151b07defcc163708e2d93982d9b7d6866035"
  ; chi2PerDofMatchesSource = refl
  ; meanPredictionOverDataMatchesSource = refl
  ; effectiveDegreesOfFreedomMatchesSource = refl
  ; freezeCommitMatchesSource = refl
  ; artifactSha256MatchesSource = refl
  ; projectionDigestMatchesSource = refl
  }

boundedBelowZComparisonLawPromoted : Bool
boundedBelowZComparisonLawPromoted = true

byteReproducibilityReceiptPresent : Bool
byteReproducibilityReceiptPresent = true

agdaKernelChecksReceiptStructure : Bool
agdaKernelChecksReceiptStructure = true

agdaKernelRecomputesFloatingPointCovarianceFit : Bool
agdaKernelRecomputesFloatingPointCovarianceFit = false

zeroFittedParametersProved : Bool
zeroFittedParametersProved = false

cmsContactProvesWholeCanonicalSpine : Bool
cmsContactProvesWholeCanonicalSpine = false

boundedBelowZComparisonLawPromotedIsTrue :
  boundedBelowZComparisonLawPromoted ≡ true
boundedBelowZComparisonLawPromotedIsTrue = refl

agdaKernelRecomputesFloatingPointCovarianceFitIsFalse :
  agdaKernelRecomputesFloatingPointCovarianceFit ≡ false
agdaKernelRecomputesFloatingPointCovarianceFitIsFalse = refl

zeroFittedParametersProvedIsFalse :
  zeroFittedParametersProved ≡ false
zeroFittedParametersProvedIsFalse = refl

cmsContactProvesWholeCanonicalSpineIsFalse :
  cmsContactProvesWholeCanonicalSpine ≡ false
cmsContactProvesWholeCanonicalSpineIsFalse = refl

recommendedBoundedClaim : String
recommendedBoundedClaim =
  "DASHI has a bounded empirical contact with CMS-SMP-20-003 t43. The frozen t43/t44 covariance comparison for the 50--76 / 76--106 GeV Drell-Yan ratio gives chi2/dof=2.1565191176 and mean prediction/data=0.9941233097 at commit 3205d746639568762c9e97adf4a3672c356bd491. Agda verifies the typed receipt, source binding, digests and claim boundary; the external numerical fit is byte-replayable but is not itself recomputed by the Agda kernel."
