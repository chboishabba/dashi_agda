module DASHI.Physics.Closure.HEPDataEmpiricalAuthorityReceiptCollation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataResidualBridgeAuthorityGate as Gate
import DASHI.Physics.Closure.HEPDataResidualObservableClassExternalAlignment as Align
import DASHI.Physics.Closure.HEPDataResidualProviderReceiptRequestPack as Pack

------------------------------------------------------------------------
-- HEPData empirical authority receipt collation.
--
-- This module records the provider-supplied CMS/HEPData source collation as
-- a non-promoting authority packet for the phistar_50_76 residual lane.
--
-- Important correction: the authoritative HEPData publication page binds
-- "phistar mass 50-76" to submission record ins2079374, table DOI
-- 10.17182/hepdata.115656.v1/t19.  Its covariance table is t20.  The older
-- t31 pointer names a different pT-ratio table, so this module records that
-- mismatch explicitly instead of using t31 as authority for phistar_50_76.

data HEPDataEmpiricalAuthorityReceiptCollationStatus : Set where
  authoritySourcesCollatedButAdapterTransformMissing :
    HEPDataEmpiricalAuthorityReceiptCollationStatus

data HEPDataEmpiricalAuthorityReceiptCollationField : Set where
  collationPrimaryPublication :
    HEPDataEmpiricalAuthorityReceiptCollationField
  collationPrimaryHEPDataSubmission :
    HEPDataEmpiricalAuthorityReceiptCollationField
  collationPrimaryTable :
    HEPDataEmpiricalAuthorityReceiptCollationField
  collationPrimaryCovarianceTable :
    HEPDataEmpiricalAuthorityReceiptCollationField
  collationRawCSVArtifact :
    HEPDataEmpiricalAuthorityReceiptCollationField
  collationLocalNormalizedArtifact :
    HEPDataEmpiricalAuthorityReceiptCollationField
  collationRawVsNormalizedAdapterGap :
    HEPDataEmpiricalAuthorityReceiptCollationField
  collationSecondaryCalibrationBaseline :
    HEPDataEmpiricalAuthorityReceiptCollationField
  collationResidualClassExternalAlignment :
    HEPDataEmpiricalAuthorityReceiptCollationField
  collationRemainingProviderReceipts :
    HEPDataEmpiricalAuthorityReceiptCollationField

canonicalHEPDataEmpiricalAuthorityReceiptCollationFields :
  List HEPDataEmpiricalAuthorityReceiptCollationField
canonicalHEPDataEmpiricalAuthorityReceiptCollationFields =
  collationPrimaryPublication
  ∷ collationPrimaryHEPDataSubmission
  ∷ collationPrimaryTable
  ∷ collationPrimaryCovarianceTable
  ∷ collationRawCSVArtifact
  ∷ collationLocalNormalizedArtifact
  ∷ collationRawVsNormalizedAdapterGap
  ∷ collationSecondaryCalibrationBaseline
  ∷ collationResidualClassExternalAlignment
  ∷ collationRemainingProviderReceipts
  ∷ []

record HEPDataEmpiricalAuthorityReceiptCollation : Setω where
  field
    status :
      HEPDataEmpiricalAuthorityReceiptCollationStatus

    externalAlignment :
      Align.HEPDataResidualObservableClassExternalAlignment

    residualAuthorityGate :
      Gate.HEPDataResidualBridgeAuthorityGate

    authorityGateStatus :
      Gate.HEPDataResidualBridgeAuthorityGateStatus

    authorityGateStatusIsBlocked :
      authorityGateStatus
      ≡
      Gate.blockedAwaitingResidualAuthorityReceiptChain

    providerFirstMissingReceipt :
      Pack.HEPDataResidualProviderFirstMissingReceipt

    providerFirstMissingReceiptIsResidualObservableClass :
      providerFirstMissingReceipt
      ≡
      Pack.firstMissingResidualObservableClass

    collationFields :
      List HEPDataEmpiricalAuthorityReceiptCollationField

    collationFieldsAreCanonical :
      collationFields
      ≡
      canonicalHEPDataEmpiricalAuthorityReceiptCollationFields

    primarySourceReceipt :
      List String

    rawUpstreamArtifacts :
      List String

    localNormalizedArtifact :
      List String

    adapterTransformGap :
      List String

    secondaryCalibrationBaseline :
      List String

    filledProviderFields :
      List String

    stillMissingProviderReceipts :
      List Pack.HEPDataResidualProviderRequiredReceipt

    stillMissingProviderReceiptsAreCanonical :
      stillMissingProviderReceipts
      ≡
      Pack.canonicalHEPDataResidualProviderRequiredReceipts

    nonPromotionBoundary :
      List String

canonicalHEPDataEmpiricalAuthorityReceiptCollation :
  HEPDataEmpiricalAuthorityReceiptCollation
canonicalHEPDataEmpiricalAuthorityReceiptCollation =
  record
    { status =
        authoritySourcesCollatedButAdapterTransformMissing
    ; externalAlignment =
        Align.canonicalHEPDataResidualObservableClassExternalAlignment
    ; residualAuthorityGate =
        Gate.canonicalHEPDataResidualBridgeAuthorityGate
    ; authorityGateStatus =
        Gate.blockedAwaitingResidualAuthorityReceiptChain
    ; authorityGateStatusIsBlocked =
        refl
    ; providerFirstMissingReceipt =
        Pack.firstMissingResidualObservableClass
    ; providerFirstMissingReceiptIsResidualObservableClass =
        refl
    ; collationFields =
        canonicalHEPDataEmpiricalAuthorityReceiptCollationFields
    ; collationFieldsAreCanonical =
        refl
    ; primarySourceReceipt =
        "experiment = CMS at LHC"
        ∷ "analysis = CMS-SMP-20-003 / CERN-EP-2022-053"
        ∷ "paper = Eur. Phys. J. C 83 (2023) 628"
        ∷ "paper DOI from HEPData/CMS source page = 10.1140/epjc/s10052-023-11631-7"
        ∷ "rejected wrong DOI pointer = 10.1140/epjc/s10052-023-11680-y"
        ∷ "arXiv = 2205.04897 [hep-ex]"
        ∷ "CMS public page = https://cms-results.web.cern.ch/cms-results/public-results/publications/SMP-20-003/"
        ∷ "HEPData publication record = https://www.hepdata.net/record/ins2079374"
        ∷ "HEPData submission DOI = 10.17182/hepdata.115656.v1"
        ∷ "INSPIRE literature record = ins2079374"
        ∷ "integrated luminosity = 36.3 fb^-1 at sqrt(s) = 13 TeV"
        ∷ "published observable family = Drell-Yan d sigma / d phi* in M_ll windows"
        ∷ []
    ; rawUpstreamArtifacts =
        "selected table = phistar mass 50-76"
        ∷ "selected table DOI = 10.17182/hepdata.115656.v1/t19"
        ∷ "selected covariance table = Covariance matrices for phistar mass 50-76"
        ∷ "selected covariance table DOI = 10.17182/hepdata.115656.v1/t20"
        ∷ "raw CSV path = scripts/data/hepdata/ins2079374_phistar_mass_50-76_t19.csv"
        ∷ "raw CSV sha256 = 1a1d280da645f4c55aba73aabf1b398a3fd9614532c363d972018f194b653677"
        ∷ "raw covariance CSV path = scripts/data/hepdata/ins2079374_Covariance_phistar_mass_50-76_t20.csv"
        ∷ "raw covariance CSV sha256 = fa4b694211862d4b07b761d0dab77c8fe1016d2ccd5015dc6f7bc3272c34201a"
        ∷ "raw bin0 center/value = 0.002 / 228.59 pb per unit phi*"
        ∷ "raw bin1 center/value = 0.006 / 225.69 pb per unit phi*"
        ∷ "raw adjacent-bin delta = 2.90 pb per unit phi*"
        ∷ []
    ; localNormalizedArtifact =
        "normalized artifact path = scripts/data/hepdata_phistar_50_76_artifact.json"
        ∷ "normalized artifact sha256 = 20085dc6092e59a6afc381cb0bf2f03da2d19f375a22a0f9e701d7c890244139"
        ∷ "normalized source path = /home/c/Documents/code/dashifine/hepdata_npz/phistar_50_76.npz"
        ∷ "normalized row count = 18"
        ∷ "normalized measurement fields = x, y, cov"
        ∷ "normalized bin0 center/value = 0.002 / 188.4"
        ∷ "normalized bin1 center/value = 0.006 / 185.09"
        ∷ "normalized adjacent-bin delta = 3.3100000000000023"
        ∷ []
    ; adapterTransformGap =
        "The upstream HEPData raw CSV and local normalized artifact are both concrete, but their first two y values differ"
        ∷ "This is not a data absence; it is an adapter-transform receipt gap"
        ∷ "The selected adapter route is now the dimensionless ratio table t43/t44; raw t19/t20 remains absolute-source context"
        ∷ "The previous t31 pointer is rejected for phistar_50_76 authority because t31 is pT ll mass 106-170 over mass 76-106"
        ∷ "The earlier DOI pointer 10.1140/epjc/s10052-023-11680-y is rejected as the wrong paper pointer; the canonical CMS-SMP-20-003 paper DOI is 10.1140/epjc/s10052-023-11631-7"
        ∷ "No W3 empirical authority can be promoted until the selected value surface is fixed by checksum and adapter semantics"
        ∷ []
    ; secondaryCalibrationBaseline =
        "calibration baseline = CMS-SMP-19-010 / JHEP 12 (2019) 061"
        ∷ "baseline paper DOI = 10.1007/JHEP12(2019)061"
        ∷ "baseline HEPData DOI = 10.17182/hepdata.88356"
        ∷ "baseline data = 2016 CMS pp at sqrt(s) = 13 TeV, about 35.8/35.9 fb^-1 depending on citation surface"
        ∷ "baseline role = prior precision/calibration reference for phi* observable class, not a W4 unit-calibration receipt"
        ∷ "baseline precision note = normalized-cross-section uncertainties below 0.5% for phi* < 0.5 is an external literature claim to be bound by a future calibration receipt"
        ∷ []
    ; filledProviderFields =
        "schema/source identity fields are now externally citable for CMS-SMP-20-003"
        ∷ "selected raw table/covariance table are checksum-bound locally"
        ∷ "published observable class is externally legible as adjacent-bin finite-difference residual / local bin-to-bin variation"
        ∷ "non-collapse is concrete on both raw upstream and normalized local surfaces"
        ∷ "secondary calibration baseline is named, but not promoted"
        ∷ "ratio adapter route t43/t44 is selected in HEP-R21, but projection/comparison and prediction freeze remain missing"
        ∷ []
    ; stillMissingProviderReceipts =
        Pack.canonicalHEPDataResidualProviderRequiredReceipts
    ; stillMissingProviderReceiptsAreCanonical =
        refl
    ; nonPromotionBoundary =
        "This module is an empirical authority collation and correction packet"
        ∷ "It does not construct residualObservableClassReceipt"
        ∷ "It does not construct accepted HEPData-to-ITIR authority route"
        ∷ "It does not construct a DASHI projection law or comparison-law theorem"
        ∷ "It does not reconcile raw upstream values with the normalized artifact by typed adapter semantics"
        ∷ "It does not promote W3, W4, W5, or W8"
        ∷ []
    }
