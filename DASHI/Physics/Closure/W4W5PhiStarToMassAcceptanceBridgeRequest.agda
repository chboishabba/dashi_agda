module DASHI.Physics.Closure.W4W5PhiStarToMassAcceptanceBridgeRequest where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- W4/W5 phi-star-to-mass acceptance bridge request.
--
-- The local HEPData cache and the public CMS-SMP-20-003 HEPData YAML expose
-- measured DSIG/DPHISTAR tables, DSIG/DPHISTAR ratio tables, covariance
-- matrices, uncertainty components, and detector response matrices.  They do
-- not expose an acceptance/efficiency surface A(M, phi*) or an accepted law
-- that converts the public phi-star ratio-table integrals into the older W5
-- mass-integrated cross-section/PDF correction surface.

data PhiStarToMassAcceptanceBridgeStatus : Set where
  blockedMissingAcceptanceBridgeArtifact :
    PhiStarToMassAcceptanceBridgeStatus

data PhiStarToMassPublicArtifactKind : Set where
  absoluteDSIGDPHISTARTable :
    PhiStarToMassPublicArtifactKind
  ratioDSIGDPHISTARTable :
    PhiStarToMassPublicArtifactKind
  covarianceMatrix :
    PhiStarToMassPublicArtifactKind
  uncertaintyComponentColumns :
    PhiStarToMassPublicArtifactKind
  detectorResponseMatrix :
    PhiStarToMassPublicArtifactKind
  metadataAndSubmissionIndex :
    PhiStarToMassPublicArtifactKind

data PhiStarToMassNeededArtifactField : Set where
  acceptanceEfficiencySurfaceAMassPhi :
    PhiStarToMassNeededArtifactField
  massIntegratedCrossSectionSurface :
    PhiStarToMassNeededArtifactField
  phiStarToMassObservableConversionLaw :
    PhiStarToMassNeededArtifactField
  pdfCorrectionSurfaceConvention :
    PhiStarToMassNeededArtifactField
  normalizationPreservationLaw :
    PhiStarToMassNeededArtifactField
  jetRequirementAndLeptonChannelBinding :
    PhiStarToMassNeededArtifactField
  systematicAndCovariancePropagationLaw :
    PhiStarToMassNeededArtifactField
  provenanceChecksumAndCitation :
    PhiStarToMassNeededArtifactField

canonicalPhiStarToMassNeededArtifactFields :
  List PhiStarToMassNeededArtifactField
canonicalPhiStarToMassNeededArtifactFields =
  acceptanceEfficiencySurfaceAMassPhi
  ∷ massIntegratedCrossSectionSurface
  ∷ phiStarToMassObservableConversionLaw
  ∷ pdfCorrectionSurfaceConvention
  ∷ normalizationPreservationLaw
  ∷ jetRequirementAndLeptonChannelBinding
  ∷ systematicAndCovariancePropagationLaw
  ∷ provenanceChecksumAndCitation
  ∷ []

record PhiStarToMassPublicArtifactAudit : Set where
  field
    artifactKind :
      PhiStarToMassPublicArtifactKind

    name :
      String

    source :
      String

    sufficientForBridge :
      Bool

    insufficiencyReason :
      String

record PhiStarToMassAcceptanceBridgeRequest : Set where
  field
    status :
      PhiStarToMassAcceptanceBridgeStatus

    localAuditScript :
      String

    localRatioDiagnostic :
      String

    localRatioDiagnosticArtifact :
      String

    publicRecord :
      String

    publicSubmissionYaml :
      String

    publicResponseMatrixExample :
      String

    checkedPublicLinks :
      List String

    publicArtifactsAudited :
      List PhiStarToMassPublicArtifactAudit

    t43OverZPublicPhiStarRatio :
      Float

    t45OverZPublicPhiStarRatio :
      Float

    t45OverT43PublicPhiStarRatio :
      Float

    previousW5MassPDFCorrectionTarget :
      Float

    previousW5MassPDFCorrectionTargetDecimal :
      String

    bridgeComputableFromPublicArtifacts :
      Bool

    neededExternalArtifactName :
      String

    exactMissingPublicField :
      String

    neededExternalArtifactFields :
      List PhiStarToMassNeededArtifactField

    exactProviderRequest :
      List String

    urlFailures :
      List String

    promotesW4 :
      Bool

    promotesW5 :
      Bool

    noPhiStarRatioPromotion :
      ⊤

    noFabricatedAcceptance :
      ⊤

    noMassPDFCorrectionClaim :
      ⊤

    noW4Promotion :
      ⊤

    noW5Promotion :
      ⊤

canonicalPublicArtifactAudit :
  List PhiStarToMassPublicArtifactAudit
canonicalPublicArtifactAudit =
  record
    { artifactKind =
        metadataAndSubmissionIndex
    ; name =
        "CMS-SMP-20-003 public CMS page, HEPData record metadata, and CMS submission.yaml"
    ; source =
        "https://cms-results.web.cern.ch/cms-results/public-results/publications/SMP-20-003/ ; https://www.hepdata.net/record/ins2079374?format=json ; https://cms-results.web.cern.ch/cms-results/public-results/publications/SMP-20-003/SMP-20-003_hepdata/submission.yaml"
    ; sufficientForBridge =
        false
    ; insufficiencyReason =
        "the indexes enumerate measured phistar cross-section, ratio, covariance, and response-matrix tables; no public field is named or typed as A(M, phi*) or as a phi-star-to-mass conversion law"
    }
  ∷
  record
    { artifactKind =
        absoluteDSIGDPHISTARTable
    ; name =
        "t19/t21 absolute phistar mass-window tables"
    ; source =
        "local scripts/data/hepdata and public submission.yaml entries phistar_mass_50-76.yaml, phistar_mass_76-106.yaml, phistar_mass_106-170.yaml"
    ; sufficientForBridge =
        false
    ; insufficiencyReason =
        "absolute DSIG/DPHISTAR values are already unfolded measurement bins, not A(M, phi*) or a mass/PDF correction law"
    }
  ∷ record
    { artifactKind =
        ratioDSIGDPHISTARTable
    ; name =
        "t43/t45 phistar ratio tables"
    ; source =
        "10.17182/hepdata.115656.v1/t43 and 10.17182/hepdata.115656.v1/t45"
    ; sufficientForBridge =
        false
    ; insufficiencyReason =
        "the tables expose DSIG/DPHISTAR / DSIG/DPHISTAR ratios over the Z window, not mass-integrated cross-section or PDF correction ratios"
    }
  ∷ record
    { artifactKind =
        covarianceMatrix
    ; name =
        "t20/t22/t44/t46 covariance matrices"
    ; source =
        "local scripts/data/hepdata covariance CSVs and public covariance YAML entries"
    ; sufficientForBridge =
        false
    ; insufficiencyReason =
        "covariance propagates uncertainty for the existing phi-star observables but does not define an observable conversion"
    }
  ∷ record
    { artifactKind =
        uncertaintyComponentColumns
    ; name =
        "Efficiency, unfolding, luminosity, lepton, background, jet, and other uncertainty columns"
    ; source =
        "local t19/t21/t43/t45 CSV headers"
    ; sufficientForBridge =
        false
    ; insufficiencyReason =
        "uncertainty components are errors on published values, not acceptance or efficiency central-value surfaces"
    }
  ∷ record
    { artifactKind =
        detectorResponseMatrix
    ; name =
        "public electron/muon response phistar mass-window matrices"
    ; source =
        "CMS-SMP-20-003 public HEPData YAML response matrix files"
    ; sufficientForBridge =
        false
    ; insufficiencyReason =
        "response matrices describe detector-bin migration for DSIG/DPHISTAR; they do not supply A(M, phi*) or a law mapping phi-star ratios to the W5 mass/PDF correction target"
    }
  ∷ []

canonicalW4W5PhiStarToMassAcceptanceBridgeRequest :
  PhiStarToMassAcceptanceBridgeRequest
canonicalW4W5PhiStarToMassAcceptanceBridgeRequest =
  record
    { status =
        blockedMissingAcceptanceBridgeArtifact
    ; localAuditScript =
        "scripts/run_w4w5_hepdata_public_ratio_integral.py"
    ; localRatioDiagnostic =
        "DASHI.Physics.Closure.W4W5PublicHEPDataRatioDiagnostic"
    ; localRatioDiagnosticArtifact =
        "scripts/data/outputs/w4w5_hepdata_public_ratio_integral.json"
    ; publicRecord =
        "https://cms-results.web.cern.ch/cms-results/public-results/publications/SMP-20-003/"
    ; publicSubmissionYaml =
        "https://cms-results.web.cern.ch/cms-results/public-results/publications/SMP-20-003/SMP-20-003_hepdata/submission.yaml"
    ; publicResponseMatrixExample =
        "https://cms-results.web.cern.ch/cms-results/public-results/publications/SMP-20-003/SMP-20-003_hepdata/electron_response_phistar_mass_50-76.yaml"
    ; checkedPublicLinks =
        "https://cms-results.web.cern.ch/cms-results/public-results/publications/SMP-20-003/ -- public result page; describes corrected differential cross sections and ratios, not A(M, phi*)"
        ∷ "https://cms-results.web.cern.ch/cms-results/public-results/publications/SMP-20-003/SMP-20-003_hepdata/submission.yaml -- HTTP 200; lists phistar measurement, covariance, and response-matrix YAML files"
        ∷ "https://www.hepdata.net/record/ins2079374?format=json -- HTTP 200; metadata lists t19/t21/t23, t43/t45, t20/t22/t44/t46, and t68-t73 response tables"
        ∷ "https://cms-results.web.cern.ch/cms-results/public-results/publications/SMP-20-003/SMP-20-003_hepdata/electron_response_phistar_mass_50-76.yaml -- HTTP 200; dependent variable P response matrix, not acceptance efficiency"
        ∷ "https://zenodo.org/record/4946277 -- additional resource is hepdata_lib packaging reference, not a CMS acceptance/efficiency artifact"
        ∷ []
    ; publicArtifactsAudited =
        canonicalPublicArtifactAudit
    ; t43OverZPublicPhiStarRatio =
        0.048798342138242475
    ; t45OverZPublicPhiStarRatio =
        0.025440376842598356
    ; t45OverT43PublicPhiStarRatio =
        0.5213369087525034
    ; previousW5MassPDFCorrectionTarget =
        0.8804486068
    ; previousW5MassPDFCorrectionTargetDecimal =
        "0.8804486068"
    ; bridgeComputableFromPublicArtifacts =
        false
    ; neededExternalArtifactName =
        "PhiStarToMassAcceptanceBridgeArtifact: A(M, phi*) or equivalent accepted law mapping CMS-SMP-20-003 DSIG/DPHISTAR ratio-table integrals to the W5 mass-integrated cross-section/PDF correction surface"
    ; exactMissingPublicField =
        "central-value acceptance/efficiency surface A(M, phi*) for mass windows 50-76, 76-106, and 106-170 GeV, or an accepted observable-conversion law from CMS-SMP-20-003 DSIG/DPHISTAR ratio-table integrals to mass-integrated cross-section/PDF correction ratios"
    ; neededExternalArtifactFields =
        canonicalPhiStarToMassNeededArtifactFields
    ; exactProviderRequest =
        "provide central-value acceptance/efficiency surface A(M, phi*) for the CMS-SMP-20-003 mass windows 50-76, 76-106, and 106-170 GeV, including the at-least-one-jet selection used by t43/t45"
        ∷ "provide an accepted observable conversion law from DSIG/DPHISTAR ratio-table integrals to mass-integrated cross-section/PDF correction ratios, or state that no such law is valid"
        ∷ "bind lepton-channel treatment, jet requirement, fiducial phase space, normalization convention, and bin-width convention"
        ∷ "provide covariance/systematic propagation for the conversion, including efficiency, unfolding model, luminosity, lepton energy, backgrounds, jet energy, and other components"
        ∷ "provide DOI/public URL/source citation, checksums or immutable package identity, provider role, and no-manual-overfit attestation"
        ∷ []
    ; urlFailures =
        "https://www.hepdata.net/record/ins2079374?format=json&table=Table%2043 redirected to https://www.hepdata.net/download/table/ins2079374/Table%2043/1/json and returned HTTP 403 / Cloudflare challenge in CLI; use browser/manual download only if canonical table JSON payload is needed"
        ∷ []
    ; promotesW4 =
        false
    ; promotesW5 =
        false
    ; noPhiStarRatioPromotion =
        tt
    ; noFabricatedAcceptance =
        tt
    ; noMassPDFCorrectionClaim =
        tt
    ; noW4Promotion =
        tt
    ; noW5Promotion =
        tt
    }
