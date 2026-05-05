module DASHI.Physics.Closure.W4W5PDFSharedDependencyDiagnostic where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.W4ZPeakCalibrationAnchorReceipt as W4ZPeak
import DASHI.Physics.Closure.W5CT18ExternalIntakeReceipt as W5CT18
import DASHI.Physics.Closure.W5PDFCarrierExternalConfirmedGap as W5Gap

------------------------------------------------------------------------
-- W4/W5 shared external PDF dependency diagnostic.
--
-- This is a non-promoting Maxwell-Faraday lane receipt.  It records that the
-- current W4 dirty Z-peak shape adequacy blocker and the current W5 t45
-- correction blocker have the same upstream missing ingredient: an accepted
-- CT18/MSHT/LHAPDF-compatible parton-luminosity/PDF intake packet.
--
-- The receipt does not claim W4 closes, does not claim a successful Z-peak
-- anchor, does not construct an external PDF carrier, and does not promote W5.

data W4W5PDFSharedDependencyStatus : Set where
  w4ShapeAndW5T45ShareExternalPDFDependency :
    W4W5PDFSharedDependencyStatus

data W4W5PDFSharedFirstMissing : Set where
  missingSharedCT18MSHTLHAPDFPartonLuminosityIntake :
    W4W5PDFSharedFirstMissing

record W4W5PDFSharedDependencyDiagnostic : Setω where
  field
    status :
      W4W5PDFSharedDependencyStatus

    w4ZPeakAnchorDiagnostic :
      W4ZPeak.W4ZPeakCalibrationAnchorMissingArtifactDiagnostic

    w5CT18IntakeReceipt :
      W5CT18.W5CT18ExternalIntakeReceipt

    w5ConfirmedExternalGap :
      W5Gap.W5PDFCarrierExternalConfirmedGap

    firstMissing :
      W4W5PDFSharedFirstMissing

    w4FirstMissingLabel :
      String

    w5FirstMissingLabel :
      String

    sharedMissingLabel :
      String

    w4CurrentShapeFitChi2PerDof :
      String

    w4CurrentShapeFitDigest :
      String

    w5RequiredT45Correction :
      Float

    w5RequiredT45CorrectionDecimal :
      String

    acceptedProviderFamilies :
      List String

    sharedProviderPayload :
      List String

    dependencyRationale :
      List String

    nextAdmissibleAction :
      String

    noW4AnchorClosure :
      ⊤

    noW4Promotion :
      ⊤

    noW5T45Promotion :
      ⊤

    noExternalPDFCarrierConstructed :
      ⊤

canonicalW4W5PDFSharedDependencyDiagnostic :
  W4W5PDFSharedDependencyDiagnostic
canonicalW4W5PDFSharedDependencyDiagnostic =
  record
    { status =
        w4ShapeAndW5T45ShareExternalPDFDependency
    ; w4ZPeakAnchorDiagnostic =
        W4ZPeak.canonicalW4ZPeakCalibrationAnchorMissingArtifactDiagnostic
    ; w5CT18IntakeReceipt =
        W5CT18.canonicalW5CT18ExternalIntakeReceipt
    ; w5ConfirmedExternalGap =
        W5Gap.canonicalW5PDFCarrierExternalConfirmedGap
    ; firstMissing =
        missingSharedCT18MSHTLHAPDFPartonLuminosityIntake
    ; w4FirstMissingLabel =
        "W4 first missing remains missingDirtyZPeakShapeAdequacy; current local shape fit chi2/dof is 298.8462841768543"
    ; w5FirstMissingLabel =
        "W5 first missing remains CT18/MSHT/LHAPDF packet fields and computed t45 correction"
    ; sharedMissingLabel =
        "missing shared CT18/MSHT/LHAPDF-compatible parton-luminosity intake"
    ; w4CurrentShapeFitChi2PerDof =
        "298.8462841768543"
    ; w4CurrentShapeFitDigest =
        "36191efc92cb3c9b1641c9206171a307c4796369a4acd1485bf87d1051662b8b"
    ; w5RequiredT45Correction =
        0.8804486068
    ; w5RequiredT45CorrectionDecimal =
        "0.8804486068"
    ; acceptedProviderFamilies =
        "CT18"
        ∷ "MSHT"
        ∷ "NNPDF"
        ∷ "LHAPDF-compatible equivalent"
        ∷ []
    ; sharedProviderPayload =
        "PDF set identifier and version"
        ∷ "LHAPDF grid/checksum or equivalent provider table checksum"
        ∷ "parton-luminosity route for CMS-SMP-20-003 Z-peak and t45 windows"
        ∷ "x and Q2 convention for the 76-106, 106-170, and denominator 76-106 mass windows"
        ∷ "flavour/channel convention for the Drell-Yan q qbar luminosity ratio"
        ∷ "computed W5 t45 correction targeting 0.8804486068"
        ∷ "W4 Z-peak shape adequacy statement under the same PDF/parton-luminosity conventions"
        ∷ "authority/provenance receipt for the external PDF table or equivalent mass-kernel route"
        ∷ []
    ; dependencyRationale =
        "The W4 dirty Z-peak data and covariance are local and parsed, but the current carrier-only shape fit is inadequate"
        ∷ "The W5 t45 route already records that local DGLAP/carrier diagnostics do not provide an accepted PDF carrier"
        ∷ "Both blockers require an accepted parton-luminosity/PDF intake before their downstream comparison surfaces can be evaluated"
        ∷ "This receipt merges the provider-facing dependency; it does not merge W4 and W5 promotions"
        ∷ []
    ; nextAdmissibleAction =
        "supply a CT18/MSHT/LHAPDF-compatible packet satisfying the shared provider payload, then rerun W4 Z-peak shape adequacy and W5 t45 correction checks"
    ; noW4AnchorClosure =
        tt
    ; noW4Promotion =
        tt
    ; noW5T45Promotion =
        tt
    ; noExternalPDFCarrierConstructed =
        tt
    }

canonicalW4W5SharedFirstMissing :
  W4W5PDFSharedDependencyDiagnostic.firstMissing
    canonicalW4W5PDFSharedDependencyDiagnostic
    ≡
  missingSharedCT18MSHTLHAPDFPartonLuminosityIntake
canonicalW4W5SharedFirstMissing =
  refl

canonicalW4W5SharedDependencyDoesNotCloseW4 :
  W4W5PDFSharedDependencyDiagnostic.noW4Promotion
    canonicalW4W5PDFSharedDependencyDiagnostic
    ≡ tt
canonicalW4W5SharedDependencyDoesNotCloseW4 =
  refl

canonicalW4W5SharedDependencyDoesNotPromoteW5 :
  W4W5PDFSharedDependencyDiagnostic.noW5T45Promotion
    canonicalW4W5PDFSharedDependencyDiagnostic
    ≡ tt
canonicalW4W5SharedDependencyDoesNotPromoteW5 =
  refl
