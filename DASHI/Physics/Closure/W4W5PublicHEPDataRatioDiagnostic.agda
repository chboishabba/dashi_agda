module DASHI.Physics.Closure.W4W5PublicHEPDataRatioDiagnostic where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- W4/W5 public HEPData ratio-table diagnostic.
--
-- The local public HEPData CSVs do not expose a mass-window dσ/dM table for
-- the proposed W4/W5 shortcut.  They expose:
--
-- * t21: absolute DSIG/DPHISTAR for the 76-106 GeV Z window;
-- * t43: DSIG/DPHISTAR(50-76) / DSIG/DPHISTAR(76-106);
-- * t45: DSIG/DPHISTAR(106-170) / DSIG/DPHISTAR(76-106).
--
-- This receipt binds the supported public-table computation and keeps it
-- separate from the older W5 PDF-carrier target 0.8804486068.

data W4W5PublicHEPDataRatioStatus : Set where
  publicRatioTableDiagnosticOnly :
    W4W5PublicHEPDataRatioStatus

data W4W5PublicHEPDataRatioFirstMissing : Set where
  missingLawFromPublicRatioTablesToW4W5CorrectionSurface :
    W4W5PublicHEPDataRatioFirstMissing

data W4W5PublicHEPDataTableKind : Set where
  absoluteDSIGDPHISTAR :
    W4W5PublicHEPDataTableKind
  ratioDSIGDPHISTAROverDSIGDPHISTAR :
    W4W5PublicHEPDataTableKind

record W4W5PublicHEPDataRatioDiagnostic : Set where
  field
    status :
      W4W5PublicHEPDataRatioStatus

    firstMissing :
      W4W5PublicHEPDataRatioFirstMissing

    runnerPath :
      String

    artifactPath :
      String

    zDenominatorTable :
      String

    belowZRatioTable :
      String

    aboveZRatioTable :
      String

    zDenominatorKind :
      W4W5PublicHEPDataTableKind

    belowZRatioKind :
      W4W5PublicHEPDataTableKind

    aboveZRatioKind :
      W4W5PublicHEPDataTableKind

    t43OverZPublicRatio :
      Float

    t45OverZPublicRatio :
      Float

    t45OverT43PublicRatio :
      Float

    previousW5PDFCarrierTarget :
      Float

    previousW5PDFCarrierTargetDecimal :
      String

    targetComputableFromTheseColumns :
      Bool

    unsupportedTargetReasons :
      List String

    interpretation :
      List String

    nextAdmissibleAction :
      String

    promotesW4 :
      Bool

    promotesW5 :
      Bool

    noDσDMClaim :
      ⊤

    noAcceptedConventionClaim :
      ⊤

    noW4Promotion :
      ⊤

    noW5Promotion :
      ⊤

canonicalW4W5PublicHEPDataRatioDiagnostic :
  W4W5PublicHEPDataRatioDiagnostic
canonicalW4W5PublicHEPDataRatioDiagnostic =
  record
    { status =
        publicRatioTableDiagnosticOnly
    ; firstMissing =
        missingLawFromPublicRatioTablesToW4W5CorrectionSurface
    ; runnerPath =
        "scripts/run_w4w5_hepdata_public_ratio_integral.py"
    ; artifactPath =
        "scripts/data/outputs/w4w5_hepdata_public_ratio_integral.json"
    ; zDenominatorTable =
        "10.17182/hepdata.115656.v1/t21"
    ; belowZRatioTable =
        "10.17182/hepdata.115656.v1/t43"
    ; aboveZRatioTable =
        "10.17182/hepdata.115656.v1/t45"
    ; zDenominatorKind =
        absoluteDSIGDPHISTAR
    ; belowZRatioKind =
        ratioDSIGDPHISTAROverDSIGDPHISTAR
    ; aboveZRatioKind =
        ratioDSIGDPHISTAROverDSIGDPHISTAR
    ; t43OverZPublicRatio =
        0.048798342138242475
    ; t45OverZPublicRatio =
        0.025440376842598356
    ; t45OverT43PublicRatio =
        0.5213369087525034
    ; previousW5PDFCarrierTarget =
        0.8804486068
    ; previousW5PDFCarrierTargetDecimal =
        "0.8804486068"
    ; targetComputableFromTheseColumns =
        false
    ; unsupportedTargetReasons =
        "none of t21/t43/t45 exposes a dsigma/dM column"
        ∷ "t43 and t45 expose Ratio columns for DSIG/DPHISTAR / DSIG/DPHISTAR"
        ∷ "0.5213369087525034 is the public ratio-table t45/t43 result, not the old 0.8804486068 PDF-carrier target"
        ∷ []
    ; interpretation =
        "t21 is an absolute DSIG/DPHISTAR Z-window denominator table"
        ∷ "t43 and t45 are already ratios over the Z-window denominator"
        ∷ "the supported public-table computation gives t43/Z = 0.048798342138242475"
        ∷ "the supported public-table computation gives t45/Z = 0.025440376842598356"
        ∷ "therefore t45/t43 = 0.5213369087525034 on the public ratio-table surface"
        ∷ "this does not reproduce or refute the old 0.8804486068 target unless a law identifies both surfaces"
        ∷ []
    ; nextAdmissibleAction =
        "either retarget W5 to the public HEPData ratio-table surface with an accepted law, or keep W5 on the PDF-carrier target and treat this diagnostic as a separate negative convention audit"
    ; promotesW4 =
        false
    ; promotesW5 =
        false
    ; noDσDMClaim =
        tt
    ; noAcceptedConventionClaim =
        tt
    ; noW4Promotion =
        tt
    ; noW5Promotion =
        tt
    }
