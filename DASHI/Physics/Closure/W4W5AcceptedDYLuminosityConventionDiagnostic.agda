module DASHI.Physics.Closure.W4W5AcceptedDYLuminosityConventionDiagnostic where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- W4/W5 accepted Drell-Yan luminosity convention diagnostic.
--
-- This is a provenance-ready negative diagnostic.  The local CT18NLO grid and
-- extractor now define a concrete Drell-Yan luminosity candidate, but this
-- module does not mark it as accepted and does not promote W4 or W5.  The
-- current first missing is the authority that accepts the luminosity
-- definition, bin integration, scale choice, flavour sum, PDF member/error
-- treatment, and tolerance as the convention for the W4/W5 comparison.

data W4W5DYLuminosityConventionStatus : Set where
  candidateLocalCT18NLOConventionNotAccepted :
    W4W5DYLuminosityConventionStatus

data W4W5DYLuminosityFirstMissing : Set where
  missingAcceptedDYLuminosityConventionAuthority :
    W4W5DYLuminosityFirstMissing

data W4W5DYLuminosityNumericStatus : Set where
  localCandidateDoesNotMatchW5Target :
    W4W5DYLuminosityNumericStatus

record W4W5AcceptedDYLuminosityConventionDiagnostic : Set where
  field
    conventionStatus :
      W4W5DYLuminosityConventionStatus

    firstMissing :
      W4W5DYLuminosityFirstMissing

    numericStatus :
      W4W5DYLuminosityNumericStatus

    packetPath :
      String

    extractorPath :
      String

    pdfSet :
      String

    pdfMember :
      String

    archiveDigest :
      String

    infoDigest :
      String

    gridDigest :
      String

    conventionFormula :
      String

    binIntegration :
      String

    scaleChoice :
      String

    flavourSum :
      List String

    provenanceFields :
      List String

    requiredAuthorityFields :
      List String

    w5Target :
      Float

    w5TargetDecimal :
      String

    matchingTargetRatio :
      String

    matchingTargetAbsGap :
      String

    rejectedProbeRatios :
      List String

    promotesW4 :
      Bool

    promotesW5 :
      Bool

    noAcceptedConventionClaimed :
      ⊤

    noW4Promotion :
      ⊤

    noW5Promotion :
      ⊤

canonicalW4W5AcceptedDYLuminosityConventionDiagnostic :
  W4W5AcceptedDYLuminosityConventionDiagnostic
canonicalW4W5AcceptedDYLuminosityConventionDiagnostic =
  record
    { conventionStatus =
        candidateLocalCT18NLOConventionNotAccepted
    ; firstMissing =
        missingAcceptedDYLuminosityConventionAuthority
    ; numericStatus =
        localCandidateDoesNotMatchW5Target
    ; packetPath =
        "scripts/data/pdf/ct18_dashi_pdf_packet.json"
    ; extractorPath =
        "scripts/extract_ct18_pdf_packet.py"
    ; pdfSet =
        "CT18NLO SetIndex 14400"
    ; pdfMember =
        "member 0 central value; CT18NLO has 59 members and hessian 90 percent error sets"
    ; archiveDigest =
        "c9127231e77e97cbec79cb5839203ab00f8db77237a061b61f9420f2b7b9c213"
    ; infoDigest =
        "be60232d8e6c49982c82f5fa990fd5b0fd1050719944f31602bf27cdb16548b0"
    ; gridDigest =
        "375db856d2f8c7087a626c92ebf228d3f080e5de83175519778ffaf6e72e5410"
    ; conventionFormula =
        "integral dlog(x1) sum_q e_q^2 [q(x1,Q) qbar(tau/x1,Q) + qbar(x1,Q) q(tau/x1,Q)] with tau = M^2/s"
    ; binIntegration =
        "trapezoid in log(x1) with n_x = 200, then trapezoid in mass with n_m = 80 over each CMS-SMP-20-003 mass window"
    ; scaleChoice =
        "Q = dilepton mass for each center/window integration point; sqrt_s = 13000 GeV; eta_cut = 2.4"
    ; flavourSum =
        "u with charge weight 4/9"
        ∷ "d with charge weight 1/9"
        ∷ "s with charge weight 1/9"
        ∷ "q qbar plus qbar q symmetrisation"
        ∷ "LHAPDF lhagrid1 x*f(x,Q) divided by x before luminosity formation"
        ∷ []
    ; provenanceFields =
        "CT18NLO info Reference: arXiv:1908.11394 (temporary)"
        ∷ "CT18NLO Authors: T.-J. Hou, K. Xie, J. Gao, S. Dulat, M. Guzzi, T. J. Hobbs, J. Huston, P. Nadolsky, J. Pumplin, C. Schmidt, I. Sitiwaldi, D. Stump, C.-P. Yuan"
        ∷ "Format lhagrid1; OrderQCD 1; AlphaS_MZ 0.118000; AlphaS_OrderQCD 1"
        ∷ "archive, info, and central grid SHA-256 digests are recorded in the packet"
        ∷ []
    ; requiredAuthorityFields =
        "citation or provider receipt accepting the Drell-Yan luminosity definition"
        ∷ "mass-bin integration prescription for CMS-SMP-20-003 phi-star windows"
        ∷ "scale choice authority for Q = M or an accepted alternative Q2 convention"
        ∷ "flavour/channel sum authority including charge weights and heavy-flavour treatment"
        ∷ "PDF member and uncertainty prescription over CT18NLO members"
        ∷ "numeric tolerance and covariance treatment for W4 shape and W5 t45 correction"
        ∷ []
    ; w5Target =
        0.8804486068
    ; w5TargetDecimal =
        "0.8804486068"
    ; matchingTargetRatio =
        "0.7514043986785174"
    ; matchingTargetAbsGap =
        "0.12904420812148265"
    ; rejectedProbeRatios =
        "fixed-x u-quark xfxQ ratio = 1.0506681065158017; abs gap = 0.17021949971580164"
        ∷ "rapidity-window t45/z_peak ratio = 0.7514043986785174; abs gap = 0.12904420812148265"
        ∷ "rapidity-window t45/t43 ratio = 0.3348750784006896; abs gap = 0.5455735283993104"
        ∷ []
    ; promotesW4 =
        false
    ; promotesW5 =
        false
    ; noAcceptedConventionClaimed =
        tt
    ; noW4Promotion =
        tt
    ; noW5Promotion =
        tt
    }

canonicalW4W5DYLuminosityFirstMissing :
  W4W5AcceptedDYLuminosityConventionDiagnostic.firstMissing
    canonicalW4W5AcceptedDYLuminosityConventionDiagnostic
    ≡
  missingAcceptedDYLuminosityConventionAuthority
canonicalW4W5DYLuminosityFirstMissing =
  refl

canonicalW4W5DYLuminosityDoesNotPromoteW4 :
  W4W5AcceptedDYLuminosityConventionDiagnostic.promotesW4
    canonicalW4W5AcceptedDYLuminosityConventionDiagnostic
    ≡
  false
canonicalW4W5DYLuminosityDoesNotPromoteW4 =
  refl

canonicalW4W5DYLuminosityDoesNotPromoteW5 :
  W4W5AcceptedDYLuminosityConventionDiagnostic.promotesW5
    canonicalW4W5AcceptedDYLuminosityConventionDiagnostic
    ≡
  false
canonicalW4W5DYLuminosityDoesNotPromoteW5 =
  refl
