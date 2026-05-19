module DASHI.Physics.Closure.W5ObservableClarificationNote where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- W5 observable clarification note.
--
-- This is a non-promoting receipt.  It records that the older W5 carrier
-- target and the current CT18/public CMS-SMP-20-003 diagnostics are different
-- observables.  W5 is therefore characterized and parked pending the accepted
-- W4 bridge/convention correction, not closed by a local proof.

data W5CarrierObservable : Set where
  carrierMassPDFCorrectionRatio :
    W5CarrierObservable

data W5CT18Observable : Set where
  ct18InclusiveDYLuminosityRatio :
    W5CT18Observable
  cmsPublicPhiStarRatioTableIntegral :
    W5CT18Observable
  cmsPublicPTAbsoluteTableIntegral :
    W5CT18Observable

data W5ObservableRelation : Set where
  differentObservablesNoDirectSubstitution :
    W5ObservableRelation

data W5ObservableGap : Set where
  missingAcceptedPhiStarToMassOrDYLuminosityBridge :
    W5ObservableGap

data W5SubtaskStatus : Set where
  w5aParkedPendingW4AcceptanceCorrection :
    W5SubtaskStatus
  w5bParkedPendingAcceptedDYLuminosityConvention :
    W5SubtaskStatus

data W5FormalParkedStatus : Set where
  characterizedParkedNonPromoting :
    W5FormalParkedStatus

record W5ObservableClarificationNote : Set where
  field
    carrierObservable :
      W5CarrierObservable

    carrierObservableName :
      String

    carrierObservableTarget :
      String

    ct18Observable :
      W5CT18Observable

    ct18ObservableName :
      String

    ct18ObservableCandidateValues :
      List String

    observableRelation :
      W5ObservableRelation

    gap :
      W5ObservableGap

    gapExplanation :
      List String

    w5aStatus :
      W5SubtaskStatus

    w5bStatus :
      W5SubtaskStatus

    formalParkedStatus :
      W5FormalParkedStatus

    currentTypedSurfaces :
      List String

    exactRemainingBlocker :
      String

    promotesW5 :
      Bool

    isProofClosure :
      Bool

    noCarrierToCT18Substitution :
      ⊤

    noW5Promotion :
      ⊤

    noProofClosureClaim :
      ⊤

canonicalW5ObservableClarificationNote :
  W5ObservableClarificationNote
canonicalW5ObservableClarificationNote =
  record
    { carrierObservable =
        carrierMassPDFCorrectionRatio
    ; carrierObservableName =
        "older W5 carrier mass-integrated cross-section/PDF correction ratio"
    ; carrierObservableTarget =
        "0.8804486068"
    ; ct18Observable =
        ct18InclusiveDYLuminosityRatio
    ; ct18ObservableName =
        "CT18/public CMS diagnostic inclusive or table-integral observable"
    ; ct18ObservableCandidateValues =
        "CT18 fixed-x candidate probe = 1.0506681065158017"
        ∷ "CT18 rapidity-window t45/z_peak candidate probe = 0.7514043986785174"
        ∷ "CT18 rapidity-window t45/t43 denominator hypothesis = 0.3348750784006896"
        ∷ "CMS public phi-star t45/t43 ratio-table integral = 0.5213369087525034"
        ∷ "CMS public pT at-least-one-jet 106-170 / 50-76 integral = 0.7588411892066674"
        ∷ []
    ; observableRelation =
        differentObservablesNoDirectSubstitution
    ; gap =
        missingAcceptedPhiStarToMassOrDYLuminosityBridge
    ; gapExplanation =
        "The carrier target is a mass-integrated correction/PDF-ratio surface."
        ∷ "The CT18 and public CMS diagnostics are luminosity or published table-integral surfaces."
        ∷ "No accepted bridge currently identifies those observables or permits substituting one value for the other."
        ∷ "The local diagnostics characterize the mismatch; they do not close W5."
        ∷ []
    ; w5aStatus =
        w5aParkedPendingW4AcceptanceCorrection
    ; w5bStatus =
        w5bParkedPendingAcceptedDYLuminosityConvention
    ; formalParkedStatus =
        characterizedParkedNonPromoting
    ; currentTypedSurfaces =
        "DASHI.Physics.Closure.W4W5PhiStarToMassAcceptanceBridgeRequest"
        ∷ "DASHI.Physics.Closure.W4W5AcceptedDYLuminosityConventionDiagnostic"
        ∷ "DASHI.Physics.Closure.W5T45CorrectionReceipt"
        ∷ "Docs/W4W5AcceptanceBridgeProviderRequest.md"
        ∷ []
    ; exactRemainingBlocker =
        "accepted W4 phi-star-to-mass acceptance/conversion bridge or accepted DY luminosity convention binding the CT18/public-CMS diagnostic observable to the older W5 carrier ratio"
    ; promotesW5 =
        false
    ; isProofClosure =
        false
    ; noCarrierToCT18Substitution =
        tt
    ; noW5Promotion =
        tt
    ; noProofClosureClaim =
        tt
    }

canonicalW5ObservableClarificationParked :
  W5ObservableClarificationNote.formalParkedStatus
    canonicalW5ObservableClarificationNote
    ≡
  characterizedParkedNonPromoting
canonicalW5ObservableClarificationParked = refl

canonicalW5ObservableClarificationNoPromotion :
  W5ObservableClarificationNote.promotesW5
    canonicalW5ObservableClarificationNote
    ≡
  false
canonicalW5ObservableClarificationNoPromotion = refl

canonicalW5ObservableClarificationNotProofClosure :
  W5ObservableClarificationNote.isProofClosure
    canonicalW5ObservableClarificationNote
    ≡
  false
canonicalW5ObservableClarificationNotProofClosure = refl
