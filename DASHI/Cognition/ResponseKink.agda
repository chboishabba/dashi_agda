{-# OPTIONS --safe #-}
module DASHI.Cognition.ResponseKink where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Facilitation before suppression
--
-- This is the qualitative theorem surface required by the observed
-- "small upward kink before the fall".  It does not claim that GELU itself is
-- non-monotone.  A continuous GELU-times-envelope or rationally attenuated
-- gate may instantiate the same shape contract in an analytic lane.

record RecruitmentSuppressionProfile (Input : Set) : Set₁ where
  field
    lowInput : Input
    prePeakInput : Input
    peakInput : Input
    overloadInput : Input
    response : Input → Nat

    low-to-prePeak-rise :
      response lowInput < response prePeakInput

    prePeak-to-peak-rise :
      response prePeakInput < response peakInput

    overload-below-peak :
      response overloadInput < response peakInput

open RecruitmentSuppressionProfile public

profile-shape :
  {Input : Set}
  (profile : RecruitmentSuppressionProfile Input) →
  (response profile (lowInput profile) <
   response profile (prePeakInput profile))
  ×
  ((response profile (prePeakInput profile) <
    response profile (peakInput profile))
  ×
   (response profile (overloadInput profile) <
    response profile (peakInput profile)))
profile-shape profile =
  low-to-prePeak-rise profile ,
  (prePeak-to-peak-rise profile ,
   overload-below-peak profile)

------------------------------------------------------------------------
-- Concrete four-stage witness:
--
-- insufficient evidence -> recruitment -> selected coherence -> overload
--
-- Scores 0, 1, 2, 1 make both the facilitation and the subsequent
-- suppression definitionally inspectable.

data DriveStage : Set where
  insufficient recruited selected overloaded : DriveStage

sampledResponse : DriveStage → Nat
sampledResponse insufficient = 0
sampledResponse recruited = 1
sampledResponse selected = 2
sampledResponse overloaded = 1

insufficient-to-recruited :
  sampledResponse insufficient < sampledResponse recruited
insufficient-to-recruited =
  n<1+n 0

recruited-to-selected :
  sampledResponse recruited < sampledResponse selected
recruited-to-selected =
  n<1+n 1

overloaded-below-selected :
  sampledResponse overloaded < sampledResponse selected
overloaded-below-selected =
  n<1+n 1

sampledKinkProfile :
  RecruitmentSuppressionProfile DriveStage
sampledKinkProfile =
  record
    { lowInput = insufficient
    ; prePeakInput = recruited
    ; peakInput = selected
    ; overloadInput = overloaded
    ; response = sampledResponse
    ; low-to-prePeak-rise = insufficient-to-recruited
    ; prePeak-to-peak-rise = recruited-to-selected
    ; overload-below-peak = overloaded-below-selected
    }

record ResponseKinkReceipt : Set where
  constructor response-kink-receipt
  field
    facilitationBeforeSuppressionChecked : Bool
    nonmonotoneGateSurfaceRequired : Bool
    geluAloneAssertedSufficient : Bool
    geluAloneAssertedSufficientIsFalse :
      geluAloneAssertedSufficient ≡ false

responseKinkReceipt : ResponseKinkReceipt
responseKinkReceipt =
  response-kink-receipt true true false refl
