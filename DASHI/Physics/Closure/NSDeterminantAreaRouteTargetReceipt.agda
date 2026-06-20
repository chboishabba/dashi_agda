module DASHI.Physics.Closure.NSDeterminantAreaRouteTargetReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

------------------------------------------------------------------------
-- Corrected determinant-side H_area target receipt.
--
-- The old Qvel route is explicitly rejected for the current Omega_K target.
-- This receipt isolates the corrected route in four steps:
--   1. target a lower bound on integral det(S)+,
--   2. convert the determinant-side positivity into a lower bound on |Omega_K|
--      using the sign rule,
--   3. push that measure bound into the isoperimetric / area route for H_area,
--   4. keep type-I as a candidate scaling environment while leaving type-II
--      and the remaining quantitative closure inputs open.
--
-- Fail-closed: no theorem promotion and no Clay promotion are discharged here.

data NSDeterminantAreaRouteTargetStatus : Set where
  determinantAreaRouteTargetRecorded :
    NSDeterminantAreaRouteTargetStatus

data NSDeterminantAreaRouteTargetStage : Set where
  oldQvelRouteMarkedInvalid :
    NSDeterminantAreaRouteTargetStage
  determinantPositivePartTargetRecorded :
    NSDeterminantAreaRouteTargetStage
  signRuleBridgeToOmegaKRecorded :
    NSDeterminantAreaRouteTargetStage
  omegaKMeasureLowerBoundTargetRecorded :
    NSDeterminantAreaRouteTargetStage
  isoperimetricAreaRouteRecorded :
    NSDeterminantAreaRouteTargetStage
  typeICandidateScalingEnvironmentRecorded :
    NSDeterminantAreaRouteTargetStage
  typeIIOpenQuantitativeBlockersRecorded :
    NSDeterminantAreaRouteTargetStage
  failClosedReceiptRecorded :
    NSDeterminantAreaRouteTargetStage

canonicalNSDeterminantAreaRouteTargetStages :
  List NSDeterminantAreaRouteTargetStage
canonicalNSDeterminantAreaRouteTargetStages =
  oldQvelRouteMarkedInvalid
  ∷ determinantPositivePartTargetRecorded
  ∷ signRuleBridgeToOmegaKRecorded
  ∷ omegaKMeasureLowerBoundTargetRecorded
  ∷ isoperimetricAreaRouteRecorded
  ∷ typeICandidateScalingEnvironmentRecorded
  ∷ typeIIOpenQuantitativeBlockersRecorded
  ∷ failClosedReceiptRecorded
  ∷ []

data NSDeterminantAreaRouteTargetBlocker : Set where
  qvelRouteDoesNotControlOmegaK :
    NSDeterminantAreaRouteTargetBlocker
  determinantLowerBoundNotYetEstablished :
    NSDeterminantAreaRouteTargetBlocker
  signRuleConversionStillConditional :
    NSDeterminantAreaRouteTargetBlocker
  areaEstimateStillOpen :
    NSDeterminantAreaRouteTargetBlocker
  typeIIQuantitativeConstantsOpen :
    NSDeterminantAreaRouteTargetBlocker
  theoremPromotionGateKeptClosed :
    NSDeterminantAreaRouteTargetBlocker
  clayPromotionGateKeptClosed :
    NSDeterminantAreaRouteTargetBlocker

canonicalNSDeterminantAreaRouteTargetBlockers :
  List NSDeterminantAreaRouteTargetBlocker
canonicalNSDeterminantAreaRouteTargetBlockers =
  qvelRouteDoesNotControlOmegaK
  ∷ determinantLowerBoundNotYetEstablished
  ∷ signRuleConversionStillConditional
  ∷ areaEstimateStillOpen
  ∷ typeIIQuantitativeConstantsOpen
  ∷ theoremPromotionGateKeptClosed
  ∷ clayPromotionGateKeptClosed
  ∷ []

data NSDeterminantAreaRouteTargetPromotion : Set where

nsDeterminantAreaRouteTargetPromotionImpossibleHere :
  NSDeterminantAreaRouteTargetPromotion →
  ⊥
nsDeterminantAreaRouteTargetPromotionImpossibleHere ()

canonicalOldQvelRouteText : String
canonicalOldQvelRouteText =
  "The old Qvel route is invalid for the Omega_K target and is retained only as a rejected branch."

canonicalDeterminantPositivePartTargetText : String
canonicalDeterminantPositivePartTargetText =
  "Corrected target: obtain a lower bound on integral det(S)+ before any area conclusion is attempted."

canonicalSignRuleBridgeText : String
canonicalSignRuleBridgeText =
  "Sign-rule bridge: convert the determinant-side positivity into a lower bound on |Omega_K| using the recorded sign decomposition."

canonicalOmegaKMeasureTargetText : String
canonicalOmegaKMeasureTargetText =
  "Measure target: the |Omega_K| bound is the next intermediate target, not a finished H_area result."

canonicalAreaRouteText : String
canonicalAreaRouteText =
  "Area route: push the |Omega_K| bound into the isoperimetric / H_area estimate on the boundary side."

canonicalTypeICandidateScalingText : String
canonicalTypeICandidateScalingText =
  "Type-I is recorded as a candidate scaling environment for the determinant-side transfer."

canonicalTypeIIOpenBlockerText : String
canonicalTypeIIOpenBlockerText =
  "Type-II remains open: the needed quantitative constants, thresholds, and closure inputs are not fixed here."

canonicalFailClosedText : String
canonicalFailClosedText =
  "Fail-closed route ledger: the determinant-side path is recorded, but theorem promotion and Clay promotion stay false until the quantitative gap is closed."

canonicalReceiptBoundaryText : List String
canonicalReceiptBoundaryText =
  "Rejected Qvel branch recorded explicitly for the Omega_K target."
  ∷ "Determinant-side lower bound on integral det(S)+ is the corrected analytic entry point."
  ∷ "The sign rule is the bridge from determinant positivity to |Omega_K|."
  ∷ "The isoperimetric / H_area route is recorded as the next downstream step."
  ∷ "Type-I is a candidate scaling environment."
  ∷ "Type-II and the remaining quantitative closure inputs remain open."
  ∷ "No theorem promotion and no Clay promotion are discharged here."
  ∷ []

record NSDeterminantAreaRouteTargetORCSLPGF : Set where
  constructor mkNSDeterminantAreaRouteTargetORCSLPGF
  field
    O : String
    OIsCanonical : O ≡
      "O: Record the corrected determinant-side H_area target as a fail-closed receipt."

    R : String
    RIsCanonical : R ≡
      "R: Reject the old Qvel route, target a lower bound on integral det(S)+, and convert it through the sign rule to a lower bound on |Omega_K| before the area step."

    C : String
    CIsCanonical : C ≡
      "C: Keep the receipt self-contained: route stages, blocker ledger, canonical text, and promotion gates are recorded locally."

    S : String
    SIsCanonical : S ≡
      "S: oldQvelRouteMarkedInvalid=true; determinantPositivePartTargetRecorded=true; signRuleBridgeToOmegaKRecorded=true; omegaKMeasureLowerBoundTargetRecorded=true; isoperimetricAreaRouteRecorded=true; typeICandidateScalingEnvironmentRecorded=true; typeIIOpenQuantitativeBlockersRecorded=true; theoremPromotion=false; clayPromotion=false."

    L : String
    LIsCanonical : L ≡
      "L: Keep the determinant-side route local to this lane until the quantitative bridge to H_area is actually closed."

    P : String
    PIsCanonical : P ≡
      "P: No theorem is promoted from this receipt and no closure claim is emitted."

    G : String
    GIsCanonical : G ≡
      "G: No Clay promotion, no external authority shortcut, and no hidden quantitative assumption are accepted here."

    F : String
    FIsCanonical : F ≡
      "F: The route stays fail-closed because the lower bound, sign-rule transfer, and area estimate are recorded as targets, not as discharged theorems."

record NSDeterminantAreaRouteTargetReceipt : Setω where
  constructor mkNSDeterminantAreaRouteTargetReceipt
  field
    status :
      NSDeterminantAreaRouteTargetStatus

    statusIsCanonical :
      status ≡ determinantAreaRouteTargetRecorded

    stageTrail :
      List NSDeterminantAreaRouteTargetStage

    stageTrailIsCanonical :
      stageTrail ≡ canonicalNSDeterminantAreaRouteTargetStages

    stageCount :
      Nat

    stageCountIsCanonical :
      stageCount ≡ listLength canonicalNSDeterminantAreaRouteTargetStages

    blockerTrail :
      List NSDeterminantAreaRouteTargetBlocker

    blockerTrailIsCanonical :
      blockerTrail ≡ canonicalNSDeterminantAreaRouteTargetBlockers

    blockerCount :
      Nat

    blockerCountIsCanonical :
      blockerCount ≡ listLength canonicalNSDeterminantAreaRouteTargetBlockers

    oldQvelRouteText :
      String

    oldQvelRouteTextIsCanonical :
      oldQvelRouteText ≡ canonicalOldQvelRouteText

    determinantPositivePartTargetText :
      String

    determinantPositivePartTargetTextIsCanonical :
      determinantPositivePartTargetText ≡ canonicalDeterminantPositivePartTargetText

    signRuleBridgeText :
      String

    signRuleBridgeTextIsCanonical :
      signRuleBridgeText ≡ canonicalSignRuleBridgeText

    omegaKMeasureTargetText :
      String

    omegaKMeasureTargetTextIsCanonical :
      omegaKMeasureTargetText ≡ canonicalOmegaKMeasureTargetText

    areaRouteText :
      String

    areaRouteTextIsCanonical :
      areaRouteText ≡ canonicalAreaRouteText

    typeICandidateScalingText :
      String

    typeICandidateScalingTextIsCanonical :
      typeICandidateScalingText ≡ canonicalTypeICandidateScalingText

    typeIIOpenBlockerText :
      String

    typeIIOpenBlockerTextIsCanonical :
      typeIIOpenBlockerText ≡ canonicalTypeIIOpenBlockerText

    receiptBoundaryText :
      List String

    receiptBoundaryTextIsCanonical :
      receiptBoundaryText ≡ canonicalReceiptBoundaryText

    determinantRouteFailClosed :
      Bool

    determinantRouteFailClosedIsTrue :
      determinantRouteFailClosed ≡ true

    theoremPromotion :
      Bool

    theoremPromotionIsFalse :
      theoremPromotion ≡ false

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

    orcslpgf :
      NSDeterminantAreaRouteTargetORCSLPGF

open NSDeterminantAreaRouteTargetReceipt public

canonicalNSDeterminantAreaRouteTargetORCSLPGF :
  NSDeterminantAreaRouteTargetORCSLPGF
canonicalNSDeterminantAreaRouteTargetORCSLPGF =
  mkNSDeterminantAreaRouteTargetORCSLPGF
    "O: Record the corrected determinant-side H_area target as a fail-closed receipt."
    refl
    "R: Reject the old Qvel route, target a lower bound on integral det(S)+, and convert it through the sign rule to a lower bound on |Omega_K| before the area step."
    refl
    "C: Keep the receipt self-contained: route stages, blocker ledger, canonical text, and promotion gates are recorded locally."
    refl
    "S: oldQvelRouteMarkedInvalid=true; determinantPositivePartTargetRecorded=true; signRuleBridgeToOmegaKRecorded=true; omegaKMeasureLowerBoundTargetRecorded=true; isoperimetricAreaRouteRecorded=true; typeICandidateScalingEnvironmentRecorded=true; typeIIOpenQuantitativeBlockersRecorded=true; theoremPromotion=false; clayPromotion=false."
    refl
    "L: Keep the determinant-side route local to this lane until the quantitative bridge to H_area is actually closed."
    refl
    "P: No theorem is promoted from this receipt and no closure claim is emitted."
    refl
    "G: No Clay promotion, no external authority shortcut, and no hidden quantitative assumption are accepted here."
    refl
    "F: The route stays fail-closed because the lower bound, sign-rule transfer, and area estimate are recorded as targets, not as discharged theorems."
    refl

canonicalNSDeterminantAreaRouteTargetReceipt :
  NSDeterminantAreaRouteTargetReceipt
canonicalNSDeterminantAreaRouteTargetReceipt =
  record
    { status =
        determinantAreaRouteTargetRecorded
    ; statusIsCanonical =
        refl
    ; stageTrail =
        canonicalNSDeterminantAreaRouteTargetStages
    ; stageTrailIsCanonical =
        refl
    ; stageCount =
        listLength canonicalNSDeterminantAreaRouteTargetStages
    ; stageCountIsCanonical =
        refl
    ; blockerTrail =
        canonicalNSDeterminantAreaRouteTargetBlockers
    ; blockerTrailIsCanonical =
        refl
    ; blockerCount =
        listLength canonicalNSDeterminantAreaRouteTargetBlockers
    ; blockerCountIsCanonical =
        refl
    ; oldQvelRouteText =
        canonicalOldQvelRouteText
    ; oldQvelRouteTextIsCanonical =
        refl
    ; determinantPositivePartTargetText =
        canonicalDeterminantPositivePartTargetText
    ; determinantPositivePartTargetTextIsCanonical =
        refl
    ; signRuleBridgeText =
        canonicalSignRuleBridgeText
    ; signRuleBridgeTextIsCanonical =
        refl
    ; omegaKMeasureTargetText =
        canonicalOmegaKMeasureTargetText
    ; omegaKMeasureTargetTextIsCanonical =
        refl
    ; areaRouteText =
        canonicalAreaRouteText
    ; areaRouteTextIsCanonical =
        refl
    ; typeICandidateScalingText =
        canonicalTypeICandidateScalingText
    ; typeICandidateScalingTextIsCanonical =
        refl
    ; typeIIOpenBlockerText =
        canonicalTypeIIOpenBlockerText
    ; typeIIOpenBlockerTextIsCanonical =
        refl
    ; receiptBoundaryText =
        canonicalReceiptBoundaryText
    ; receiptBoundaryTextIsCanonical =
        refl
    ; determinantRouteFailClosed =
        true
    ; determinantRouteFailClosedIsTrue =
        refl
    ; theoremPromotion =
        false
    ; theoremPromotionIsFalse =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; orcslpgf =
        canonicalNSDeterminantAreaRouteTargetORCSLPGF
    }
